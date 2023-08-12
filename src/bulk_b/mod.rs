// Copyright 2020-2023 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0"
//
// This is part of rust-bulk-allocator
//
//  rust-bulk-allocator is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  rust-bulk-allocator is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
//
//  You should have received a copy of the GNU Lesser General Public License
//  along with rust-bulk-allocator.  If not, see <http://www.gnu.org/licenses/>.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

mod large_cache;
mod small_cache;

use self::large_cache::LargeCache;
use self::small_cache::SmallCache;
use crate::MEMORY_CHUNK_SIZE;
use std::alloc::{GlobalAlloc, Layout};
use std::cell::{Cell, UnsafeCell};
use std::mem::{align_of, size_of};
use std::ptr::{null_mut, NonNull};

type Link<T> = Option<NonNull<T>>;
const ALIGN: usize = if 8 < align_of::<usize>() {
    align_of::<usize>()
} else {
    8
};

/// `BulkAlloc` is an implementation of [`GlobalAlloc`](`std::alloc::GlobalAlloc`)
/// holding memory cache.
/// This struct acquires bulk memories from the backend, and frees them on the
/// drop at once for the performance.
///
/// Each instance has 2 kinds of caches: some forward linked lists to store a specific sized
/// pointers, and one red black tree to store arbitrary sized memory block.
///
/// The balanced tree cache merges 2 holding pointers if they are placed next to each other.
/// `BulkAlloc` stores a pointer into the tree cache if the size is large enough
/// or if the pointer can be merged into another;
/// otherwise, it is stored into the linked list cache for the size.
///
/// # Safety
///
/// Instance drop releases all the memories acquired from the backend.
/// All the pointers allocated via the instance will be invalid after then.
/// Accessing such a pointer may lead to memory unsafety even if the pointer itself is not
/// deallocated.
///
/// # See also
///
/// - [`alloc`]
/// - [`dealloc`]
///
/// [`alloc`]: Self::alloc
/// [`dealloc`]: Self::dealloc
pub struct BulkAlloc<B>
where
    B: GlobalAlloc,
{
    large_cache: UnsafeCell<LargeCache>,
    small_cache: UnsafeCell<SmallCache>,
    to_free: Cell<Link<u8>>,
    backend: B,
}

impl<B> BulkAlloc<B>
where
    B: GlobalAlloc,
{
    /// The max byte size that `BulkAlloc` can cache.
    pub const MAX_CACHE_SIZE: usize = MEMORY_CHUNK_SIZE - size_of::<Link<u8>>();
}

impl<B> Drop for BulkAlloc<B>
where
    B: GlobalAlloc,
{
    fn drop(&mut self) {
        let mut it = self.to_free.get();

        unsafe {
            let layout = Layout::from_size_align(MEMORY_CHUNK_SIZE, ALIGN).unwrap();

            while let Some(ptr) = it {
                it = NonNull::new(*ptr.cast().as_ref());

                let ptr = ptr.as_ptr().offset(-1 * Self::MAX_CACHE_SIZE as isize);
                self.backend.dealloc(ptr, layout);
            }
        }
    }
}

impl<B> BulkAlloc<B>
where
    B: GlobalAlloc,
{
    /// Creates a new instance.
    pub const fn new(backend: B) -> Self {
        Self {
            large_cache: UnsafeCell::new(LargeCache::new()),
            small_cache: UnsafeCell::new(SmallCache::new()),
            to_free: Cell::new(None),
            backend,
        }
    }
}

unsafe impl<B> GlobalAlloc for BulkAlloc<B>
where
    B: GlobalAlloc,
{
    /// Method `alloc` delegates the request to the backend if `layout` is too large (i.e. the size is
    /// greater than [`MAX_CACHE_SIZE`] or the align is greater than [`align_of::<usize>()`](align_of).
    /// Note that usually, the alignment of [`Layout`] is less than
    /// or equals to the value unless the caller dares to enlarge it.)
    ///
    /// Otherwise, `alloc` searches the cache for a larger or the same size memory in the cache.
    /// If no proper memory is found, it acquires a [`MEMORY_CHUNK_SIZE`] bytes chunk
    /// from the backend allocator at first.
    /// Then, it takes a pointer from the memory block to return and caches the rest again.
    ///
    /// # Safety
    ///
    /// All the pointers allocated via the instance will be invalid after the instance drop.
    /// Accessing such a pointer may lead to memory unsafety even if the pointer itself is not
    /// deallocated.
    ///
    /// [read more](std::alloc::GlobalAlloc::alloc)
    ///
    /// [`MAX_CACHE_SIZE`]: Self::MAX_CACHE_SIZE
    /// [`align_of`]: std::mem::align_of
    /// [`Layout`]: std::alloc::Layout
    /// [`MEMORY_CHUNK_SIZE`]: crate::MEMORY_CHUNK_SIZE
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // Delegate the request if layout is too large.
        if Self::MAX_CACHE_SIZE < layout.size() || ALIGN < layout.align() {
            return self.backend.alloc(layout);
        }

        // Round up size.
        let request_size = (layout.size() + ALIGN - 1) / ALIGN * ALIGN;

        let small_cache = &mut *self.small_cache.get();
        let large_cache = &mut *self.large_cache.get();

        // Search memory block in small_cache and large_cache.
        // If no cache is hit, allocate from the backend.
        let (ptr, alloc_size) = if let Some((ptr, size)) = small_cache.alloc(request_size) {
            (ptr, size)
        } else if let Some((ptr, size)) = large_cache.alloc(request_size) {
            (ptr, size)
        } else {
            let layout = Layout::from_size_align(MEMORY_CHUNK_SIZE, ALIGN).unwrap();
            let ptr = self.backend.alloc(layout);

            if ptr.is_null() {
                return ptr;
            } else {
                // Take the end of memory block and append to self.to_free.
                {
                    let ptr = ptr.add(Self::MAX_CACHE_SIZE);
                    *ptr.cast() = self
                        .to_free
                        .get()
                        .map(NonNull::as_ptr)
                        .unwrap_or(null_mut());
                    self.to_free.set(NonNull::new(ptr));
                }

                (NonNull::new_unchecked(ptr), Self::MAX_CACHE_SIZE)
            }
        };

        debug_assert!(alloc_size % ALIGN == 0);

        // Take the end of the memory block as the return value, and cache the rest again if necessary.
        let rest_size = alloc_size - request_size;
        if 0 < rest_size {
            let _is_ok = large_cache.dealloc_without_merge(ptr, rest_size)
                || small_cache.dealloc(ptr, rest_size);
            debug_assert!(_is_ok);
        }

        ptr.as_ptr().add(rest_size)
    }

    /// Method `dealloc` delegates the request to the backend if `layout` is too large (i.e. the size
    /// is greater than [`MAX_CACHE_SIZE`] or the align is greater
    /// than [`align_of::<usize>()`](align_of).
    /// Note that usually, the alignment of [`Layout`] is less than or equals to the value
    /// unless the caller dare to enlarge it.)
    ///
    /// Otherwise, `dealloc` stores the passed pointer into the proper cache.
    /// It is when the instance is dropped when the pointer is released.
    ///
    /// # Safety
    ///
    /// All the pointers allocated via the instance will be invalid after the instance drop.
    /// Accessing such a pointer may lead to memory unsafety even if the pointer itself is not
    /// deallocated.
    ///
    /// [read more](std::alloc::GlobalAlloc::dealloc)
    ///
    /// [`MAX_CACHE_SIZE`]: Self::MAX_CACHE_SIZE
    /// [`Layout`]: std::alloc::Layout
    /// [`align_of`]: std::mem::align_of
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // Delegate the request if layout is too large.
        if Self::MAX_CACHE_SIZE < layout.size() || ALIGN < layout.align() {
            self.backend.dealloc(ptr, layout);
            return;
        }

        // Round up size.
        let size = (layout.size() + ALIGN - 1) / ALIGN * ALIGN;
        debug_assert!(ptr as usize % ALIGN == 0);

        // Cache ptr.
        let small_cache = &mut *self.small_cache.get();
        let large_cache = &mut *self.large_cache.get();
        let ptr = NonNull::new(ptr).unwrap();

        let _is_ok = large_cache.dealloc(ptr, size) || small_cache.dealloc(ptr, size);
        debug_assert!(_is_ok);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use gharial::GAlloc;

    type Alloc = BulkAlloc<GAlloc>;

    #[test]
    fn test_alloc_large_layout() {
        let backend = GAlloc::default();
        let alloc = BulkAlloc::new(backend.clone());

        // Large align
        for size in (1..64).chain([Alloc::MAX_CACHE_SIZE, Alloc::MAX_CACHE_SIZE + 1]) {
            unsafe {
                let align = 2 * ALIGN;
                let layout = Layout::from_size_align(size, align).unwrap();

                let ptr = alloc.alloc(layout);
                assert_eq!(ptr.is_null(), false);
                assert_eq!(backend.providing_pointers(), [(ptr, layout)]);

                ptr.write_bytes(0xff, size);
                alloc.dealloc(ptr, layout);
            }
        }

        // Large size
        let mut align = 1;
        while align <= ALIGN {
            unsafe {
                let size = Alloc::MAX_CACHE_SIZE + 1;
                let layout = Layout::from_size_align(size, align).unwrap();

                let ptr = alloc.alloc(layout);
                assert_eq!(ptr.is_null(), false);
                assert_eq!(backend.providing_pointers(), [(ptr, layout)]);

                ptr.write_bytes(0xff, size);
                alloc.dealloc(ptr, layout);
            }

            align *= 2;
        }
    }

    #[test]
    fn test_alloc_dealloc() {
        let backend = GAlloc::default();
        let alloc = Alloc::new(backend.clone());

        unsafe {
            for _ in 0..16 {
                let mut align = 1;
                let mut pointers = Vec::new();

                while align <= ALIGN {
                    for size in (0..1024).chain([Alloc::MAX_CACHE_SIZE]) {
                        let layout = Layout::from_size_align(size, align).unwrap();
                        let ptr = alloc.alloc(layout);

                        assert_eq!(ptr.is_null(), false);
                        ptr.write_bytes(0xff, layout.size());
                        pointers.push((ptr, layout));
                    }

                    align *= 2;
                }

                for (ptr, layout) in pointers {
                    alloc.dealloc(ptr, layout);
                }
            }
        }
    }
}
