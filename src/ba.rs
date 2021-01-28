// Copyright 2020 Shin Yoshida
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

use crate::{PtrList, MEMORY_CHUNK_SIZE};
use core::alloc::{GlobalAlloc, Layout};
use core::cell::UnsafeCell;
use core::mem::{align_of, size_of};
use core::ptr::NonNull;

/// Inner type of 'Ba' and 'Uba'.
pub struct Cache {
    to_free: PtrList,
    pools: [PtrList; Self::POOLS_LEN],
}

impl Cache {
    pub const MAX_CACHE_SIZE: usize = 4096; // 4 KB.
    pub const MIN_CACHE_SIZE: usize = size_of::<PtrList>();
    const POOLS_LEN: usize =
        (Self::MIN_CACHE_SIZE.leading_zeros() - Self::MAX_CACHE_SIZE.leading_zeros() + 1) as usize;
}

impl Drop for Cache {
    fn drop(&mut self) {
        // Make sure 'self.to_free' is empty.
        debug_assert_eq!(None, self.to_free.pop());
    }
}

impl Cache {
    /// Creates a new empty instance.
    pub const fn new() -> Self {
        Self {
            to_free: PtrList::new(),
            pools: [PtrList::new(); Self::POOLS_LEN],
        }
    }

    /// Deallocates all the allocated memory chunks and clears `self.to_free` .
    pub fn destroy<B>(&mut self, backend: &B)
    where
        B: GlobalAlloc,
    {
        let layout = Self::backend_layout();
        while let Some(ptr) = self.to_free.pop() {
            unsafe { backend.dealloc(ptr, layout) };
        }
    }

    pub unsafe fn alloc<B>(&mut self, layout: Layout, backend: &B) -> *mut u8
    where
        B: GlobalAlloc,
    {
        let layout = Self::fit_layout(layout).unwrap();

        // If some pointer is cached, just return it.
        if let Some(ptr) = self.pop_cache(layout) {
            return ptr;
        }

        // Allocate a memory chunk from the backend.
        let block = {
            let layout = Self::backend_layout();
            let ptr = backend.alloc(layout);
            // Return null pointer if failed.
            if ptr.is_null() {
                return ptr;
            }

            core::slice::from_raw_parts_mut(ptr, layout.size())
        };

        // Add block to the self.to_free list.
        let block = {
            let layout = Self::to_free_layout();
            let (f, s) = block.split_at_mut(layout.size());

            let ptr = NonNull::new_unchecked(f.as_mut_ptr());
            self.to_free.push(ptr);

            s
        };

        self.fill_cache(block, 0);
        self.pop_cache(layout).unwrap()
    }

    /// Pools `ptr` to the cache.
    ///
    /// Causes an assertion error if `layout` is not in the range to be cached.
    pub unsafe fn dealloc(&mut self, ptr: *mut u8, layout: Layout) {
        debug_assert_eq!(false, ptr.is_null());

        let layout = Self::fit_layout(layout).unwrap();
        let index = Self::pools_index(layout);

        let ptr = NonNull::new_unchecked(ptr);
        self.pools[index].push(ptr);
    }

    fn fit_layout(layout: Layout) -> Option<Layout> {
        // 'size' is the minimum number satisfying followings.
        // - a Power of 2.
        // - layout.size() <= size
        let size = if layout.size().count_ones() == 1 {
            layout.size()
        } else {
            (usize::MAX >> layout.size().leading_zeros()) as usize + 1
        };
        debug_assert_eq!(1, size.count_ones());
        debug_assert!(layout.size() <= size);
        debug_assert!(size <= 2 * layout.size());

        let size = usize::max(Self::MIN_CACHE_SIZE, size);
        let layout = unsafe { Layout::from_size_align_unchecked(size, Self::align()) };
        let layout = layout.pad_to_align();

        if Self::MAX_CACHE_SIZE < layout.size() {
            None
        } else {
            Some(layout)
        }
    }

    fn pools_index(layout: Layout) -> usize {
        debug_assert!(layout.size() <= Self::MAX_CACHE_SIZE);
        debug_assert!(Self::MIN_CACHE_SIZE <= layout.size());
        debug_assert_eq!(1, layout.size().count_ones());

        (layout.size().leading_zeros() - Self::MAX_CACHE_SIZE.leading_zeros()) as usize
    }

    fn fill_cache(&mut self, memory_block: &mut [u8], index_hint: usize) {
        let mut block = memory_block;

        for i in index_hint..Self::POOLS_LEN {
            let pool_size = Self::MAX_CACHE_SIZE >> i;

            while pool_size <= block.len() {
                unsafe {
                    let (f, s) = block.split_at_mut(pool_size);
                    self.pools[i].push(NonNull::new_unchecked(f.as_mut_ptr()));
                    block = s;
                }
            }
            if block.is_empty() {
                break;
            }
        }
    }

    fn pop_cache(&mut self, layout: Layout) -> Option<*mut u8> {
        let index = Self::pools_index(layout);

        // If a pointer to fit layout is cached, just return it.
        if let Some(ptr) = self.pools[index].pop() {
            return Some(ptr);
        }

        // Try to find a cache greater than layout.
        // If found, return it. The rest of the memory block will be cached again.
        for i in (0..index).rev() {
            match self.pools[i].pop() {
                None => continue,

                Some(ptr) => {
                    let size = Self::MAX_CACHE_SIZE >> i;
                    let block = unsafe { core::slice::from_raw_parts_mut(ptr, size) };
                    let (_, s) = block.split_at_mut(layout.size());

                    self.fill_cache(s, i + 1);
                    return Some(ptr);
                }
            }
        }

        None
    }

    const fn align() -> usize {
        // Same to usize::max(align_of::<PtrList>(), align_of::<u128>()).
        // (usize::max is not a const function.)
        if align_of::<PtrList>() < align_of::<u128>() {
            align_of::<u128>()
        } else {
            align_of::<PtrList>()
        }
    }

    fn to_free_layout() -> Layout {
        let layout =
            unsafe { Layout::from_size_align_unchecked(size_of::<PtrList>(), Self::align()) };
        layout.pad_to_align()
    }

    const fn backend_layout() -> Layout {
        let size = MEMORY_CHUNK_SIZE;
        let align = Self::align();
        unsafe { Layout::from_size_align_unchecked(size, align) }
    }
}

#[cfg(test)]
mod cache_tests {
    use super::*;
    use gharial::GAlloc;
    use std::collections::HashSet;

    #[test]
    fn new() {
        let backend = GAlloc::default();
        let mut cache = Cache::new();
        cache.destroy(&backend);
    }

    #[test]
    fn alloc_dealloc() {
        let check = |layout| {
            let backend = GAlloc::default();
            let mut cache = Cache::new();
            let mut pointers = HashSet::with_capacity(MEMORY_CHUNK_SIZE);

            for _ in 0..MEMORY_CHUNK_SIZE {
                let ptr = unsafe { cache.alloc(layout, &backend) };
                assert_eq!(true, pointers.insert(ptr));
            }

            for &ptr in pointers.iter() {
                unsafe { cache.dealloc(ptr, layout) };
            }

            cache.destroy(&backend);
        };

        let mut size = 1;
        while size <= Cache::MAX_CACHE_SIZE {
            let mut align = 1;
            while align <= Cache::align() {
                let layout = Layout::from_size_align(size, align).unwrap();
                check(layout);
                align *= 2;
            }

            size *= 2;
        }
    }

    #[test]
    fn alloc_effectivity() {
        let check = |layout| {
            let backend = GAlloc::default();
            let mut cache = Cache::new();

            for _ in 0..MEMORY_CHUNK_SIZE {
                unsafe {
                    let ptr = cache.alloc(layout, &backend);
                    cache.dealloc(ptr, layout);

                    assert_eq!(1, cache.to_free.len());
                }
            }

            cache.destroy(&backend);
        };

        let mut size = 1;
        while size <= Cache::MAX_CACHE_SIZE {
            let mut align = 1;
            while align <= Cache::align() {
                let layout = Layout::from_size_align(size, align).unwrap();
                check(layout);
                align *= 2;
            }

            size *= 2;
        }
    }
}

/// 'Uba' stands for 'Unsafe Bulk Allocator'.
/// This implements `GlobalAlloc` . It allocates and caches bulk memory from the backend, and
/// deallocates them on the drop at once.
///
/// The `Layout` to be cached is limited. `size` must be less than or equal to [`MAX_LAYOUT_SIZE`]
/// and `align` must be less than or equal to [`MAX_LAYOUT_ALIGN`] .
/// Method `alloc` causes an assertion error if argument `Layout` does not satisfy the conditions.
///
/// `alloc` tries to find a cached pointer and returns it if specified `Layout` is cacheable.
/// If appropriate cache is not found, tries to find a larger cache and splits it to return. (The
/// rest parts of the large cache will be cached again.)
/// If neither the appropriate nor larger cache is not found, it allocates a memory chunk from
/// backend, and makes a cache at first. (The size of memory chunk is same to [`MEMORY_CHUNK_SIZE`]
/// .)
///
/// Method `dealloc` always caches the passed pointer. i.e. the memory will not be freed then. It
/// is when the instance is dropped to deallocate the memories.
///
/// Instance drop releases all the memory chunks using the backend allocator. All the pointers
/// allocated via the instance will be invalid after the instance drop. Accessing such a pointer
/// may lead memory unsafety even if the pointer itself is not deallocated.
///
/// # Warnings
///
/// The allocated pointers via `Usba` will be invalid after the instance is dropped. Accessing such
/// a pointer may lead memory unsafety evenn if the pointer itself is not deallocated.
///
/// # Errors
///
/// `alloc` causes an assertion error if either `size` or `align` of the specified `Layout` is
/// greater than those of [`MAX_LAYOUT`] .
/// the constructor.
///
/// [`MEMORY_CHUNK_SIZE`]: constant.MEMORY_CHUNK_SIZE.html
/// [`MAX_LAYOUT_ALIGN`]: #associatedconstant.MAX_LAYOUT_ALIGN
/// [`MAX_LAYOUT_SIZE`]: #associatedconstant.MAX_LAYOUT_SIZE
pub struct Uba<B>
where
    B: GlobalAlloc,
{
    cache: UnsafeCell<Cache>,
    backend_: B,
}

impl<B> Uba<B>
where
    B: GlobalAlloc,
{
    /// The max size of the `Layout` that method `alloc` accepts.
    /// If specified `Layout` has greater size, `alloc` causes an assertion error.
    pub const MAX_LAYOUT_SIZE: usize = Cache::MAX_CACHE_SIZE;

    /// The max layout of the `Layout` that method `alloc` accepts.
    /// If specified `Layout` has greater align, `alloc` causes an assertion error.
    ///
    /// (Actually, the align of `Layout` usually equals to or less than this value except for that
    /// the programer dares to set some greater value for some reason.)
    pub const MAX_LAYOUT_ALIGN: usize = Cache::align();
}

impl<B> Drop for Uba<B>
where
    B: GlobalAlloc,
{
    fn drop(&mut self) {
        let cache = unsafe { &mut *self.cache.get() };
        cache.destroy(self.backend());
    }
}

impl<B> Uba<B>
where
    B: GlobalAlloc,
{
    /// Creates a new instance with empty cache.
    ///
    /// `backend` is an allocator to allocate memory chunks to make cache. It is also used to
    /// deallocate the memory chunks on the drop.
    ///
    /// # Examples
    ///
    /// ```
    /// use bulk_allocator::Uba;
    /// use std::alloc::System;
    ///
    /// let _uba = Uba::new(System);
    /// ```
    pub fn new(backend: B) -> Self {
        Self {
            cache: UnsafeCell::new(Cache::new()),
            backend_: backend,
        }
    }
}

impl<B> Uba<B>
where
    B: GlobalAlloc,
{
    /// Provides a reference to the backend allocator.
    pub fn backend(&self) -> &B {
        &self.backend_
    }
}

#[cfg(test)]
mod uba_tests {
    use super::*;
    use gharial::GAlloc;

    #[test]
    fn new() {
        let _uba = Uba::new(GAlloc::default());
    }
}
