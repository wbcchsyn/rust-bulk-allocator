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

/// Structure for `Sba` and `Usba` .
struct Cache {
    to_free: PtrList,
    pool: PtrList,
}

impl Drop for Cache {
    fn drop(&mut self) {
        // Make sure 'self.to_free' is empty.
        debug_assert_eq!(None, self.to_free.pop());
    }
}

impl Cache {
    /// Creates a new instance.
    pub const fn new() -> Self {
        Self {
            to_free: PtrList::new(),
            pool: PtrList::new(),
        }
    }

    /// Frees all the bulk memories via `backend`.
    pub fn destroy<B>(&mut self, layout: Layout, backend: &B)
    where
        B: GlobalAlloc,
    {
        let layout = Self::backend_layout(layout);
        while let Some(ptr) = self.to_free.pop() {
            debug_assert_eq!(false, ptr.is_null());
            unsafe { backend.dealloc(ptr, layout) };
        }
    }

    /// Pools `ptr` to the cache.
    pub fn dealloc(&mut self, ptr: *mut u8) {
        debug_assert_eq!(false, ptr.is_null());
        let ptr = unsafe { NonNull::new_unchecked(ptr) };
        self.pool.push(ptr);
    }

    /// Pops from the cache and returns. If cache is empty, allocates memory chunk from `backend`
    /// and makes cache at first.
    pub fn alloc<B>(&mut self, layout: Layout, backend: &B) -> *mut u8
    where
        B: GlobalAlloc,
    {
        // Search the cache at first.
        if let Some(ptr) = self.pool.pop() {
            return ptr;
        }

        // If no cache is, allocate memory chunk.
        let (begin, end) = unsafe {
            let layout = Self::backend_layout(layout);
            let begin = backend.alloc(layout);
            if begin.is_null() {
                // Returns null pointer on fail.
                return begin;
            }
            let end = begin.add(layout.size());
            (begin, end)
        };

        // Use the first position of the chunk as to_free link.
        {
            let ptr = unsafe { NonNull::new_unchecked(begin) };
            self.to_free.push(ptr);
        }

        // Split into small pieces and make cache
        unsafe {
            // Shift ptr by the size of to_free link.
            let mut ptr = begin.add(Self::to_free_layout(layout).size());
            let size = Self::element_layout(layout).size();

            while (size as isize) <= end.offset_from(ptr) {
                self.pool.push(NonNull::new_unchecked(ptr));
                ptr = ptr.add(size);
            }
        }

        self.pool.pop().unwrap()
    }

    fn align(layout: Layout) -> usize {
        usize::max(layout.align(), align_of::<PtrList>())
    }

    fn element_layout(layout: Layout) -> Layout {
        let align = Self::align(layout);
        let size = usize::max(layout.size(), size_of::<PtrList>());
        let layout = unsafe { Layout::from_size_align_unchecked(size, align) };
        layout.pad_to_align()
    }

    fn to_free_layout(layout: Layout) -> Layout {
        let align = Self::align(layout);
        let size = size_of::<PtrList>();
        let layout = unsafe { Layout::from_size_align_unchecked(size, align) };
        layout.pad_to_align()
    }

    fn backend_layout(layout: Layout) -> Layout {
        let align = Self::align(layout);
        let min_size = Self::element_layout(layout).size() + Self::to_free_layout(layout).size();
        let size = usize::max(min_size, MEMORY_CHUNK_SIZE);
        unsafe { Layout::from_size_align_unchecked(size, align) }
    }
}

#[cfg(test)]
mod cache_tests {
    use super::*;
    use gharial::GAlloc;
    use std::collections::HashSet;

    const SMALL_SIZES: &[usize] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 63, 64, 65];
    const LARGE_SIZES: &[usize] = &[
        MEMORY_CHUNK_SIZE - 1,
        MEMORY_CHUNK_SIZE,
        MEMORY_CHUNK_SIZE + 1,
    ];
    const SMALL_ALIGNS: &[usize] = &[1, 2, 4, 8, 16];
    const LARGE_ALIGNS: &[usize] = &[
        MEMORY_CHUNK_SIZE / 2,
        MEMORY_CHUNK_SIZE,
        MEMORY_CHUNK_SIZE * 2,
    ];

    #[test]
    fn new() {
        let layout = Layout::new::<usize>();
        let backend = GAlloc::default();

        let mut cache = Cache::new();
        cache.destroy(layout, &backend);
    }

    #[test]
    fn alloc_small() {
        let check = |layout| {
            let backend = GAlloc::default();
            let mut cache = Cache::new();
            let mut pointers = HashSet::with_capacity(MEMORY_CHUNK_SIZE);

            for _ in 0..MEMORY_CHUNK_SIZE {
                let ptr = cache.alloc(layout, &backend);
                assert_eq!(true, pointers.insert(ptr));
            }

            for &ptr in pointers.iter() {
                cache.dealloc(ptr);
            }

            cache.destroy(layout, &backend);
        };

        for &size in SMALL_SIZES {
            for &align in SMALL_ALIGNS {
                let layout = Layout::from_size_align(size, align).unwrap();
                check(layout);
            }
        }
    }

    #[test]
    fn alloc_large() {
        let check = |layout| {
            let backend = GAlloc::default();
            let mut cache = Cache::new();
            let mut pointers = HashSet::with_capacity(3);

            for _ in 0..3 {
                let ptr = cache.alloc(layout, &backend);
                assert_eq!(true, pointers.insert(ptr));
            }

            for &ptr in pointers.iter() {
                cache.dealloc(ptr);
            }

            cache.destroy(layout, &backend);
        };

        for &size in SMALL_SIZES.iter().chain(LARGE_SIZES.iter()) {
            for &align in SMALL_ALIGNS.iter().chain(LARGE_ALIGNS.iter()) {
                let layout = Layout::from_size_align(size, align).unwrap();
                check(layout);
            }
        }
    }

    #[test]
    fn alloc_effectivity() {
        let check = |layout| {
            let backend = GAlloc::default();
            let mut cache = Cache::new();

            for _ in 0..MEMORY_CHUNK_SIZE {
                let ptr = cache.alloc(layout, &backend);
                cache.dealloc(ptr);

                // Make sure only one memory chunk is.
                assert_eq!(1, cache.to_free.len());
            }

            cache.destroy(layout, &backend);
        };

        for &size in SMALL_SIZES.iter().chain(LARGE_SIZES.iter()) {
            for &align in SMALL_ALIGNS.iter().chain(LARGE_ALIGNS.iter()) {
                let layout = Layout::from_size_align(size, align).unwrap();
                check(layout);
            }
        }
    }
}

/// 'Usba' stands for 'Unsafe Single-layout-cache Bulk Allocator'.
/// This implements `GlobalAlloc` . It allocates and caches bulk memory from the backend, and
/// deallocates them on the drop at once.
///
/// Constructor takes a `Layout` as the argument, and builds instance with cache for memories which
/// fits the `Layout` .
///
/// Method `alloc` causes an assertion error if the specified `Layout` is different from that is
/// passed to the constructor. (This is why named as 'Unsafe'.)
/// Otherwise, `alloc` searches the cache for an available pointer and returns it. If the cache is
/// empty, `alloc` allocates a memory chunk from the backend allocator, splits the chunk into
/// pieces to fit the `Layout` , and makes cache at first.
///
/// The size of the bulk memory is usualy same to [`MEMORY_CHUNK_SIZE`] , however, if the `Layout`
/// is too large, the size exceeds [`MEMORY_CHUNK_SIZE`] .
///
/// Method `dealloc` always caches the passed pointer. i.e. the memory will not be freed then. It
/// is when the instance is dropped to deallocate the memories.
///
/// Instance drop releases all the memory chunks using the backend allocator. All the pointers
/// allocated via the instance will be invalid after the instance drop. Accessing such a pointer
/// may lead memory unsafety even if the pointer itself is not deallocated.
///
/// This struct is similar to [`Sba`] except for the behavior when `alloc` and `dealloc` was
/// passed different argument `Layout` from that is passed to the constructor. See also [`Sba`] .
///
/// # Warnings
///
/// The allocated pointers via `Usba` will be invalid after the instance is dropped. Accessing such
/// a pointer may lead memory unsafety evenn if the pointer itself is not deallocated.
///
/// # Errors
///
/// `alloc` causes an assertion error if the specified `Layout` is different from that is passed to
/// the constructor.
///
/// [`MEMORY_CHUNK_SIZE`]: constant.MEMORY_CHUNK_SIZE.html
/// [`Sba`]: struct.Sba.html
pub struct Usba<B>
where
    B: GlobalAlloc,
{
    layout_: Layout,
    cache: UnsafeCell<Cache>,
    backend_: B,
}

unsafe impl<B> Send for Usba<B> where B: Send + GlobalAlloc {}

impl<B> Drop for Usba<B>
where
    B: GlobalAlloc,
{
    fn drop(&mut self) {
        let cache = unsafe { &mut *self.cache.get() };
        cache.destroy(self.layout(), self.backend());
    }
}

impl<B> From<Layout> for Usba<B>
where
    B: Default + GlobalAlloc,
{
    fn from(layout: Layout) -> Self {
        Self::new(layout, B::default())
    }
}

impl<B> Usba<B>
where
    B: GlobalAlloc,
{
    /// Creates a new instance with empty cache.
    ///
    /// The cache is built for memories to fit `layout` and method `alloc` can take same value as
    /// the argument; otherwise `alloc` causes an assertion error.
    ///
    /// `backend` is an allocator to allocate memory chunks to make cache. It is also used to
    /// deallocate the memory chunks on the drop.
    ///
    /// # Examples
    ///
    /// ```
    /// use bulk_allocator::Usba;
    /// use std::alloc::{Layout, System};
    ///
    /// let layout = Layout::new::<usize>();
    /// let _usba = Usba::new(layout, System);
    /// ```
    pub fn new(layout: Layout, backend: B) -> Self {
        Self {
            layout_: layout,
            cache: UnsafeCell::new(Cache::new()),
            backend_: backend,
        }
    }
}

unsafe impl<B> GlobalAlloc for Usba<B>
where
    B: GlobalAlloc,
{
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        assert_eq!(self.layout(), layout);

        let cache = &mut *self.cache.get();
        cache.alloc(layout, self.backend())
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        debug_assert_eq!(false, ptr.is_null());
        debug_assert_eq!(self.layout(), layout);

        let cache = &mut *self.cache.get();
        cache.dealloc(ptr)
    }
}

impl<B> Usba<B>
where
    B: GlobalAlloc,
{
    /// Returns same `Layout` that is passed to the constructor.
    /// The cache is build for this `Layout` and method `alloc` can take only this value as the
    /// argument; otherwise `alloc` causes an assertion error.
    ///
    /// # Examples
    ///
    /// ```
    /// use bulk_allocator::Usba;
    /// use std::alloc::{Layout, System};
    ///
    /// let layout = Layout::new::<usize>();
    /// let usba = Usba::new(layout, System);
    /// assert_eq!(layout, usba.layout());
    /// ```
    pub fn layout(&self) -> Layout {
        self.layout_
    }

    /// Provides a reference to the backend allocator.
    pub fn backend(&self) -> &B {
        &self.backend_
    }
}

#[cfg(test)]
mod usba_tests {
    use super::*;
    use gharial::GAlloc;

    #[test]
    fn new() {
        let layout = Layout::new::<u8>();
        let _usba = Usba::new(layout, GAlloc::default());
    }

    #[test]
    fn alloc_dealloc() {
        let layout = Layout::new::<[u8; 16]>();
        let usba = Usba::new(layout, GAlloc::default());

        unsafe {
            let ptr = usba.alloc(layout);
            assert_eq!(false, ptr.is_null());
            usba.dealloc(ptr, layout);
        }
    }
}

/// 'Sba' stands for 'Single-layout-cache Bulk Allocator'.
/// This implements `GlobalAlloc` . It allocates and caches bulk memory from the backend, and
/// deallocates them on the drop at once.
///
/// Constructor takes a `Layout` as the argument, and builds instance with cache for memories which
/// fits the `Layout` .
///
/// Method `alloc` delegates the request to the backend allocator if specified `Layout` is
/// different from that is passed to the constructor.
/// Otherwise, `alloc` searches the cache for an available pointer and returns it. If the cache is
/// empty, `alloc` allocates a memory chunk from the backend allocator, splits the chunk into
/// pieces to fit the `Layout` , and makes cache at first.
///
/// The size of the bulk memory is usualy same to [`MEMORY_CHUNK_SIZE`] , however, if the `Layout`
/// is too large, the size exceeds [`MEMORY_CHUNK_SIZE`] .
///
/// Method `dealloc` delegates the request to the backend allocator if specified `Layout` is
/// different from that is passed to the constructor; otherwise `dealloc` caches the pointer. i.e.
/// the memory will not be freed then. It is when the instance is dropped to deallocate the
/// memories.
///
/// Instance drop releases all the memory chunks using the backend allocator. Pointers allocated
/// via the instance will be invalid after the instance drop if the argument `Layout` is same
/// between the constructor and method `alloc` . Accessing such a pointer may lead memory unsafety
/// even if the pointer itself is not deallocated.
///
/// This struct is similar to [`Usba`] except for the behavior when `alloc` and `dealloc` was
/// passed different argument `Layout` from that is passed to the constructor. See also [`Usba`] .
///
/// # Warnings
///
/// Pointers allocated vir the instance will be invalid after the instance drop if the argument
/// `Layout` is same between the constructor and method `alloc` . Accessing such a pointer may lead
/// memory unsafety even if the pointer itself is not deallocated.
///
///
/// [`MEMORY_CHUNK_SIZE`]: constant.MEMORY_CHUNK_SIZE.html
/// [`Usba`]: struct.Usba.html
pub struct Sba<B>
where
    B: GlobalAlloc,
{
    inner: Usba<B>,
}

impl<B> Sba<B>
where
    B: GlobalAlloc,
{
    /// Creates a new instance with empty cache.
    ///
    /// The cache is built for memories to fit `layout` and method `alloc` uses the cache only when
    /// the same `layout` is passed; otherwise `alloc` just delegates the request to the backend.
    ///
    /// `backend` is an allocator to allocate memory chunks to make cache. It is also used to
    /// deallocate the memory chunks on the drop.
    ///
    /// # Examples
    ///
    /// ```
    /// use bulk_allocator::Sba;
    /// use std::alloc::{Layout, System};
    ///
    /// let layout = Layout::new::<usize>();
    /// let _sba = Sba::new(layout, System);
    /// ```
    pub fn new(layout: Layout, backend: B) -> Self {
        Self {
            inner: Usba::new(layout, backend),
        }
    }
}

impl<B> Sba<B>
where
    B: GlobalAlloc,
{
    /// Returns same `Layout` that is passed to the constructor.
    /// The cache is build for this `Layout` and method `alloc` can take only this value as the
    /// argument; otherwise `alloc` causes an assertion error.
    ///
    /// # Examples
    ///
    /// ```
    /// use bulk_allocator::Sba;
    /// use std::alloc::{Layout, System};
    ///
    /// let layout = Layout::new::<usize>();
    /// let sba = Sba::new(layout, System);
    /// assert_eq!(layout, sba.layout());
    /// ```
    pub fn layout(&self) -> Layout {
        self.inner.layout()
    }

    /// Provides a reference to the backend allocator.
    pub fn backend(&self) -> &B {
        &self.inner.backend()
    }
}

#[cfg(test)]
mod sba_tests {
    use super::*;
    use gharial::GAlloc;

    #[test]
    fn new() {
        let layout = Layout::new::<usize>();
        let _sba = Sba::new(layout, GAlloc::default());
    }
}
