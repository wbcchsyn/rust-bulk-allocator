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

use crate::backend::Backend;
use crate::ptr_list::PtrList;
use crate::split_memory_block;
use crate::MemoryBlock;
use crate::{MAX_CACHE_SIZE, MEMORY_CHUNK_SIZE, MIN_CACHE_SIZE};
use core::alloc::{AllocErr, AllocRef, Layout};
use core::mem::size_of;
use core::ptr::NonNull;
use core::result::Result;
use std::sync::atomic::{AtomicBool, Ordering};

/// `LayoutBulkAllocator` pools allocated memory and frees it on the destruction.
///
/// `alloc()` and `dealloc()` delegates the request if the layout is different from
/// what is specified to the constructor; otherwise, `dealloc()` caches the passed
/// pointer and `alloc()` returns the cache. If no memory is pooled, `alloc()`
/// allocate memory chunk from the backend, and makes caches at first.
///
/// Compared to `BulkAllocator` the performance of `LayoutBulkAllocator` is better than
/// that of `BulkAllocator` as long as the argument layout of `alloc()` and `dealloc()` is
/// same to which is passed to the constructor.
///
/// # Lifetime
///
/// Each instance owns or borrows the backend `AllocRef` instance. If it is borrowed, the lifetime
/// is limited by the reference; otherwise, the lifetime will be 'static.
///
/// # Thread safety
///
/// All the mutable methods are thread unsafe.
///
/// # Warnings
///
/// After drop, programer must NOT use the memories which method `alloc()` of this instance returned.
pub struct LayoutBulkAllocator<'a, B: 'a + AllocRef> {
    layout: Layout,
    pool: PtrList,
    // Memory chunks to be freed on the destruction.
    to_free: PtrList,
    // Backend allocator
    backend: Backend<'a, B>,
}

impl<B> LayoutBulkAllocator<'static, B>
where
    B: AllocRef + Default,
{
    /// Constructor specifies only the layout for the instance to use the cache.
    ///
    /// The backend `AllocRef` instance is created by `Default::default()`.
    /// The instance owns the backend, so there is no limitation for the lifetime.
    pub fn from_layout(layout: Layout) -> Self {
        Self::check_layout(layout);

        Self {
            layout,
            pool: Default::default(),
            to_free: Default::default(),
            backend: Default::default(),
        }
    }
}

impl<B: AllocRef> LayoutBulkAllocator<'static, B> {
    /// Construct a new instance from the layout and the backend `AllocRef` instance.
    ///
    /// The instance owns the backend, so there is no limitation of the lifetime.
    pub fn from_layout_backend(layout: Layout, backend: B) -> Self {
        Self::check_layout(layout);

        Self {
            layout,
            pool: Default::default(),
            to_free: Default::default(),
            backend: Backend::from(backend),
        }
    }
}

impl<'a, B: 'a + AllocRef> LayoutBulkAllocator<'a, B> {
    /// Construct a neww instance from the layout and the reference to the backend.
    ///
    /// The instance just borrows the backend, so the lifetime is limited.
    pub fn from_layout_mut_backend(layout: Layout, backend: &'a mut B) -> Self {
        Self::check_layout(layout);

        Self {
            layout,
            pool: Default::default(),
            to_free: Default::default(),
            backend: Backend::from(backend),
        }
    }
}

impl<B: AllocRef> Drop for LayoutBulkAllocator<'_, B> {
    fn drop(&mut self) {
        // Guarantees to deallocate the memory chunks only after the program finished
        // using memories self.alloc() returned.
        // (I am afraid of optimization.)
        let barrier = AtomicBool::new(false);
        barrier.load(Ordering::SeqCst);

        while let Some(ptr) = self.to_free.pop() {
            // move ptr to the first position of the chunk.
            let ptr = ptr.as_ptr() as usize;
            let ptr = ptr + size_of::<PtrList>() - self.memory_chunk_layout().size();

            unsafe {
                self.backend.dealloc(
                    NonNull::new_unchecked(ptr as *mut u8),
                    self.memory_chunk_layout(),
                );
            }
        }
    }
}

/// # Thread safety
///
/// All the methods are thread unsafe.
unsafe impl<B: AllocRef> AllocRef for LayoutBulkAllocator<'_, B> {
    fn alloc(&mut self, layout: Layout) -> Result<NonNull<[u8]>, AllocErr> {
        if layout != self.layout {
            self.backend.alloc(layout)
        } else {
            let size = core::cmp::max(MIN_CACHE_SIZE, layout.pad_to_align().size());

            // Try to fetch the cache.
            let mut ptr = self.pool.pop();

            // Make cache and try again.
            if ptr.is_none() {
                let block = self.backend.alloc(self.memory_chunk_layout())?;
                let mut block = MemoryBlock::from(block);

                {
                    let first_size = self.memory_chunk_layout().size() - size_of::<PtrList>();
                    let (f, s) = split_memory_block(block, first_size);

                    debug_assert!(size_of::<PtrList>() <= s.size);
                    self.to_free.push(s.ptr);
                    block = f;
                }

                // Dispatch and pool the first space.
                while size <= block.size {
                    let (f, s) = split_memory_block(block, size);
                    block = s;
                    self.pool.push(f.ptr);
                }

                ptr = self.pool.pop();
            }

            let block = MemoryBlock {
                ptr: ptr.unwrap(),
                size,
            };

            Ok(block.to_slice())
        }
    }

    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: Layout) {
        if layout == self.layout {
            self.pool.push(ptr);
        } else {
            self.backend.dealloc(ptr, layout);
        }
    }
}

impl<B: AllocRef> LayoutBulkAllocator<'_, B> {
    fn memory_chunk_layout(&self) -> Layout {
        Layout::from_size_align(MEMORY_CHUNK_SIZE, self.layout.align()).unwrap()
    }

    fn check_layout(layout: Layout) {
        assert!(layout.size() <= MAX_CACHE_SIZE);
        assert!(layout.align() <= MAX_CACHE_SIZE);
    }

    #[cfg(test)]
    fn memory_chunk_count(&self) -> usize {
        self.to_free.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{MAX_CACHE_SIZE, MIN_CACHE_SIZE};
    use std::alloc::Global;

    const SIZES: [usize; 10] = [
        1,
        2,
        3,
        4,
        5,
        MIN_CACHE_SIZE - 1,
        MIN_CACHE_SIZE,
        MIN_CACHE_SIZE + 1,
        MAX_CACHE_SIZE - 1,
        MAX_CACHE_SIZE,
    ];
    const ALIGNS: [usize; 4] = [2, 4, MIN_CACHE_SIZE, MAX_CACHE_SIZE];
    const LARGE_LAYOUTS: [Layout; 3] = unsafe {
        [
            Layout::from_size_align_unchecked(MAX_CACHE_SIZE + 1, MAX_CACHE_SIZE),
            Layout::from_size_align_unchecked(MAX_CACHE_SIZE, 2 * MAX_CACHE_SIZE),
            Layout::from_size_align_unchecked(MAX_CACHE_SIZE + 1, 2 * MAX_CACHE_SIZE),
        ]
    };

    #[test]
    fn from_layout_constructor() {
        let layout = Layout::from_size_align(35, 16).unwrap();
        let _ = LayoutBulkAllocator::<'static, Global>::from_layout(layout);
    }

    #[test]
    fn from_layout_backend_constructor() {
        let layout = Layout::from_size_align(64, 32).unwrap();
        let global = Default::default();
        let _ = LayoutBulkAllocator::<'static, Global>::from_layout_backend(layout, global);
    }

    #[test]
    fn from_layout_mut_backend_constructor() {
        let layout = Layout::from_size_align(64, 32).unwrap();
        let mut global = Default::default();
        let _ = LayoutBulkAllocator::<'_, Global>::from_layout_mut_backend(layout, &mut global);
    }

    #[test]
    fn alloc_and_dealloc_works() {
        let build = |size, align| {
            let layout = Layout::from_size_align(size, align).unwrap();
            LayoutBulkAllocator::<'static, Global>::from_layout(layout)
        };

        let check = |size, align, alloc: &mut LayoutBulkAllocator<'static, Global>| {
            let layout = Layout::from_size_align(size, align).unwrap();

            let block = alloc.alloc(layout).unwrap();

            assert!(layout.size() <= block.len());

            let ptr = unsafe { block.as_ref().as_ptr() } as usize;
            assert_eq!(0, ptr % layout.align());

            unsafe {
                alloc.dealloc(block.cast::<u8>(), layout);
            }
        };

        for &s in &SIZES {
            for &a in &ALIGNS {
                let mut alloc = build(s, a);

                for &s in &SIZES {
                    for &a in &ALIGNS {
                        check(s, a, &mut alloc);
                    }
                }

                for &l in &LARGE_LAYOUTS {
                    check(l.size(), l.align(), &mut alloc);
                }
            }
        }
    }

    #[test]
    fn chunk_count() {
        let layout = Layout::from_size_align(35, 16).unwrap();
        let mut alloc = LayoutBulkAllocator::<'static, Global>::from_layout(layout);

        let size = core::cmp::max(MIN_CACHE_SIZE, layout.pad_to_align().size());

        //  At first, no cache is
        assert_eq!(0, alloc.memory_chunk_count());

        // The first call of alloc() increases the chunk count.
        let block = alloc.alloc(layout).unwrap();
        assert_eq!(1, alloc.memory_chunk_count());
        unsafe {
            alloc.dealloc(block.cast::<u8>(), layout);
        }

        // Repeatable alloc()/dealloc() call won't change the chunk count.
        for _ in 0..1024 {
            let block = alloc.alloc(layout).unwrap();
            assert_eq!(1, alloc.memory_chunk_count());
            unsafe {
                alloc.dealloc(block.cast::<u8>(), layout);
            }
        }

        let mut ptrs = Vec::new();
        for i in 1..10 {
            for _ in 0..((MEMORY_CHUNK_SIZE - size_of::<PtrList>()) / size) {
                let block = alloc.alloc(layout).unwrap();
                ptrs.push(block);
                assert_eq!(i, alloc.memory_chunk_count());
            }
        }

        let chunk_count = alloc.memory_chunk_count();

        // If the request layout is different, the count will not be changed.
        for &s in &SIZES {
            for &a in &ALIGNS {
                let layout_ = Layout::from_size_align(s, a).unwrap();

                if layout == layout_ {
                    continue;
                }

                let block = alloc.alloc(layout_).unwrap();
                assert_eq!(chunk_count, alloc.memory_chunk_count());
                unsafe {
                    alloc.dealloc(block.cast::<u8>(), layout);
                }
            }
        }

        // Deallocation won't change the chunk count
        for &ptr in &ptrs {
            unsafe {
                alloc.dealloc(ptr.cast::<u8>(), layout);
            }
            assert_eq!(chunk_count, alloc.memory_chunk_count());
        }
    }
}
