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
use crate::{MEMORY_CHUNK_SIZE, MIN_CACHE_SIZE};
use core::alloc::{AllocErr, AllocInit, AllocRef, Layout, MemoryBlock};
use core::mem::size_of;
use core::ptr::NonNull;
use core::result::Result;
use std::sync::atomic::{AtomicBool, Ordering};

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
    pub fn from_layout(layout: Layout) -> Self {
        Self {
            layout,
            pool: Default::default(),
            to_free: Default::default(),
            backend: Default::default(),
        }
    }
}

impl<B: AllocRef> LayoutBulkAllocator<'static, B> {
    pub fn from_layout_backend(layout: Layout, backend: B) -> Self {
        Self {
            layout,
            pool: Default::default(),
            to_free: Default::default(),
            backend: Backend::from(backend),
        }
    }
}

impl<'a, B: 'a + AllocRef> LayoutBulkAllocator<'a, B> {
    pub fn from_layout_mut_backend(layout: Layout, backend: &'a mut B) -> Self {
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

unsafe impl<B: AllocRef> AllocRef for LayoutBulkAllocator<'_, B> {
    fn alloc(&mut self, layout: Layout, init: AllocInit) -> Result<MemoryBlock, AllocErr> {
        if layout != self.layout {
            self.backend.alloc(layout, init)
        } else {
            let size = core::cmp::max(MIN_CACHE_SIZE, layout.pad_to_align().size());

            // Try to fetch the cache.
            let mut ptr = self.pool.pop();

            // Make cache and try again.
            if ptr.is_none() {
                let mut block = self
                    .backend
                    .alloc(self.memory_chunk_layout(), AllocInit::Uninitialized)?;

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
                ptr: ptr.unwrap().cast::<u8>(),
                size,
            };

            // Fill the block with 0 if necessary
            if init == AllocInit::Zeroed {
                unsafe {
                    core::ptr::write_bytes(block.ptr.as_ptr(), 0, block.size);
                }
            }

            Ok(block)
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

            // AllocInit::Uninitialized
            {
                let block = alloc.alloc(layout, AllocInit::Uninitialized).unwrap();

                assert!(layout.size() <= block.size);

                let ptr = block.ptr.as_ptr() as usize;
                assert_eq!(0, ptr % layout.align());

                unsafe {
                    alloc.dealloc(block.ptr, layout);
                }
            }

            // AllocInit::Zeroed
            {
                let block = alloc.alloc(layout, AllocInit::Zeroed).unwrap();

                assert!(layout.size() <= block.size);

                let ptr = block.ptr.as_ptr() as usize;
                assert_eq!(0, ptr % layout.align());

                unsafe {
                    let s = core::slice::from_raw_parts(ptr as *const u8, block.size);
                    for &u in s {
                        assert_eq!(0, u);
                    }

                    alloc.dealloc(block.ptr, layout);
                }
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
        let block = alloc.alloc(layout, AllocInit::Uninitialized).unwrap();
        assert_eq!(1, alloc.memory_chunk_count());
        unsafe {
            alloc.dealloc(block.ptr, layout);
        }

        // Repeatable alloc()/dealloc() call won't change the chunk count.
        for _ in 0..1024 {
            let block = alloc.alloc(layout, AllocInit::Zeroed).unwrap();
            assert_eq!(1, alloc.memory_chunk_count());
            unsafe {
                alloc.dealloc(block.ptr, layout);
            }
        }

        let mut ptrs = Vec::new();
        for i in 1..10 {
            for _ in 0..((MEMORY_CHUNK_SIZE - size_of::<PtrList>()) / size) {
                let block = alloc.alloc(layout, AllocInit::Zeroed).unwrap();
                ptrs.push(block.ptr);
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

                let block = alloc.alloc(layout_, AllocInit::Uninitialized).unwrap();
                assert_eq!(chunk_count, alloc.memory_chunk_count());
                unsafe {
                    alloc.dealloc(block.ptr, layout);
                }
            }
        }

        // Deallocation won't change the chunk count
        for &ptr in &ptrs {
            unsafe {
                alloc.dealloc(ptr, layout);
            }
            assert_eq!(chunk_count, alloc.memory_chunk_count());
        }
    }
}
