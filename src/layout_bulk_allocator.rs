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
use crate::MEMORY_CHUNK_SIZE;
use core::alloc::{AllocErr, AllocInit, AllocRef, Layout, MemoryBlock};
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
            unsafe {
                self.backend
                    .dealloc(ptr.cast::<u8>(), self.memory_chunk_layout());
            }
        }
    }
}

unsafe impl<B: AllocRef> AllocRef for LayoutBulkAllocator<'_, B> {
    fn alloc(&mut self, layout: Layout, init: AllocInit) -> Result<MemoryBlock, AllocErr> {
        self.backend.alloc(layout, init)
    }

    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: Layout) {
        self.backend.dealloc(ptr, layout)
    }
}

impl<B: AllocRef> LayoutBulkAllocator<'_, B> {
    fn memory_chunk_layout(&self) -> Layout {
        Layout::from_size_align(MEMORY_CHUNK_SIZE, self.layout.align()).unwrap()
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
}
