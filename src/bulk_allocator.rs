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
use crate::cache_chain::CacheChain;
use crate::ptr_list::PtrList;
use crate::split_memory_block;
use crate::MEMORY_CHUNK_LAYOUT;
use core::alloc::{AllocErr, AllocInit, AllocRef, Layout, MemoryBlock};
use core::mem::size_of;
use core::ptr::NonNull;
use core::result::Result;
use std::alloc::Global;

/// BulkAllocator pools allocated memory and frees it on the destruction.
///
/// alloc() delegates the request to the backend if the requested layout is too
/// large to cache; otherwise, it dispatches the pooled memory and return. If no
/// memory is pooled, acquire memory chunk from the backend.
///
/// dealloc() delegates the request to the backend if the requested layout is too
/// large to cache; otherwise, it pools the passed memory.
pub struct BulkAllocator<'a, B: 'a + AllocRef> {
    pool: CacheChain,
    // Memory chunks to be freed on the destruction.
    to_free: PtrList,
    // Backend allocator
    backend: Backend<'a, B>,
}

impl Default for BulkAllocator<'static, Global> {
    fn default() -> Self {
        Self {
            pool: Default::default(),
            to_free: Default::default(),
            backend: Default::default(),
        }
    }
}

impl<B: AllocRef> From<B> for BulkAllocator<'static, B> {
    fn from(backend: B) -> Self {
        Self {
            pool: Default::default(),
            to_free: Default::default(),
            backend: From::from(backend),
        }
    }
}

impl<'a, B> From<&'a mut B> for BulkAllocator<'a, B>
where
    B: 'a + AllocRef,
{
    fn from(backend: &'a mut B) -> Self {
        Self {
            pool: Default::default(),
            to_free: Default::default(),
            backend: From::from(backend),
        }
    }
}

impl<B: AllocRef> Drop for BulkAllocator<'_, B> {
    fn drop(&mut self) {
        while let Some(ptr) = self.to_free.pop() {
            unsafe { self.backend.dealloc(ptr.cast::<u8>(), MEMORY_CHUNK_LAYOUT) }
        }
    }
}

unsafe impl<B: AllocRef> AllocRef for BulkAllocator<'_, B> {
    /// ToDo: Implement later
    fn alloc(&mut self, layout: Layout, init: AllocInit) -> Result<MemoryBlock, AllocErr> {
        match self.pool.find(layout) {
            // Too large for the pool
            None => self.backend.alloc(layout, init),
            Some(index) => {
                let block = match self.pool.pop(index) {
                    None => {
                        // Make cache and try again
                        let chunk = self
                            .backend
                            .alloc(MEMORY_CHUNK_LAYOUT, AllocInit::Uninitialized)?;
                        let (to_free, block) = split_memory_block(chunk, size_of::<PtrList>());

                        self.to_free.push(to_free.ptr);
                        self.pool.fill_cache(block);

                        self.pool.pop(index).unwrap()
                    }
                    // Cache is pooled.
                    Some(block) => block,
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
    }

    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: Layout) {
        // Pool if possible
        match self.pool.find(layout) {
            // Too large to cache
            None => self.backend.dealloc(ptr, layout),
            // Cache the memory
            Some(index) => self.pool.push(ptr, index),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{MAX_CACHE_SIZE, MIN_CACHE_SIZE};

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
    fn default_constructor() {
        let _ = BulkAllocator::<'static, Global>::default();
    }

    #[test]
    fn move_constructor() {
        let global = Global::default();
        let _ = BulkAllocator::<'static, Global>::from(global);
    }

    #[test]
    fn reference_constructor() {
        let mut global = Global::default();
        let _ = BulkAllocator::<'_, Global>::from(&mut global);
    }

    #[test]
    fn alloc_and_dealloc_works() {
        let mut alloc = BulkAllocator::default();

        let mut check = |size, align| {
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
                check(s, a);
            }
        }

        for &l in &LARGE_LAYOUTS {
            check(l.size(), l.align());
        }
    }
}
