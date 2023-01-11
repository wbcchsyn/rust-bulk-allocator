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

// TODO: Finish this module and replace into layout_bulk_a

use crate::{MemBlock, MEMORY_CHUNK_SIZE};
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::mem::{align_of, size_of};

type PointerList = *mut u8;

/// `UnsafeLayoutBulkAlloc` is an implementation of `GlobalAlloc`.
/// It caches memory blocks to allocate. If the cache is empty, acquires a memory chunk from the
/// backend and makes a cache at first. The allocated memory chunks are freed on the drop at once.
///
/// To cache effectively, each instance assumes that [`alloc`] is passed same `layout` every
/// time. The behavior is undefined if different `layout` is passed to the same
/// `UnsafeLayoutBulkAlloc` instance. See [`alloc`] for details. (This is why named 'Unsafe'.)
///
/// The size of the memory chunk is usually same to [`MEMORY_CHUNK_SIZE`] unless `layout` passed
/// to [`alloc`] is so large that at most one memory block can be acquired from
/// [`MEMORY_CHUNK_SIZE`].
///
/// Method `dealloc` always caches the passed pointer. i.e. the memory will not be freed then. It
/// is when the instance is dropped to deallocate the memories.
///
/// Instance drop releases all the memory chunks using the backend allocator. All the pointers
/// allocated via the instance will be invalid after then. Accessing such a pointer
/// may lead memory unsafety even if the pointer itself is not deallocated.
///
/// # Warnings
///
/// The allocated pointers via `UnsafeLayoutBulkAlloc` will be invalid after the instance is
/// dropped. Accessing such a pointer may lead memory unsafety evenn if the pointer itself is
/// not deallocated.
///
/// # Safety
///
/// The behavior is undefined if same instance is passed different `layout` to be called [`alloc`].
///
/// # Panics
///
/// Panics if different `layout` is passed to method [`alloc`] from that passed to the constructor.
///
/// [`MEMORY_CHUNK_SIZE`]: constant.MEMORY_CHUNK_SIZE.html
pub struct UnsafeLayoutBulkAlloc<B = System>
where
    B: GlobalAlloc,
{
    layout: Cell<Layout>, // Layout for u8 before initialized.
    to_free_list: Cell<PointerList>,
    pools: Cell<*mut MemBlock>,
    backend: B,
}

impl<B> UnsafeLayoutBulkAlloc<B>
where
    B: GlobalAlloc,
{
    /// Calculates the layout that method alloc() returns.    
    fn block_layout(layout: Layout) -> Layout {
        let size = std::cmp::max(layout.size(), size_of::<MemBlock>());
        let align = std::cmp::max(layout.align(), align_of::<MemBlock>());

        let not_padded = unsafe { Layout::from_size_align_unchecked(size, align) };
        let padded = not_padded.pad_to_align();

        if MEMORY_CHUNK_SIZE < 2 * padded.size() + size_of::<PointerList>() {
            not_padded
        } else {
            padded
        }
    }
}

#[cfg(test)]
mod unsafe_layout_bulk_alloc_tests {
    use super::*;
    use gharial::GAlloc;

    type A = UnsafeLayoutBulkAlloc<GAlloc>;

    #[test]
    fn test_block_layout() {
        let check = |size, align| -> Layout {
            let layout = Layout::from_size_align(size, align).unwrap();
            let layout = A::block_layout(layout);

            assert!(size <= layout.size());
            assert!(size_of::<MemBlock>() <= layout.size());
            assert!(align <= layout.align());
            assert!(align_of::<MemBlock>() <= layout.align());

            let max_size = std::cmp::max(size, size_of::<MemBlock>());
            if max_size < layout.size() {
                assert!(layout.size() % layout.align() == 0);
                assert!(layout.size() - max_size < layout.align());
            }

            layout
        };

        for size in (1..64)
            .chain(MEMORY_CHUNK_SIZE / 2 - 16..MEMORY_CHUNK_SIZE / 2 + 16)
            .chain(MEMORY_CHUNK_SIZE - 16..MEMORY_CHUNK_SIZE + 16)
        {
            for align in [
                1,
                2,
                4,
                8,
                16,
                32,
                MEMORY_CHUNK_SIZE / 2,
                MEMORY_CHUNK_SIZE,
                2 * MEMORY_CHUNK_SIZE,
            ] {
                check(size, align);
            }
        }
    }
}
