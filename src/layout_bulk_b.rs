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

use crate::MemBlock;
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

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
