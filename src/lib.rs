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

#![feature(allocator_api, external_doc, slice_ptr_len)]
#![doc(include = "../README.md")]

mod backend;
mod bulk_allocator;
mod cache_chain;
mod layout_bulk_allocator;
mod ptr_list;

pub use crate::bulk_allocator::BulkAllocator;
pub use crate::layout_bulk_allocator::LayoutBulkAllocator;
use crate::ptr_list::PtrList;
use core::mem::size_of;
use core::ptr::NonNull;

/// The maximum memory size BulkAllocator::alloc() uses the cache.
pub const MAX_CACHE_SIZE: usize = 1024;
/// The minimum memory size BulkAllocator::alloc() returns.
const MIN_CACHE_SIZE: usize = size_of::<PtrList>();
/// Memory chunk size BulkAllocator allocate from the backend.
//
// This must equal to 2 * MAX_CACHE_SIZE or larger; otherwise BulkAllocator
// doesn't always make cache for MAX_CACHE_SIZE.
const MEMORY_CHUNK_SIZE: usize = 8 * MAX_CACHE_SIZE;

#[derive(Clone, Copy)]
struct MemoryBlock {
    ptr: NonNull<u8>,
    size: usize,
}

impl MemoryBlock {
    fn to_slice(self) -> NonNull<[u8]> {
        unsafe {
            let slice = core::slice::from_raw_parts(self.ptr.as_ptr(), self.size);
            From::from(slice)
        }
    }
}

impl From<NonNull<[u8]>> for MemoryBlock {
    fn from(ptr: NonNull<[u8]>) -> Self {
        let mut ptr = ptr;
        Self {
            ptr: unsafe { NonNull::new_unchecked(ptr.as_mut().as_mut_ptr()) },
            size: ptr.len(),
        }
    }
}

fn split_memory_block<T>(block: NonNull<[T]>, count: usize) -> (NonNull<[T]>, NonNull<[T]>) {
    debug_assert!(count <= block.len());

    unsafe {
        let fst = core::slice::from_raw_parts(block.as_ref().as_ptr(), count);
        let snd =
            core::slice::from_raw_parts(block.as_ref().as_ptr().add(count), block.len() - count);

        (From::from(fst), From::from(snd))
    }
}
