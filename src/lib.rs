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

mod cache_chain;
mod ptr_list;

use crate::ptr_list::PtrList;
use core::alloc::Layout;
use core::mem::size_of;

/// The maximum memory size BulkAllocator::alloc() uses the cache.
pub const MAX_CACHE_SIZE: usize = 1024;
/// The minimum memory size BulkAllocator::alloc() returns.
pub const MIN_CACHE_SIZE: usize = size_of::<PtrList>();
/// Layout of memory chunk BulkAllocator acquires from the backend.
pub const MEMORY_CHUNK_LAYOUT: Layout =
    unsafe { Layout::from_size_align_unchecked(MAX_CACHE_SIZE * 8, MIN_CACHE_SIZE) };
