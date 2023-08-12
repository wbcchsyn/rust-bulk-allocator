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

#![deny(missing_docs)]

//! `bulk-allocator` provides implementations of [`GlobalAlloc`] that manage a memory cache.
//! The instance fetches memory chunks from the backend and frees them on the drop at once for
//! the performance.
//!
//! Method `dealloc` does not instantly free the specified pointer; instead, it pools the pointer
//! within the cache.
//!
//! Method `alloc` acquires a memory chunk from the backend and fill the cache if necessary, and
//! returns a requested pointer from the cache.
//!
//! It is when the instance is dropped that the memory chunks are deallocated.
//!
//! [`GlobalAlloc`]: std::alloc::GlobalAlloc

mod bulk_b;
mod layout_bulk_b;
mod rb_tree;

pub use bulk_b::BulkAlloc;
pub use layout_bulk_b::{LayoutBulkAlloc, UnsafeLayoutBulkAlloc};

/// The default byte count of the bulk memory that this crate allocates from the backend
/// if no cache is.
/// Note that if too large layout is requested, it may exceed this value that this crate
/// acquires via the backend.
pub const MEMORY_CHUNK_SIZE: usize = 16384; // 16 KB
