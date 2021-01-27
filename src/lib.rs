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

#![deny(missing_docs)]

//! bulk-allocator is implementations for AllocRef.
//! They pool allocated memory and release them on the destruction.
//!
//! Method `dealloc` caches the released memory and `alloc` reuses it.
//! If no cache is left, `alloc` acquires a memory chunk from the backend and make cache at first.
//!
//! Using cache effectively, the performance is better compared to the same name functions in `std::alloc`.
//!
//! # Note
//!
//! Trait `AllocRef` is defined only in Rust nightly toolchain so far.
//! It is required to enable feathre `allocator_api` to use this crate and `AllocRef`.
//!
//! # Implementations
//!
//! ## BulkAllocator
//!
//! `AllocRef` method `alloc` and `dealloc` delegate the request to the backend if the argument `layout`
//! is too large to cache; otherwise, `dealloc` stores the released memory and `alloc` dispatches it and return.
//!
//! If the argument `layout` is always same, probably `LayoutBulkAllocator` is better.
//!
//! All methods in `AllocRef` are thread unsafe.
//!
//! ## LayoutBulkAllocator
//!
//! `LayoutBulkAllocator` behaves like `BulkAllocator` except for the constructor requires `Layout` as the argument.
//!
//! The instance uses cache only when the argument `layout` is same to what the constructor is passed; otherwise,
//! the requests are delegated to the backend.

mod ba;
mod ptr_list;
mod sba;

use ptr_list::PtrList;
pub use sba::{Sba, Usba};

/// The default byte count of bulk memory that this crate allocates from the backend if no cache
/// is.
/// Note that if too large layout is requested, the bulk size may exceed this value.
pub const MEMORY_CHUNK_SIZE: usize = 16384; // 16 KB
