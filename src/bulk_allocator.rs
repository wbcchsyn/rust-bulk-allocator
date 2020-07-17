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
use core::alloc::AllocRef;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_constructor() {
        let _ = BulkAllocator::<'static, Global>::default();
    }

    #[test]
    fn move_constructor() {
        let global = Global::default();
        let _ = BulkAllocator::<'static, Global>::from(global);
    }
}
