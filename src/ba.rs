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

use crate::{PtrList, MEMORY_CHUNK_SIZE};
use core::alloc::{GlobalAlloc, Layout};
use core::mem::{align_of, size_of};

/// Inner type of 'Ba' and 'Uba'.
pub struct Cache {
    to_free: PtrList,
    pools: [PtrList; Self::POOLS_LEN],
}

impl Cache {
    pub const MAX_CACHE_SIZE: usize = 4096; // 4 KB.
    pub const MIN_CACHE_SIZE: usize = size_of::<PtrList>();
    const POOLS_LEN: usize =
        (Self::MIN_CACHE_SIZE.leading_zeros() - Self::MAX_CACHE_SIZE.leading_zeros() + 1) as usize;
}

impl Drop for Cache {
    fn drop(&mut self) {
        // Make sure 'self.to_free' is empty.
        debug_assert_eq!(None, self.to_free.pop());
    }
}

impl Cache {
    /// Creates a new empty instance.
    pub const fn new() -> Self {
        Self {
            to_free: PtrList::new(),
            pools: [PtrList::new(); Self::POOLS_LEN],
        }
    }

    /// Deallocates all the allocated memory chunks and clears `self.to_free` .
    pub fn destroy<B>(&mut self, backend: &B)
    where
        B: GlobalAlloc,
    {
        let layout = Self::backend_layout();
        while let Some(ptr) = self.to_free.pop() {
            unsafe { backend.dealloc(ptr, layout) };
        }
    }

    const fn align() -> usize {
        // Same to usize::max(align_of::<PtrList>(), align_of::<u128>()).
        // (usize::max is not a const function.)
        if align_of::<PtrList>() < align_of::<u128>() {
            align_of::<u128>()
        } else {
            align_of::<PtrList>()
        }
    }

    const fn backend_layout() -> Layout {
        let size = MEMORY_CHUNK_SIZE;
        let align = Self::align();
        unsafe { Layout::from_size_align_unchecked(size, align) }
    }
}

#[cfg(test)]
mod cache_tests {
    use super::*;
    use gharial::GAlloc;

    #[test]
    fn new() {
        let backend = GAlloc::default();
        let mut cache = Cache::new();
        cache.destroy(&backend);
    }
}
