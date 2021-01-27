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

/// Structure for `Sba` and `Usba` .
struct Cache {
    to_free: PtrList,
    pool: PtrList,
}

impl Drop for Cache {
    fn drop(&mut self) {
        // Make sure 'self.to_free' is empty.
        debug_assert_eq!(None, self.to_free.pop());
    }
}

impl Cache {
    /// Creates a new instance.
    pub const fn new() -> Self {
        Self {
            to_free: PtrList::new(),
            pool: PtrList::new(),
        }
    }

    /// Frees all the bulk memories via `backend`.
    pub fn destroy<B>(&mut self, layout: Layout, backend: &B)
    where
        B: GlobalAlloc,
    {
        let layout = Self::backend_layout(layout);
        while let Some(ptr) = self.to_free.pop() {
            debug_assert_eq!(false, ptr.is_null());
            unsafe { backend.dealloc(ptr, layout) };
        }
    }

    fn align(layout: Layout) -> usize {
        usize::max(layout.align(), align_of::<PtrList>())
    }

    fn element_layout(layout: Layout) -> Layout {
        let align = Self::align(layout);
        let size = usize::max(layout.size(), size_of::<PtrList>());
        let layout = unsafe { Layout::from_size_align_unchecked(size, align) };
        layout.pad_to_align()
    }

    fn to_free_layout(layout: Layout) -> Layout {
        let align = Self::align(layout);
        let size = size_of::<PtrList>();
        let layout = unsafe { Layout::from_size_align_unchecked(size, align) };
        layout.pad_to_align()
    }

    fn backend_layout(layout: Layout) -> Layout {
        let align = Self::align(layout);
        let min_size = Self::element_layout(layout).size() + Self::to_free_layout(layout).size();
        let size = usize::max(min_size, MEMORY_CHUNK_SIZE);
        unsafe { Layout::from_size_align_unchecked(size, align) }
    }
}

#[cfg(test)]
mod cache_tests {
    use super::*;
    use gharial::GAlloc;

    #[test]
    fn new() {
        let layout = Layout::new::<usize>();
        let backend = GAlloc::default();

        let mut cache = Cache::new();
        cache.destroy(layout, &backend);
    }
}
