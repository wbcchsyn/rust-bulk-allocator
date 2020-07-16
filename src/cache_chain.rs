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

use crate::ptr_list::PtrList;
use crate::{MAX_CACHE_SIZE, MIN_CACHE_SIZE};

const CHAIN_LENGTH: usize =
    (MAX_CACHE_SIZE.trailing_zeros() - MIN_CACHE_SIZE.trailing_zeros() + 1) as usize;

/// Slice of PtrList
/// (Forms like 2 dimensions vector.)
pub struct CacheChain {
    caches: [PtrList; CHAIN_LENGTH],
}

impl Default for CacheChain {
    fn default() -> Self {
        Self {
            caches: Default::default(),
        }
    }
}

impl CacheChain {
    fn iter(&self) -> CacheChainIter {
        CacheChainIter {
            body: &self.caches,
            index_: 0,
            size_: MIN_CACHE_SIZE as i32,
        }
    }
}

#[derive(Copy, Clone)]
pub struct CacheChainIter<'a> {
    body: &'a [PtrList],
    index_: i32,
    size_: i32,
}

impl CacheChainIter<'_> {
    pub fn item(&self) -> &PtrList {
        &self.body[self.index()]
    }

    pub fn index(&self) -> usize {
        debug_assert!(0 <= self.index_);
        debug_assert!(self.index_ < (CHAIN_LENGTH) as i32);
        self.index_ as usize
    }

    pub fn size(&self) -> usize {
        debug_assert!((MIN_CACHE_SIZE as i32) <= self.size_);
        debug_assert!(self.size_ <= (MAX_CACHE_SIZE as i32));
        self.size_ as usize
    }
}

impl<'a> Iterator for CacheChainIter<'a> {
    type Item = Self;

    fn next(&mut self) -> Option<Self> {
        if (CHAIN_LENGTH as i32) <= self.index_ {
            None
        } else {
            let ret = *self;
            self.index_ += 1;
            self.size_ *= 2;
            Some(ret)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn iterator_count() {
        let chain = CacheChain::default();
        let count = chain.iter().count();
        assert_eq!(CHAIN_LENGTH, count);
    }

    #[test]
    fn iterator_last_item() {
        let chain = CacheChain::default();
        let last = chain.iter().last().unwrap();
        assert_eq!(CHAIN_LENGTH - 1, last.index());
        assert_eq!(MAX_CACHE_SIZE, last.size());
    }
}
