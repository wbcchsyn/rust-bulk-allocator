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
use core::alloc::{Layout, MemoryBlock};
use core::mem::size_of;
use core::ptr::NonNull;

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
    pub fn iter(&self) -> CacheChainIter {
        CacheChainIter {
            index_: 0,
            size_: MIN_CACHE_SIZE as i32,
        }
    }

    pub fn iter_mut(&mut self) -> CacheChainIterMut {
        CacheChainIterMut {
            item_: unsafe { NonNull::new_unchecked(&mut self.caches[0]) },
            index_: 0,
            size_: MIN_CACHE_SIZE as i32,
            _phantom: Default::default(),
        }
    }

    pub fn find(&self, layout: Layout) -> Option<CacheChainIter> {
        let target = core::cmp::max(layout.size(), layout.align());
        self.iter().find(|x| target <= x.size())
    }

    pub fn pop(&mut self, index: CacheChainIter) -> Option<MemoryBlock> {
        match self.caches[index.index()].pop() {
            None => None,
            Some(ptr) => Some(MemoryBlock {
                ptr: ptr.cast::<u8>(),
                size: index.size(),
            }),
        }
    }

    pub fn push(&mut self, ptr: NonNull<u8>, index: CacheChainIter) {
        self.caches[index.index()].push(ptr)
    }
}

#[derive(Copy, Clone)]
pub struct CacheChainIter {
    index_: i32,
    size_: i32,
}

impl CacheChainIter {
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

impl Iterator for CacheChainIter {
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

impl DoubleEndedIterator for CacheChainIter {
    fn next_back(&mut self) -> Option<Self> {
        if self.index_ < 0 {
            None
        } else {
            let ret = *self;
            self.index_ -= 1;
            debug_assert_eq!(0, self.size_ % 2);
            self.size_ /= 2;
            Some(ret)
        }
    }
}

#[derive(Copy, Clone)]
pub struct CacheChainIterMut<'a> {
    item_: NonNull<PtrList>,
    index_: i32,
    size_: i32,
    _phantom: std::marker::PhantomData<&'a PtrList>,
}

impl<'a> Iterator for CacheChainIterMut<'a> {
    type Item = Self;

    fn next(&mut self) -> Option<Self::Item> {
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

impl<'a> DoubleEndedIterator for CacheChainIterMut<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index_ < 0 {
            None
        } else {
            let ret = *self;
            self.index_ -= 1;
            debug_assert_eq!(0, self.size_ % 2);
            self.size_ /= 2;
            Some(ret)
        }
    }
}

impl CacheChainIterMut<'_> {
    pub fn item(&mut self) -> &mut PtrList {
        let ptr = (self.item_.as_ptr() as usize) + (size_of::<PtrList>() * self.index());
        unsafe { &mut *(ptr as *mut PtrList) }
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

    #[test]
    fn reverse_iterator_count() {
        let chain = CacheChain::default();
        let mut it = chain.iter();

        // Move to the end
        it.nth(CHAIN_LENGTH - 1);
        assert!(it.next().is_none());

        // Move to the last item
        it.next_back();

        let it = it.rev();
        assert_eq!(CHAIN_LENGTH, it.count());
    }

    #[test]
    fn reverse_iterator_last_item() {
        let chain = CacheChain::default();
        let last = chain.iter().rev().last().unwrap();

        assert_eq!(0, last.index());
        assert_eq!(MIN_CACHE_SIZE, last.size());
    }

    #[test]
    fn mut_iterator_count() {
        let mut chain = CacheChain::default();
        let count = chain.iter_mut().count();
        assert_eq!(CHAIN_LENGTH, count);
    }

    #[test]
    fn mut_iterator_last_item() {
        let mut chain = CacheChain::default();
        let last = chain.iter_mut().last().unwrap();
        assert_eq!(CHAIN_LENGTH - 1, last.index());
        assert_eq!(MAX_CACHE_SIZE, last.size());
    }

    #[test]
    fn reverse_mut_iterator_count() {
        let mut chain = CacheChain::default();
        let mut it = chain.iter_mut();

        // Move to the end
        it.nth(CHAIN_LENGTH - 1);
        assert!(it.next().is_none());

        // Move to the last item
        it.next_back();

        let it = it.rev();
        assert_eq!(CHAIN_LENGTH, it.count());
    }

    #[test]
    fn reverse_mut_iterator_last_item() {
        let mut chain = CacheChain::default();
        let last = chain.iter_mut().rev().last().unwrap();

        assert_eq!(0, last.index());
        assert_eq!(MIN_CACHE_SIZE, last.size());
    }

    #[test]
    fn find_works() {
        let mut chain = CacheChain::default();

        for s in &[1, 7, 8, 9, MAX_CACHE_SIZE - 1, MAX_CACHE_SIZE] {
            for a in &[2, 4, 8, MAX_CACHE_SIZE] {
                let layout = Layout::from_size_align(*s, *a).unwrap();
                let it = chain.find(layout).unwrap();

                assert!(*s <= it.size());
                assert!(*a <= it.size());
            }
        }
    }

    #[test]
    fn find_fails_too_large_layout() {
        let mut chain = CacheChain::default();
        let mut err_check = |size, align| {
            let layout = Layout::from_size_align(size, align).unwrap();
            let it = chain.find(layout);
            assert!(it.is_none());
        };

        for s in &[1, 7, 8, 9, 15, 16, 17, MAX_CACHE_SIZE, MAX_CACHE_SIZE + 1] {
            err_check(*s, 2 * MAX_CACHE_SIZE);
        }

        for a in &[2, 4, 8, 16, MAX_CACHE_SIZE, 2 * MAX_CACHE_SIZE] {
            err_check(MAX_CACHE_SIZE + 1, *a);
        }
    }
}
