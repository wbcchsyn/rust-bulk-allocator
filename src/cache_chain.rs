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
use crate::split_memory_block;
use crate::MemoryBlock;
use crate::{MAX_CACHE_SIZE, MIN_CACHE_SIZE};
use core::alloc::Layout;
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
    fn iter(&self) -> CacheChainIter {
        CacheChainIter {
            index_: 0,
            size_: MIN_CACHE_SIZE as i32,
        }
    }

    pub fn find(&self, layout: Layout) -> Option<CacheChainIter> {
        let target = core::cmp::max(layout.size(), layout.align());
        self.iter().find(|x| target <= x.size())
    }

    pub fn fill_cache(&mut self, mut block: MemoryBlock) {
        let mut hint = self.iter();
        debug_assert!(is_fit(hint.layout(), block.to_slice()));

        let mut make_cache = |i: CacheChainIter, block: MemoryBlock| -> MemoryBlock {
            let (f, s) = split_memory_block(block.to_slice(), i.size());
            debug_assert!(is_fit(i.layout(), f));
            self.caches[i.index()].push(MemoryBlock::from(f).ptr);
            MemoryBlock::from(s)
        };

        // Increasing the hint and make cache
        while is_fit_size(hint.layout(), block.size) {
            while is_fit(hint.layout(), block.to_slice()) {
                hint.next();
                if hint.is_end() {
                    break;
                }
            }
            hint.next_back();
            block = make_cache(hint, block);
        }

        // Decreasing the hint and make cache
        while 0 < block.size {
            while !is_fit_size(hint.layout(), block.size) {
                hint.next_back();
                debug_assert!(!hint.is_end());
            }

            block = make_cache(hint, block);
        }
    }

    pub fn pop(&mut self, index: CacheChainIter) -> Option<MemoryBlock> {
        for mut it in index {
            match self.caches[it.index()].pop() {
                None => continue,
                Some(ptr) => {
                    let mut block = MemoryBlock {
                        ptr,
                        size: it.size(),
                    };

                    for _ in index.index()..it.index() {
                        it.next_back();
                        let (f, s) = split_memory_block(block.to_slice(), it.size());
                        debug_assert_eq!(f.len(), s.len());
                        self.caches[it.index()].push(MemoryBlock::from(f).ptr);
                        block = MemoryBlock::from(f);
                    }

                    debug_assert_eq!(index.size(), block.size);
                    return Some(block);
                }
            }
        }

        None
    }

    pub fn push(&mut self, ptr: NonNull<u8>, index: CacheChainIter) {
        self.caches[index.index()].push(ptr)
    }
}

fn is_fit_align<T>(layout: Layout, ptr: NonNull<T>) -> bool {
    let ptr = ptr.as_ptr() as usize;
    ptr % layout.align() == 0
}

fn is_fit_size(layout: Layout, size: usize) -> bool {
    layout.size() <= size
}

fn is_fit(layout: Layout, block: NonNull<[u8]>) -> bool {
    is_fit_size(layout, block.len()) && is_fit_align(layout, block.cast::<u8>())
}

#[derive(Copy, Clone, Eq, PartialEq, PartialOrd, Ord)]
pub struct CacheChainIter {
    index_: i32,
    size_: i32,
}

impl CacheChainIter {
    fn index(&self) -> usize {
        debug_assert!(0 <= self.index_);
        debug_assert!(self.index_ < (CHAIN_LENGTH) as i32);
        self.index_ as usize
    }

    fn size(&self) -> usize {
        debug_assert_eq!(1, self.size_.count_ones());
        debug_assert!((MIN_CACHE_SIZE as i32) <= self.size_);
        debug_assert!(self.size_ <= (MAX_CACHE_SIZE as i32));
        self.size_ as usize
    }

    fn is_end(&self) -> bool {
        self.index_ < 0 || (CHAIN_LENGTH as i32) <= self.index_
    }

    pub fn layout(&self) -> Layout {
        unsafe { Layout::from_size_align_unchecked(self.size(), self.size()) }
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
    fn find_works() {
        let chain = CacheChain::default();

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
        let chain = CacheChain::default();
        let err_check = |size, align| {
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

    mod fill_cache_tests {
        use super::*;

        fn allocate(size: usize, align: usize) -> MemoryBlock {
            let layout = Layout::from_size_align(size + align, 2 * align).unwrap();
            let ptr = unsafe { std::alloc::alloc(layout) };
            let ptr = (ptr as usize) + align;
            let ptr = NonNull::new(ptr as *mut u8).unwrap();

            MemoryBlock { ptr, size }
        }

        fn deallocate(block: MemoryBlock, size: usize, align: usize) {
            let layout = Layout::from_size_align(size + align, 2 * align).unwrap();
            let ptr = block.ptr.as_ptr() as usize;
            let ptr = (ptr - align) as *mut u8;
            unsafe {
                std::alloc::dealloc(ptr, layout);
            }
        }

        #[test]
        fn fill_one_cache() {
            let check = |i: CacheChainIter| {
                let block = allocate(i.size(), i.size());

                let mut chain = CacheChain::default();
                chain.fill_cache(block);

                for j in chain.iter() {
                    let ptr = chain.caches[j.index()].pop();
                    if i == j {
                        assert!(ptr.is_some());
                        assert!(is_fit_align(j.layout(), ptr.unwrap()));

                        let ptr = chain.caches[j.index()].pop();
                        assert!(ptr.is_none());
                    } else {
                        assert!(ptr.is_none());
                    }
                }

                deallocate(block, i.size(), i.size());
            };

            for i in CacheChain::default().iter() {
                check(i);
            }
        }

        #[test]
        fn fill_two_caches() {
            let check = |i: CacheChainIter, j: CacheChainIter| {
                let block = allocate(i.size() + j.size(), i.size());

                let mut chain = CacheChain::default();
                chain.fill_cache(block);

                for k in chain.iter() {
                    let ptr = chain.caches[k.index()].pop();

                    if (k == i) || (k == j) {
                        assert!(ptr.is_some());
                        assert!(is_fit_align(k.layout(), ptr.unwrap()));

                        let ptr = chain.caches[k.index()].pop();
                        if i == j {
                            assert!(ptr.is_some());
                            assert!(is_fit_align(k.layout(), ptr.unwrap()));
                        } else {
                            assert!(ptr.is_none());
                        }
                    } else {
                        assert!(ptr.is_none());
                    }
                }

                deallocate(block, i.size() + j.size(), i.size());
            };

            for i in CacheChain::default().iter() {
                check(i, i);

                let mut j = i;
                j.next();
                if j.is_end() {
                    break;
                }

                check(j, i);
                check(i, j);
            }
        }
    }
}
