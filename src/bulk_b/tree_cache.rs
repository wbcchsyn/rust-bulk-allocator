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

use crate::rb_tree::{Color, Direction, RBTree, TreeBucket};
use std::cmp::Ordering;
use std::mem::{align_of, size_of};
use std::ptr::NonNull;

type Link<T> = Option<NonNull<T>>;
const ALIGN: usize = align_of::<Bucket>();
pub const MIN_CACHE_SIZE: usize = size_of::<Bucket>();

struct Bucket {
    left_order: Link<Self>,
    right_order: Link<Self>,

    left_size: Link<Self>,
    right_size: Link<Self>,

    size: u16,
    order_color: Color,
    size_color: Color,
}

impl Bucket {}

struct SizeBucket(Bucket);

impl SizeBucket {
    pub fn init(ptr: NonNull<u8>, size: usize) {
        debug_assert!(size_of::<Self>() <= size);
        debug_assert!(size <= u16::MAX as usize);
        debug_assert!(size % ALIGN == 0);

        let this: &mut Self = unsafe { ptr.cast().as_mut() };
        this.0.size = size as u16;
    }

    pub fn size(&self) -> usize {
        self.0.size as usize
    }
}

impl PartialEq<Self> for SizeBucket {
    fn eq(&self, other: &Self) -> bool {
        let this: *const SizeBucket = self;
        this == other
    }
}

impl Eq for SizeBucket {}

impl PartialEq<usize> for SizeBucket {
    fn eq(&self, other: &usize) -> bool {
        self.size() == *other
    }
}

#[cfg(test)]
impl PartialEq<Bucket> for SizeBucket {
    fn eq(&self, other: &Bucket) -> bool {
        unsafe { self == std::mem::transmute::<&Bucket, &Self>(other) }
    }
}

impl PartialOrd<Self> for SizeBucket {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.0.size == other.0.size {
            let this: *const SizeBucket = self;
            let other: *const SizeBucket = other;
            this.partial_cmp(&other)
        } else {
            self.0.size.partial_cmp(&other.0.size)
        }
    }
}

impl Ord for SizeBucket {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.0.size == other.0.size {
            let this: *const SizeBucket = self;
            let other: *const SizeBucket = other;
            this.cmp(&other)
        } else {
            self.0.size.cmp(&other.0.size)
        }
    }
}

impl PartialOrd<usize> for SizeBucket {
    fn partial_cmp(&self, other: &usize) -> Option<Ordering> {
        self.size().partial_cmp(other)
    }
}

#[cfg(test)]
impl PartialOrd<Bucket> for SizeBucket {
    fn partial_cmp(&self, other: &Bucket) -> Option<Ordering> {
        unsafe { self.partial_cmp(std::mem::transmute::<&Bucket, &SizeBucket>(other)) }
    }
}

impl TreeBucket for SizeBucket {
    fn child(&self, direction: Direction) -> Link<Self> {
        match direction {
            Direction::Left => self.0.left_size.map(NonNull::cast),
            Direction::Right => self.0.right_size.map(NonNull::cast),
        }
    }

    fn set_child(&mut self, child: Link<Self>, direction: Direction) {
        match direction {
            Direction::Left => self.0.left_size = child.map(NonNull::cast),
            Direction::Right => self.0.right_size = child.map(NonNull::cast),
        }
    }

    fn color(&self) -> Color {
        self.0.size_color
    }

    fn set_color(&mut self, color: Color) {
        self.0.size_color = color
    }
}

struct OrderBucket(Bucket);

impl OrderBucket {
    pub fn init(ptr: NonNull<u8>, _size: usize) {
        debug_assert!(size_of::<Self>() <= _size);
        debug_assert!(_size <= u16::MAX as usize);
        debug_assert!(_size % ALIGN == 0);

        let _this: &mut Self = unsafe { ptr.cast().as_mut() };
        debug_assert!(_this.size() == _size);
    }

    pub fn size(&self) -> usize {
        self.0.size as usize
    }
}

impl PartialEq<Self> for OrderBucket {
    fn eq(&self, other: &Self) -> bool {
        self as *const Self == other
    }
}

impl PartialEq<NonNull<u8>> for OrderBucket {
    fn eq(&self, other: &NonNull<u8>) -> bool {
        let begin: *const u8 = (self as *const Self).cast();
        let end: *const u8 = unsafe { begin.add(self.size()) };
        let other: *const u8 = other.as_ptr();
        begin <= other && other < end
    }
}

#[cfg(test)]
impl PartialEq<Bucket> for OrderBucket {
    fn eq(&self, other: &Bucket) -> bool {
        unsafe { self == std::mem::transmute::<&Bucket, &Self>(other) }
    }
}

impl Eq for OrderBucket {}

impl PartialOrd<Self> for OrderBucket {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let this: *const Self = self;
        let other: *const Self = other;
        this.partial_cmp(&other)
    }
}

impl PartialOrd<NonNull<u8>> for OrderBucket {
    fn partial_cmp(&self, other: &NonNull<u8>) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else {
            let this: *const u8 = (self as *const Self).cast();
            let other: *const u8 = other.as_ptr();
            this.partial_cmp(&other)
        }
    }
}

#[cfg(test)]
impl PartialOrd<Bucket> for OrderBucket {
    fn partial_cmp(&self, other: &Bucket) -> Option<Ordering> {
        unsafe { self.partial_cmp(std::mem::transmute::<&Bucket, &OrderBucket>(other)) }
    }
}

impl Ord for OrderBucket {
    fn cmp(&self, other: &Self) -> Ordering {
        let this: *const Self = self;
        let other: *const Self = other;
        this.cmp(&other)
    }
}

impl TreeBucket for OrderBucket {
    fn child(&self, direction: Direction) -> Link<Self> {
        match direction {
            Direction::Left => self.0.left_order.map(NonNull::cast),
            Direction::Right => self.0.right_order.map(NonNull::cast),
        }
    }

    fn set_child(&mut self, child: Link<Self>, direction: Direction) {
        match direction {
            Direction::Left => self.0.left_order = child.map(NonNull::cast),
            Direction::Right => self.0.right_order = child.map(NonNull::cast),
        }
    }

    fn color(&self) -> Color {
        self.0.order_color
    }

    fn set_color(&mut self, color: Color) {
        self.0.order_color = color
    }
}

pub struct TreeCache {
    size_tree: RBTree<SizeBucket>,
    order_tree: RBTree<OrderBucket>,
}

impl TreeCache {
    pub const fn new() -> Self {
        Self {
            size_tree: RBTree::new(),
            order_tree: RBTree::new(),
        }
    }

    #[cfg(test)]
    pub fn is_empty(&self) -> bool {
        if self.size_tree.is_empty() {
            assert!(self.order_tree.is_empty());
            true
        } else {
            assert_eq!(self.order_tree.is_empty(), false);
            false
        }
    }

    pub fn alloc(&mut self, size: usize) -> Option<(NonNull<u8>, usize)> {
        debug_assert!(size % ALIGN == 0);
        debug_assert!(0 < size);

        unsafe {
            // Try to find a memory block from size_tree.
            let mut ptr = self.size_tree.remove_lower_bound(&size)?;
            let alloc_size = ptr.as_ref().size();

            // Take the end of ptr as a return value and cache again the rest
            // if the memory block is large enough.
            let rest_size = alloc_size - size;
            if size_of::<Bucket>() <= rest_size {
                // Store into size_tree again.
                let size_bucket = ptr.as_mut();
                SizeBucket::init(ptr.cast(), rest_size);
                self.size_tree.insert(size_bucket);

                // Do nothing for order_tree, because changing size does not matter to it.

                // Return
                let ret = ptr.as_ptr().cast::<u8>().add(rest_size);
                Some((NonNull::new_unchecked(ret), size))
            } else {
                // Return all of the memory block.
                let order_bucket: &mut OrderBucket = ptr.cast().as_mut();
                self.order_tree.remove(order_bucket);

                Some((ptr.cast(), alloc_size))
            }
        }
    }

    pub fn dealloc_without_merge(&mut self, ptr: NonNull<u8>, size: usize) -> bool {
        debug_assert!(ptr.as_ptr() as usize % ALIGN == 0);
        debug_assert!(size % ALIGN == 0);

        if size < size_of::<Bucket>() {
            false
        } else {
            unsafe {
                SizeBucket::init(ptr, size);
                self.size_tree.insert(ptr.cast().as_mut());

                OrderBucket::init(ptr, size);
                self.order_tree.insert(ptr.cast().as_mut());
            }

            true
        }
    }

    /// Does nothing and returns `false` if `layout` is too small to cache; otherwise, caches ptr
    /// and returns `true`.
    pub fn dealloc(&mut self, ptr: NonNull<u8>, size: usize) -> bool {
        debug_assert!(ptr.as_ptr() as usize % ALIGN == 0);
        debug_assert!(size % ALIGN == 0);

        // If the next memory block is cached, pop the block and merge to ptr.
        let size = unsafe {
            let next_ptr = NonNull::new_unchecked(ptr.as_ptr().add(size));
            match self.order_tree.remove(&next_ptr) {
                None => size,
                Some(ptr) => {
                    // The next block was cached.
                    // Remove from the size_tree as well.
                    let size_bucket: &SizeBucket = ptr.cast().as_ref();
                    self.size_tree.remove(size_bucket);

                    size + size_bucket.size()
                }
            }
        };

        // If the previous memory block is cached, enlarge the size to merge to ptr;
        // otherwise, store ptr into the cache.
        unsafe {
            let prev_ptr = NonNull::new_unchecked(ptr.as_ptr().offset(-1));
            match self.order_tree.find(&prev_ptr) {
                None => {
                    // Do nothing and return false if the size is too small.
                    if size < size_of::<Bucket>() {
                        return false;
                    }

                    SizeBucket::init(ptr, size);
                    self.size_tree.insert(ptr.cast().as_mut());

                    OrderBucket::init(ptr, size);
                    self.order_tree.insert(ptr.cast().as_mut());
                }
                Some(prev_ptr) => {
                    let order_bucket = prev_ptr.as_ref();
                    let size = size + order_bucket.size();

                    // Changeng size affect to the size_tree.
                    // Remove from size_tree, change the size, and insert into size_tree again.
                    let size_bucket: &mut SizeBucket = prev_ptr.cast().as_mut();
                    self.size_tree.remove(size_bucket);
                    SizeBucket::init(prev_ptr.cast(), size);
                    self.size_tree.insert(size_bucket);

                    // Do nothing for order_tree, because changing the size does not matter to it.
                }
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alloc() {
        let mut cache = TreeCache::new();

        // Make cache to prepare.
        type Block = [usize; 16];
        let mut blocks: Vec<Block> = Vec::with_capacity(1024);
        unsafe { blocks.set_len(1024) };
        for i in 0..blocks.len() {
            if i % 2 == 1 {
                continue;
            } else {
                let size = size_of::<Block>();
                let ptr = NonNull::from(&mut blocks[i]);
                cache.dealloc(ptr.cast(), size);
            }
        }

        // Test to allocate
        for _ in 0..8 {
            let mut pointers = Vec::new();

            for (_, size) in (0..512).zip((ALIGN..=size_of::<Block>()).cycle()) {
                let size = size - (size % ALIGN);
                let allocated = cache.alloc(size);

                assert!(allocated.is_some());

                let (ptr, s) = allocated.unwrap();
                assert!(ptr.as_ptr() as usize % ALIGN == 0);
                assert!(size <= s);
                assert!(s < size + size_of::<Bucket>());

                unsafe { ptr.as_ptr().write_bytes(0xff, s) };

                // Make sure cache works well.
                unsafe { ptr.as_ptr().write_bytes(0xff, s) };

                pointers.push((ptr, s));
            }

            for (ptr, size) in pointers {
                cache.dealloc(ptr, size);
            }
        }
    }

    #[test]
    fn test_alloc_fraction() {
        let mut buckets: Vec<Bucket> = Vec::with_capacity(3);
        unsafe { buckets.set_len(3) };

        // Cache 1 bucket, and allocate 1 byte.
        {
            let mut cache = TreeCache::new();

            // Cache 1 bucket
            {
                let ptr = NonNull::from(&mut buckets[0]);
                let size = size_of::<Bucket>();
                cache.dealloc(ptr.cast(), size);
            }

            // Alloc the minimum size
            {
                let size = ALIGN;
                let allocated = cache.alloc(size);

                assert!(allocated.is_some());

                let (ptr, s) = allocated.unwrap();
                assert!(size <= s);
                unsafe { ptr.as_ptr().write_bytes(0xff, s) };
            }

            // Make sure no cache is left.
            assert!(cache.is_empty());
        }

        // Cache a series of buckets, and allocate 1 byte and size_of::<Bucket>()
        {
            let mut cache = TreeCache::new();

            // Cache 2 buckets
            {
                let size = 2 * size_of::<Bucket>();
                let ptr = NonNull::from(&mut buckets[0]);
                cache.dealloc(ptr.cast(), size);
            }

            // Alloc the minimum bytes.
            {
                let size = ALIGN;
                let allocated = cache.alloc(size);

                assert!(allocated.is_some());

                let (ptr, s) = allocated.unwrap();
                assert!(size <= s);
                unsafe { ptr.as_ptr().write_bytes(0xff, s) };
            }

            // Alloc size_of::<Bucket>()
            {
                let size = size_of::<Bucket>();
                let allocated = cache.alloc(size);

                assert!(allocated.is_some());

                let (ptr, s) = allocated.unwrap();
                assert!(size <= s);
                unsafe { ptr.as_ptr().write_bytes(0xff, s) };
            }

            // Make sure no cache is left.
            assert!(cache.is_empty());
        }

        // Cache a series of buckets, and allocate size_of::<Bucket>() and 1 byte
        {
            let mut cache = TreeCache::new();

            // Cache 2 buckets
            {
                let size = 2 * size_of::<Bucket>();
                let ptr = NonNull::from(&mut buckets[0]);
                cache.dealloc(ptr.cast(), size);
            }

            // Alloc size_of::<Bucket>()
            {
                let size = size_of::<Bucket>();
                let allocated = cache.alloc(size);

                assert!(allocated.is_some());

                let (ptr, s) = allocated.unwrap();
                assert!(size <= s);
                unsafe { ptr.as_ptr().write_bytes(0xff, s) };
            }

            // Alloc the minimum bytes.
            {
                let size = ALIGN;
                let allocated = cache.alloc(size);

                assert!(allocated.is_some());

                let (ptr, s) = allocated.unwrap();
                assert!(size <= s);
                unsafe { ptr.as_ptr().write_bytes(0xff, s) };
            }

            // Make sure no cache is left.
            assert!(cache.is_empty());
        }

        // Cache a separated of buckets, and allocate 1 byte twice.
        {
            let mut cache = TreeCache::new();

            // Cache 2 buckets
            {
                let size = size_of::<Bucket>();
                let ptr = NonNull::from(&mut buckets[0]);
                cache.dealloc(ptr.cast(), size);

                let ptr = NonNull::from(&mut buckets[2]);
                cache.dealloc(ptr.cast(), size);
            }

            // Alloc the minimum bytes twice.
            for _ in 0..2 {
                let size = ALIGN;
                let allocated = cache.alloc(size);

                assert!(allocated.is_some());

                let (ptr, s) = allocated.unwrap();
                assert!(size <= s);
                unsafe { ptr.as_ptr().write_bytes(0xff, s) };
            }

            // Make sure no cache is left.
            assert!(cache.is_empty());
        }
    }

    #[test]
    fn test_dealloc_merge() {
        unsafe {
            let mut buckets: Vec<Bucket> = Vec::with_capacity(5);
            buckets.set_len(5);

            let mut cache = TreeCache::new();
            let size = size_of::<Bucket>();

            // dealloc the first block
            {
                cache.dealloc(NonNull::from(&mut buckets[0]).cast(), size);

                let size_ptr = cache.size_tree.find(&buckets[0]);
                assert!(size_ptr.is_some());
                assert!(size_ptr.unwrap().as_ref().size() == size_of::<Bucket>());

                let order_ptr = cache.order_tree.find(&buckets[0]);
                assert!(order_ptr.is_some());
                assert!(order_ptr.unwrap().as_ref().size() == size_of::<Bucket>());

                for i in 1..5 {
                    assert!(cache.size_tree.find(&buckets[i]).is_none());
                    assert!(cache.order_tree.find(&buckets[i]).is_none());
                }
            }

            // dealloc the last block
            {
                cache.dealloc(NonNull::from(&mut buckets[4]).cast(), size);

                let size_ptr = cache.size_tree.find(&buckets[0]);
                assert!(size_ptr.is_some());
                assert!(size_ptr.unwrap().as_ref().size() == size_of::<Bucket>());

                let order_ptr = cache.order_tree.find(&buckets[0]);
                assert!(order_ptr.is_some());
                assert!(order_ptr.unwrap().as_ref().size() == size_of::<Bucket>());

                let size_ptr = cache.size_tree.find(&buckets[4]);
                assert!(size_ptr.is_some());
                assert!(size_ptr.unwrap().as_ref().size() == size_of::<Bucket>());

                let order_ptr = cache.order_tree.find(&buckets[4]);
                assert!(order_ptr.is_some());
                assert!(order_ptr.unwrap().as_ref().size() == size_of::<Bucket>());

                for i in 1..4 {
                    assert!(cache.size_tree.find(&buckets[i]).is_none());
                    assert!(cache.order_tree.find(&buckets[i]).is_none());
                }
            }

            // dealloc the 2nd block
            // The 1st and the 2nd blocks are merged.
            {
                cache.dealloc(NonNull::from(&mut buckets[1]).cast(), size);

                let size_ptr = cache.size_tree.find(&buckets[0]);
                assert!(size_ptr.is_some());
                assert!(size_ptr.unwrap().as_ref().size() == 2 * size_of::<Bucket>());

                let order_ptr = cache.order_tree.find(&buckets[0]);
                assert!(order_ptr.is_some());
                assert!(order_ptr.unwrap().as_ref().size() == 2 * size_of::<Bucket>());

                let size_ptr = cache.size_tree.find(&buckets[4]);
                assert!(size_ptr.is_some());
                assert!(size_ptr.unwrap().as_ref().size() == size_of::<Bucket>());

                let order_ptr = cache.order_tree.find(&buckets[4]);
                assert!(order_ptr.is_some());
                assert!(order_ptr.unwrap().as_ref().size() == size_of::<Bucket>());

                for i in 2..4 {
                    assert!(cache.size_tree.find(&buckets[i]).is_none());
                    assert!(cache.order_tree.find(&buckets[i]).is_none());
                }
            }

            // dealloc the 4th block
            // The 4th and the last blocks are merged.
            {
                cache.dealloc(NonNull::from(&mut buckets[3]).cast(), size);

                let size_ptr = cache.size_tree.find(&buckets[0]);
                assert!(size_ptr.is_some());
                assert!(size_ptr.unwrap().as_ref().size() == 2 * size_of::<Bucket>());

                let order_ptr = cache.order_tree.find(&buckets[0]);
                assert!(order_ptr.is_some());
                assert!(order_ptr.unwrap().as_ref().size() == 2 * size_of::<Bucket>());

                let size_ptr = cache.size_tree.find(&buckets[3]);
                assert!(size_ptr.is_some());
                assert!(size_ptr.unwrap().as_ref().size() == 2 * size_of::<Bucket>());

                let order_ptr = cache.order_tree.find(&buckets[3]);
                assert!(order_ptr.is_some());
                assert!(order_ptr.unwrap().as_ref().size() == 2 * size_of::<Bucket>());

                for i in 2..3 {
                    assert!(cache.size_tree.find(&buckets[i]).is_none());
                    assert!(cache.order_tree.find(&buckets[i]).is_none());
                }
            }

            // dealloc the 3rd block
            // All the blocks are merged.
            {
                cache.dealloc(NonNull::from(&mut buckets[2]).cast(), size);

                let size_ptr = cache.size_tree.find(&buckets[0]);
                assert!(size_ptr.is_some());
                assert!(size_ptr.unwrap().as_ref().size() == 5 * size_of::<Bucket>());

                let order_ptr = cache.order_tree.find(&buckets[0]);
                assert!(order_ptr.is_some());
                assert!(order_ptr.unwrap().as_ref().size() == 5 * size_of::<Bucket>());

                for i in 1..5 {
                    assert!(cache.size_tree.find(&buckets[i]).is_none());
                    assert!(cache.order_tree.find(&buckets[i]).is_none());
                }
            }
        }
    }

    #[test]
    fn test_dealloc_small_merge() {
        unsafe {
            let mut buckets: Vec<Bucket> = Vec::with_capacity(3);
            buckets.set_len(3);

            let mut cache = TreeCache::new();
            let size = size_of::<Bucket>();

            // dealloc the 2nd block
            {
                assert!(cache.dealloc(NonNull::from(&mut buckets[1]).cast(), size));

                let size_ptr = cache.size_tree.find(&buckets[1]);
                assert!(size_ptr.is_some());
                assert!(size_ptr.unwrap().as_ref().size() == size_of::<Bucket>());

                let order_ptr = cache.order_tree.find(&buckets[1]);
                assert!(order_ptr.is_some());
                assert!(order_ptr.unwrap().as_ref().size() == size_of::<Bucket>());

                for i in [0, 2] {
                    assert!(cache.size_tree.find(&buckets[i]).is_none());
                    assert!(cache.order_tree.find(&buckets[i]).is_none());
                }
            }

            // Try to dealloc the first ALIGN bytes and fail.
            {
                assert!(cache.dealloc(NonNull::from(&mut buckets[0]).cast(), ALIGN) == false);

                for i in [0, 2] {
                    assert!(cache.size_tree.find(&buckets[i]).is_none());
                    assert!(cache.order_tree.find(&buckets[i]).is_none());
                }
            }

            // Dealloc the last ALIGN bytes of buckets[0]
            {
                let ptr: *mut u8 = (&mut buckets[1] as *mut Bucket).cast();
                let ptr = NonNull::new(ptr.offset(-1 * ALIGN as isize)).unwrap();
                assert!(cache.dealloc(ptr, ALIGN) == true);

                let size_ptr = cache.size_tree.find(&(size_of::<Bucket>() + ALIGN));
                assert!(size_ptr.is_some());
                assert!(size_ptr.unwrap().as_ref().size() == size_of::<Bucket>() + ALIGN);

                let order_ptr = cache.order_tree.find(&ptr);
                assert!(order_ptr.is_some());
                assert!(order_ptr.unwrap().as_ref().size() == size_of::<Bucket>() + ALIGN);

                for i in [0, 2] {
                    assert!(cache.size_tree.find(&buckets[i]).is_none());
                    assert!(cache.order_tree.find(&buckets[i]).is_none());
                }
            }

            // Dealloc the first ALIGN bytes of buckets[2]
            {
                assert!(cache.dealloc(NonNull::from(&mut buckets[2]).cast(), ALIGN) == true);

                let size_ptr = cache.size_tree.find(&(size_of::<Bucket>() + 2 * ALIGN));
                assert!(size_ptr.is_some());
                assert!(size_ptr.unwrap().as_ref().size() == size_of::<Bucket>() + 2 * ALIGN);

                let ptr: *mut u8 = (&mut buckets[1] as *mut Bucket).cast();
                let ptr = NonNull::new(ptr.offset(-1 * ALIGN as isize)).unwrap();
                let order_ptr = cache.order_tree.find(&ptr);
                assert!(order_ptr.is_some());
                assert!(order_ptr.unwrap().as_ref().size() == size_of::<Bucket>() + 2 * ALIGN);
            }
        }
    }
}
