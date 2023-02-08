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

use crate::rb_tree::{Color, Direction, TreeBucket};
use std::cmp::Ordering;
use std::ptr::NonNull;

type Link<T> = Option<NonNull<T>>;

struct Bucket {
    left_order: Link<Self>,
    right_order: Link<Self>,

    left_size: Link<Self>,
    right_size: Link<Self>,

    size: u16,
    order_color: Color,
    size_color: Color,
}

struct SizeBucket(Bucket);

impl SizeBucket {
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

impl PartialEq<Self> for OrderBucket {
    fn eq(&self, other: &Self) -> bool {
        self as *const Self == other
    }
}
