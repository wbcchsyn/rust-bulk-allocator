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

use std::ptr::null_mut;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    Red,
    Black,
}

pub trait Bucket {
    fn child(&self, direction: Direction) -> *mut Self;
    fn set_child(&mut self, child: *mut Self, direction: Direction);

    fn color(&self) -> Color;
    fn set_color(&mut self, color: Color);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    Left,
    Right,
}

impl Direction {
    pub fn alter(self) -> Self {
        match self {
            Self::Left => Self::Right,
            Self::Right => Self::Left,
        }
    }
}

pub struct RBTree<B> {
    root: *mut B,
}

impl<B> RBTree<B> {
    pub fn new() -> Self {
        Self { root: null_mut() }
    }
}

impl<B> RBTree<B>
where
    B: Bucket,
{
    pub fn insert(&mut self, bucket: &mut B)
    where
        B: Ord,
    {
        debug_assert!(bucket.color() == Color::Red);
        debug_assert!(bucket.child(Direction::Left) == null_mut());
        debug_assert!(bucket.child(Direction::Right) == null_mut());

        match unsafe { self.root.as_mut() } {
            None => {
                bucket.set_color(Color::Black);
                self.root = bucket;
            }
            Some(root) => {
                let d = if bucket < root {
                    Direction::Left
                } else {
                    Direction::Right
                };

                match unsafe { root.child(d).as_mut() } {
                    None => root.set_child(bucket, d),
                    Some(child) => {
                        let (new_root, _) = Self::iter_insert(root, (child, d), bucket);
                        self.root = new_root;
                        new_root.set_color(Color::Black);
                    }
                }
            }
        }
    }

    fn iter_insert<'a>(
        g_parent: &'a mut B,
        parent: (&'a mut B, Direction),
        bucket: &'a mut B,
    ) -> (&'a mut B, Option<(&'a mut B, Direction)>)
    where
        B: Ord,
    {
        let d = if bucket < parent.0 {
            Direction::Left
        } else {
            Direction::Right
        };

        match unsafe { parent.0.child(d).as_mut() } {
            None => {
                parent.0.set_child(bucket, d);
                match parent.0.color() {
                    Color::Black => (g_parent, None),
                    Color::Red => {
                        let new_parent = Self::insert_rotate(g_parent, parent, (bucket, d));
                        (new_parent, None)
                    }
                }
            }
            Some(child) => {
                let (new_parent, child) = Self::iter_insert(parent.0, (child, d), bucket);
                g_parent.set_child(new_parent, parent.1);
                let parent = (new_parent, parent.1);

                // If both parent and child are red, rotate.
                match child {
                    None => {
                        if g_parent.color() == Color::Red && parent.0.color() == Color::Red {
                            (g_parent, Some(parent))
                        } else {
                            (g_parent, None)
                        }
                    }
                    Some(child) => {
                        let g_parent = Self::insert_rotate(g_parent, parent, child);
                        (g_parent, None)
                    }
                }
            }
        }
    }

    fn insert_rotate<'a>(
        g_parent: &'a mut B,
        parent: (&'a mut B, Direction),
        child: (&'a mut B, Direction),
    ) -> &'a mut B {
        debug_assert_eq!(g_parent.color(), Color::Black);
        debug_assert_eq!(parent.0.color(), Color::Red);
        debug_assert_eq!(child.0.color(), Color::Red);

        if parent.1 == child.1 {
            let d = parent.1;
            g_parent.set_child(parent.0.child(d.alter()), d);
            parent.0.set_child(g_parent, d.alter());
            child.0.set_color(Color::Black);
            parent.0
        } else {
            g_parent.set_child(child.0.child(child.1), parent.1);
            parent.0.set_child(child.0.child(parent.1), child.1);
            child.0.set_child(parent.0, parent.1);
            child.0.set_child(g_parent, child.1);
            parent.0.set_color(Color::Black);
            child.0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cmp::Ordering;

    struct B {
        left_: *mut Self,
        right_: *mut Self,
        color_: Color,
        v: usize,
    }

    impl B {
        fn build(n: usize) -> Vec<B> {
            let mut ret: Vec<B> = Vec::with_capacity(n);

            unsafe {
                ret.set_len(n);

                for i in 0..n {
                    let b = &mut ret[i];
                    b.left_ = null_mut();
                    b.right_ = null_mut();
                    b.color_ = Color::Red;
                    b.v = i
                }
            }

            ret
        }
    }

    impl Bucket for B {
        fn child(&self, direction: Direction) -> *mut Self {
            match direction {
                Direction::Left => self.left_,
                Direction::Right => self.right_,
            }
        }
        fn set_child(&mut self, child: *mut Self, direction: Direction) {
            match direction {
                Direction::Left => self.left_ = child,
                Direction::Right => self.right_ = child,
            }
        }

        fn color(&self) -> Color {
            self.color_
        }
        fn set_color(&mut self, color: Color) {
            self.color_ = color
        }
    }

    impl PartialEq<B> for B {
        fn eq(&self, other: &B) -> bool {
            self.v == other.v
        }
    }

    impl Eq for B {}

    impl PartialOrd<B> for B {
        fn partial_cmp(&self, other: &B) -> Option<Ordering> {
            self.v.partial_cmp(&other.v)
        }
    }

    impl Ord for B {
        fn cmp(&self, other: &Self) -> Ordering {
            self.v.cmp(&other.v)
        }
    }

    fn check_tree(tree: &RBTree<B>) {
        unsafe {
            if tree.root.is_null() {
                return;
            }

            let root = &*tree.root;
            assert!(root.color() == Color::Black);

            check_black_count(root);
            check_not_red_red(root);
            check_order(root);
        }
    }

    unsafe fn check_black_count(b: &B) -> usize {
        let left = b
            .child(Direction::Left)
            .as_ref()
            .map_or(0, |c| check_black_count(c));
        let right = b
            .child(Direction::Right)
            .as_ref()
            .map_or(0, |c| check_black_count(c));

        assert_eq!(left, right);
        left + (b.color() == Color::Black) as usize
    }

    unsafe fn check_not_red_red(b: &B) {
        if let Some(left) = b.child(Direction::Left).as_ref() {
            if b.color() == Color::Red {
                assert_eq!(left.color(), Color::Black);
            }
            check_not_red_red(left);
        }
        if let Some(right) = b.child(Direction::Right).as_ref() {
            if b.color() == Color::Red {
                assert_eq!(right.color(), Color::Black);
            }
            check_not_red_red(right);
        }
    }

    unsafe fn check_order(b: &B) {
        if let Some(left) = b.child(Direction::Left).as_ref() {
            assert!(left <= b);
            check_order(left);
        }
        if let Some(right) = b.child(Direction::Right).as_ref() {
            assert!(b <= right);
            check_order(right);
        }
    }

    fn permutation_next(val: &mut [usize]) -> bool {
        for i in (1..val.len()).rev() {
            if val[i - 1] < val[i] {
                (val[i - 1], val[i]) = (val[i], val[i - 1]);
                val[(i + 1)..].reverse();
                return true;
            }
        }

        false
    }

    #[test]
    fn new() {
        RBTree::<usize>::new();
    }

    #[test]
    fn test_insert_permutation() {
        const LEN: usize = 12;
        let mut order: Vec<usize> = (0..LEN).collect();

        while {
            let mut tree = RBTree::new();
            let mut buckets = B::build(LEN);

            for &i in order.iter() {
                tree.insert(&mut buckets[i]);
                check_tree(&tree);
            }

            permutation_next(&mut order)
        } {}
    }

    #[test]
    fn test_insert_in_order() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);

        for b in buckets.iter_mut() {
            tree.insert(b);
            check_tree(&tree);
        }
    }

    #[test]
    fn test_insert_rev_order() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);

        for b in buckets.iter_mut().rev() {
            tree.insert(b);
            check_tree(&tree);
        }
    }

    #[test]
    fn test_insert_alternate_order() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);

        let mut a = 0;
        let mut b = LEN - 1;
        while a < b {
            tree.insert(&mut buckets[a]);
            check_tree(&tree);

            tree.insert(&mut buckets[b]);
            check_tree(&tree);

            a += 1;
            b -= 1;
        }
    }
}
