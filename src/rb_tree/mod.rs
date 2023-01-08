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
    fn left(&self) -> *mut Self;
    fn set_left(&mut self, left: *mut Self);

    fn right(&self) -> *mut Self;
    fn set_right(&mut self, right: *mut Self);

    fn color(&self) -> Color;
    fn set_color(&mut self, color: Color);
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
    B: Ord + Bucket,
{
    pub fn insert(&mut self, bucket: &mut B) {
        debug_assert!(bucket.left().is_null());
        debug_assert!(bucket.right().is_null());
        debug_assert_eq!(bucket.color(), Color::Red);

        if self.root.is_null() {
            // This is the first element.
            self.root = bucket;
            bucket.set_color(Color::Black);
            return;
        }

        let parent = unsafe { &mut *self.root };
        unsafe { self.iter_insert(null_mut(), null_mut(), parent, bucket) };
    }

    // Returns `true` if the tree has already been balanced, or `false`, inserting `bucket` to `parent`.
    unsafe fn iter_insert(
        &mut self,
        gg_parent: *mut B,
        g_parent: *mut B,
        parent: &mut B,
        bucket: &mut B,
    ) -> bool {
        // Insert the bucket as a leaf
        let child: &mut B = if bucket < parent {
            match parent.left().as_mut() {
                None => {
                    parent.set_left(bucket);
                    bucket
                }
                Some(child) => {
                    if self.iter_insert(g_parent, parent, child, bucket) {
                        return true;
                    } else {
                        child
                    }
                }
            }
        } else {
            match parent.right().as_mut() {
                None => {
                    parent.set_right(bucket);
                    bucket
                }
                Some(child) => {
                    if self.iter_insert(g_parent, parent, child, bucket) {
                        return true;
                    } else {
                        child
                    }
                }
            }
        };

        if parent.color() == Color::Black {
            // If the parent is black, tree has already been balanced anyway.
            return true;
        } else if g_parent.is_null() {
            // If parent is the root, make sure parent black and return.
            parent.set_color(Color::Black);
            return true;
        }

        // Not balanced yet.
        // No bucket was rotated yet.

        if child.color() == Color::Black {
            // child and the brother were set black before.
            // Nothing should be done here, and the parent will be checked next.
            return false;
        }

        self.insert_balance(gg_parent.as_mut(), &mut *g_parent, parent, child)
    }

    fn insert_balance<'a>(
        &mut self,
        gg_parent: Option<&mut B>,
        g_parent: &mut B,
        mut parent: &'a mut B,
        mut child: &'a mut B,
    ) -> bool {
        debug_assert_eq!(g_parent.color(), Color::Black);
        debug_assert_eq!(parent.color(), Color::Red);
        debug_assert_eq!(child.color(), Color::Red);

        // If the uncle is red, make parent and uncle black, and g_parent red, and then continue the balancing.
        if let Some(uncle) = unsafe { Self::uncle(g_parent, parent).as_mut() } {
            if uncle.color() == Color::Red {
                g_parent.set_color(Color::Red);
                parent.set_color(Color::Black);
                uncle.set_color(Color::Black);

                return false;
            }
        }

        // Make sure both parent and child are the same direction.
        if parent.left() == child && g_parent.left() == parent {
            // Both parent and child are left.
            // Do nothing.
        } else if parent.right() == child && g_parent.right() == parent {
            // Both parent and child are right.
            // Do nothing.
        } else {
            self.rotate(Some(g_parent), parent, child);
            std::mem::swap(&mut parent, &mut child);
        }

        // Rotate g_parent and parent, and update the color.
        self.rotate(gg_parent, g_parent, parent);

        debug_assert_eq!(parent.color(), Color::Red);
        parent.set_color(Color::Black);

        debug_assert_eq!(g_parent.color(), Color::Black);
        g_parent.set_color(Color::Red);

        true
    }

    fn uncle(g_parent: &B, parent: &B) -> *mut B {
        if g_parent.left() as *const B == parent {
            g_parent.right()
        } else {
            debug_assert_eq!(parent as *const B, g_parent.right());
            g_parent.left()
        }
    }

    /// Make `parent` the child of `child`, and `child` the parent of `parent`.
    fn rotate(&mut self, g_parent: Option<&mut B>, parent: &mut B, child: &mut B) {
        // Link g_parent to child
        match g_parent {
            None => {
                self.root = child;
            }
            Some(g_parent) => {
                if child < g_parent {
                    g_parent.set_left(child);
                } else {
                    g_parent.set_right(child);
                }
            }
        }

        // Link child to parent, and parent to g_child.
        if parent.left() == child {
            let g_child = child.right();
            child.set_right(parent);
            parent.set_left(g_child);
        } else {
            debug_assert!(parent.right() == child);
            let g_child = child.left();
            child.set_left(parent);
            parent.set_right(g_child);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct B {
        left_: *mut Self,
        right_: *mut Self,
        color_: Color,
        v: usize,
    }

    impl Bucket for B {
        fn left(&self) -> *mut Self {
            self.left_
        }
        fn set_left(&mut self, left: *mut Self) {
            self.left_ = left;
        }

        fn right(&self) -> *mut Self {
            self.right_
        }
        fn set_right(&mut self, right: *mut Self) {
            self.right_ = right;
        }

        fn color(&self) -> Color {
            self.color_
        }
        fn set_color(&mut self, color: Color) {
            debug_assert!(color != self.color());
            self.color_ = color;
        }
    }

    impl PartialEq for B {
        fn eq(&self, other: &Self) -> bool {
            self.v == other.v
        }
    }
    impl Eq for B {}

    impl PartialOrd for B {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            self.v.partial_cmp(&other.v)
        }
    }

    impl Ord for B {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.v.cmp(&other.v)
        }
    }

    fn build_buckets(num: usize) -> Vec<B> {
        let mut ret: Vec<B> = Vec::with_capacity(num);
        unsafe {
            ret.set_len(num);
            ret.as_mut_ptr().write_bytes(0, num);
        }

        for i in 0..num {
            ret[i].color_ = Color::Red;
            ret[i].v = i;
        }

        ret
    }

    fn check_tree(tree: RBTree<B>) {
        if let Some(root) = unsafe { tree.root.as_ref() } {
            assert_eq!(root.color(), Color::Black);
            check_red_child(root);
            check_black_count(root);
            check_order(root);
        }
    }

    fn check_order(bucket: &B) {
        unsafe {
            if let Some(left) = bucket.left().as_ref() {
                assert!(left <= bucket);
                check_order(left);
            }
            if let Some(right) = bucket.right().as_ref() {
                assert!(bucket <= right);
                check_order(right);
            }
        }
    }

    fn check_red_child(bucket: &B) {
        let check_child = |c: &B| {
            if bucket.color() == Color::Red {
                assert_eq!(c.color(), Color::Black);
            }
            check_red_child(c);
        };

        if let Some(c) = unsafe { bucket.left().as_ref() } {
            check_child(c);
        }
        if let Some(c) = unsafe { bucket.right().as_ref() } {
            check_child(c);
        }
    }

    fn check_black_count(bucket: &B) -> usize {
        let left = unsafe { bucket.left().as_ref().map(check_black_count).unwrap_or(0) };
        let right = unsafe { bucket.right().as_ref().map(check_black_count).unwrap_or(0) };
        assert_eq!(left, right);

        (bucket.color() == Color::Black) as usize + left
    }

    #[test]
    fn new() {
        RBTree::<usize>::new();
    }

    #[test]
    fn insert_one() {
        let mut buckets = build_buckets(1);
        let mut tree = RBTree::new();

        tree.insert(&mut buckets[0]);
        assert!(tree.root == &mut buckets[0]);
        assert_eq!(buckets[0].color(), Color::Black);
    }

    #[test]
    fn insert_two() {
        // Insert 0, 1
        {
            let mut buckets = build_buckets(2);
            let mut tree = RBTree::new();

            tree.insert(&mut buckets[0]);
            tree.insert(&mut buckets[1]);

            assert!(tree.root == &mut buckets[0]);
            assert_eq!(buckets[0].color(), Color::Black);

            assert!(buckets[0].right() == &mut buckets[1]);
            assert_eq!(buckets[1].color(), Color::Red);
        }

        // Insert 1, 0
        {
            let mut buckets = build_buckets(2);
            let mut tree = RBTree::new();

            tree.insert(&mut buckets[1]);
            tree.insert(&mut buckets[0]);

            assert!(tree.root == &mut buckets[1]);
            assert_eq!(buckets[1].color(), Color::Black);

            assert!(buckets[1].left() == &mut buckets[0]);
            assert_eq!(buckets[0].color(), Color::Red);
        }
    }

    #[test]
    fn insert_red_uncle() {
        for i in [0, 2, 4, 6] {
            let mut buckets = build_buckets(7);
            let mut tree = RBTree::new();

            tree.insert(&mut buckets[3]);
            tree.insert(&mut buckets[1]);
            tree.insert(&mut buckets[5]);
            tree.insert(&mut buckets[i]);

            assert!(tree.root == &mut buckets[3]);
            assert_eq!(buckets[3].color(), Color::Black);
            assert!(buckets[3].left() == &mut buckets[1]);
            assert_eq!(buckets[1].color(), Color::Black);
            assert!(buckets[3].right() == &mut buckets[5]);
            assert_eq!(buckets[5].color(), Color::Black);

            match i {
                0 => assert!(buckets[1].left() == &mut buckets[0]),
                2 => assert!(buckets[1].right() == &mut buckets[2]),
                4 => assert!(buckets[5].left() == &mut buckets[4]),
                6 => assert!(buckets[5].right() == &mut buckets[6]),
                _ => unreachable!(),
            }

            assert_eq!(buckets[i].color(), Color::Red);
        }
    }

    #[test]
    fn insert_rotate_left_left() {
        let mut buckets = build_buckets(15);
        let mut tree = RBTree::new();

        tree.insert(&mut buckets[7]);
        tree.insert(&mut buckets[3]);
        tree.insert(&mut buckets[11]);
        tree.insert(&mut buckets[1]);

        tree.insert(&mut buckets[0]);

        assert!(tree.root == &mut buckets[7]);
        assert_eq!(buckets[7].color(), Color::Black);

        assert!(buckets[7].left() == &mut buckets[1]);
        assert_eq!(buckets[1].color(), Color::Black);
        assert!(buckets[1].left() == &mut buckets[0]);
        assert_eq!(buckets[0].color(), Color::Red);
        assert!(buckets[1].right() == &mut buckets[3]);
        assert_eq!(buckets[3].color(), Color::Red);

        assert!(buckets[7].right() == &mut buckets[11]);
        assert_eq!(buckets[11].color(), Color::Black);
    }

    #[test]
    fn insert_rotate_left_right() {
        let mut buckets = build_buckets(15);
        let mut tree = RBTree::new();

        tree.insert(&mut buckets[7]);
        tree.insert(&mut buckets[3]);
        tree.insert(&mut buckets[11]);
        tree.insert(&mut buckets[1]);

        tree.insert(&mut buckets[2]);

        assert!(tree.root == &mut buckets[7]);
        assert_eq!(buckets[7].color(), Color::Black);

        assert!(buckets[7].left() == &mut buckets[2]);
        assert_eq!(buckets[2].color(), Color::Black);
        assert!(buckets[2].left() == &mut buckets[1]);
        assert_eq!(buckets[1].color(), Color::Red);
        assert!(buckets[2].right() == &mut buckets[3]);
        assert_eq!(buckets[3].color(), Color::Red);

        assert!(buckets[7].right() == &mut buckets[11]);
        assert_eq!(buckets[11].color(), Color::Black);
    }

    #[test]
    fn insert_rotate_right_left() {
        let mut buckets = build_buckets(15);
        let mut tree = RBTree::new();

        tree.insert(&mut buckets[7]);
        tree.insert(&mut buckets[3]);
        tree.insert(&mut buckets[11]);
        tree.insert(&mut buckets[5]);

        tree.insert(&mut buckets[4]);

        assert!(tree.root == &mut buckets[7]);
        assert_eq!(buckets[7].color(), Color::Black);

        assert!(buckets[7].left() == &mut buckets[4]);
        assert_eq!(buckets[4].color(), Color::Black);
        assert!(buckets[4].left() == &mut buckets[3]);
        assert_eq!(buckets[3].color(), Color::Red);
        assert!(buckets[4].right() == &mut buckets[5]);
        assert_eq!(buckets[5].color(), Color::Red);

        assert!(buckets[7].right() == &mut buckets[11]);
        assert_eq!(buckets[11].color(), Color::Black);
    }

    #[test]
    fn insert_rotate_right_right() {
        let mut buckets = build_buckets(15);
        let mut tree = RBTree::new();

        tree.insert(&mut buckets[7]);
        tree.insert(&mut buckets[3]);
        tree.insert(&mut buckets[11]);
        tree.insert(&mut buckets[5]);

        tree.insert(&mut buckets[6]);

        assert!(tree.root == &mut buckets[7]);
        assert_eq!(buckets[7].color(), Color::Black);

        assert!(buckets[7].left() == &mut buckets[5]);
        assert_eq!(buckets[5].color(), Color::Black);
        assert!(buckets[5].left() == &mut buckets[3]);
        assert_eq!(buckets[3].color(), Color::Red);
        assert!(buckets[5].right() == &mut buckets[6]);
        assert_eq!(buckets[6].color(), Color::Red);

        assert!(buckets[7].right() == &mut buckets[11]);
        assert_eq!(buckets[11].color(), Color::Black);
    }

    #[test]
    fn insert_in_order() {
        let mut buckets = build_buckets(256);
        let mut tree = RBTree::new();

        for b in buckets.iter_mut() {
            tree.insert(b);
        }

        check_tree(tree);
    }

    #[test]
    fn insert_reverse_order() {
        let mut buckets = build_buckets(256);
        let mut tree = RBTree::new();

        for b in buckets.iter_mut().rev() {
            tree.insert(b);
        }

        check_tree(tree);
    }

    #[test]
    fn insert_alternate_order() {
        let mut buckets = build_buckets(256);
        let mut tree = RBTree::new();

        let mut a = 0;
        let mut b = 255;
        while a < b {
            tree.insert(&mut buckets[a]);
            tree.insert(&mut buckets[b]);
            tree.insert(&mut buckets[b - 1]);
            tree.insert(&mut buckets[a + 1]);

            a += 2;
            b -= 2;
        }

        check_tree(tree);
    }
}
