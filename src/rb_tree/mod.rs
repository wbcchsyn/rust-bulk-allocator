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

use std::cmp::Ordering;
use std::ptr::NonNull;

type Link<B> = Option<NonNull<B>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    Red,
    Black,
}

pub trait Bucket {
    fn init(&mut self) {
        self.set_left(None);
        self.set_right(None);
        self.set_color(Color::Red);
    }

    fn child(&self, direction: Direction) -> Link<Self>;
    fn set_child(&mut self, child: Link<Self>, direction: Direction);

    fn color(&self) -> Color;
    fn set_color(&mut self, color: Color);

    fn left(&self) -> Link<Self> {
        self.child(Direction::Left)
    }
    fn set_left(&mut self, child: Link<Self>) {
        self.set_child(child, Direction::Left)
    }

    fn right(&self) -> Link<Self> {
        self.child(Direction::Right)
    }
    fn set_right(&mut self, child: Link<Self>) {
        self.set_child(child, Direction::Right)
    }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Balance {
    Ok,
    Bad,
}

impl From<bool> for Balance {
    fn from(value: bool) -> Self {
        if value {
            Self::Ok
        } else {
            Self::Bad
        }
    }
}

pub struct RBTree<B> {
    root: Link<B>,
}

impl<B> RBTree<B> {
    pub fn new() -> Self {
        Self { root: None }
    }
}

impl<B> RBTree<B>
where
    B: Bucket,
{
    /// # Safety
    ///
    /// The caller must not update where the return value points to change the order.
    pub unsafe fn find<K>(&self, key: &K) -> Link<B>
    where
        B: PartialOrd<K>,
    {
        let mut it = self.root;

        while let Some(bucket) = it.map(|ptr| ptr.as_ref()) {
            match bucket.partial_cmp(key).unwrap() {
                Ordering::Less => it = bucket.right(),
                Ordering::Equal => return it,
                Ordering::Greater => it = bucket.left(),
            }
        }

        None
    }

    pub fn insert(&mut self, bucket: &mut B)
    where
        B: Ord,
    {
        bucket.init();

        match unsafe { self.root.map(|mut ptr| ptr.as_mut()) } {
            None => {
                bucket.set_color(Color::Black);
                self.root = NonNull::new(bucket);
            }
            Some(root) => {
                let d = if bucket < root {
                    Direction::Left
                } else {
                    Direction::Right
                };

                unsafe {
                    match root.child(d) {
                        None => root.set_child(NonNull::new(bucket), d),
                        Some(mut child) => {
                            let (new_root, _) =
                                Self::iter_insert(root, (child.as_mut(), d), bucket);
                            self.root = NonNull::new(new_root);
                            new_root.set_color(Color::Black);
                        }
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

        unsafe {
            match parent.0.child(d) {
                None => {
                    parent.0.set_child(NonNull::new(bucket), d);
                    match parent.0.color() {
                        Color::Black => (g_parent, None),
                        Color::Red => {
                            let new_parent = Self::insert_rotate(g_parent, parent, (bucket, d));
                            (new_parent, None)
                        }
                    }
                }
                Some(mut child) => {
                    let (new_parent, child) =
                        Self::iter_insert(parent.0, (child.as_mut(), d), bucket);
                    g_parent.set_child(NonNull::new(new_parent), parent.1);
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
            parent.0.set_child(NonNull::new(g_parent), d.alter());
            child.0.set_color(Color::Black);
            parent.0
        } else {
            g_parent.set_child(child.0.child(child.1), parent.1);
            parent.0.set_child(child.0.child(parent.1), child.1);
            child.0.set_child(NonNull::new(parent.0), parent.1);
            child.0.set_child(NonNull::new(g_parent), child.1);
            parent.0.set_color(Color::Black);
            child.0
        }
    }

    pub fn remove_lower_bound<K>(&mut self, key: &K) -> Link<B>
    where
        B: PartialOrd<K>,
    {
        unsafe {
            let root = self.root.map(|mut ptr| ptr.as_mut())?;

            let (new_root, ret, _) = Self::iter_remove(root, key, |ret| {
                if ret.1.is_none() && ret.0.unwrap().as_ref() > key {
                    let (new_root, ret, balance) = Self::remove_bucket(ret.0.unwrap().as_mut());
                    (new_root, Some(ret), balance)
                } else {
                    ret
                }
            });

            self.root = new_root;
            self.root
                .map(|mut root| root.as_mut().set_color(Color::Black));
            ret
        }
    }

    pub fn remove<K>(&mut self, key: &K) -> Link<B>
    where
        B: PartialOrd<K>,
    {
        unsafe {
            let root = self.root.map(|mut ptr| ptr.as_mut())?;
            let (new_root, ret, _) = Self::iter_remove(root, key, |ret| ret);

            self.root = new_root;
            self.root
                .map(|mut root| root.as_mut().set_color(Color::Black));

            ret
        }
    }

    /// Returns one arbitrary bucket removing it if not empty; otherwise, does nothing and returns `None`.
    ///
    /// This method always pops the min bucket for now.
    pub fn pop_one(&mut self) -> Link<B>
    where
        B: Ord,
    {
        unsafe {
            let mut root = self.root?;

            let (new_root, popped, _) = Self::pop_min(root.as_mut());
            new_root.map(|mut ptr| ptr.as_mut().set_color(Color::Black));
            self.root = new_root;

            Some(popped)
        }
    }

    unsafe fn iter_remove<K, F>(parent: &mut B, key: &K, f: F) -> (Link<B>, Link<B>, Balance)
    where
        B: PartialOrd<K>,
        F: Copy + Fn((Link<B>, Link<B>, Balance)) -> (Link<B>, Link<B>, Balance),
    {
        if (parent as &B) == key {
            let (new_parent, popped, balance) = Self::remove_bucket(parent);
            return (new_parent, Some(popped), balance);
        }

        let d = if (parent as &B) < key {
            Direction::Right
        } else {
            Direction::Left
        };

        let ret: (Link<B>, Link<B>, Balance) = match parent.child(d) {
            None => (NonNull::new(parent), None, Balance::Ok),
            Some(mut child) => {
                let (child, bucket, balance) = Self::iter_remove(child.as_mut(), key, f);
                parent.set_child(child, d);

                match balance {
                    Balance::Bad => {
                        let (parent, balance) = Self::remove_rotate(parent, (child, d));
                        (NonNull::new(parent), bucket, balance)
                    }
                    Balance::Ok => (NonNull::new(parent), bucket, Balance::Ok),
                }
            }
        };

        f(ret)
    }

    unsafe fn remove_bucket(bucket: &mut B) -> (Link<B>, NonNull<B>, Balance) {
        match bucket.right() {
            None => {
                let balance = Balance::from(bucket.color() == Color::Red);
                return (bucket.left(), NonNull::from(bucket), balance);
            }
            Some(mut right) => {
                let (new_right, mut new_bucket, balance) = Self::pop_min(right.as_mut());
                bucket.set_right(new_right);
                let new_bucket = new_bucket.as_mut();

                new_bucket.set_left(bucket.left());
                new_bucket.set_right(bucket.right());
                new_bucket.set_color(bucket.color());

                match balance {
                    Balance::Ok => (NonNull::new(new_bucket), NonNull::from(bucket), Balance::Ok),
                    Balance::Bad => {
                        let (new_bucket, balance) =
                            Self::remove_rotate(new_bucket, (Some(right), Direction::Right));
                        (NonNull::new(new_bucket), NonNull::from(bucket), balance)
                    }
                }
            }
        }
    }

    unsafe fn pop_min(parent: &mut B) -> (Link<B>, NonNull<B>, Balance) {
        match parent.left().as_mut() {
            None => {
                let balance = Balance::from(parent.color() == Color::Red);
                (parent.right(), NonNull::from(parent), balance)
            }
            Some(child) => {
                let (new_child, popped, balance) = Self::pop_min(child.as_mut());
                parent.set_left(new_child);

                match balance {
                    Balance::Ok => (NonNull::new(parent), popped, Balance::Ok),
                    Balance::Bad => {
                        let (new_parent, balance) =
                            Self::remove_rotate(parent, (new_child, Direction::Left));
                        (NonNull::new(new_parent), popped, balance)
                    }
                }
            }
        }
    }

    unsafe fn remove_rotate<'a>(
        parent: &'a mut B,
        lacking: (Link<B>, Direction),
    ) -> (&'a mut B, Balance) {
        let brother = {
            let d = lacking.1.alter();
            debug_assert_eq!(parent.child(d).is_none(), false);
            (parent.child(d).unwrap().as_mut(), d)
        };

        match brother.0.color() {
            Color::Red => {
                parent.set_child(brother.0.child(lacking.1), brother.1);
                brother.0.set_child(NonNull::new(parent), lacking.1);

                parent.set_color(Color::Red);
                brother.0.set_color(Color::Black);

                let (new_lacking, _balance) = Self::remove_rotate(parent, lacking);
                debug_assert_eq!(_balance, Balance::Ok);
                brother.0.set_child(NonNull::new(new_lacking), lacking.1);

                (brother.0, Balance::Ok)
            }
            Color::Black => {
                let straight_nephew = brother.0.child(brother.1);
                let alter_nephew = brother.0.child(lacking.1);

                if straight_nephew.map(|ptr| Bucket::color(ptr.as_ref())) == Some(Color::Red) {
                    parent.set_child(alter_nephew, brother.1);
                    brother.0.set_child(NonNull::new(parent), lacking.1);

                    straight_nephew.map(|mut ptr| ptr.as_mut().set_color(Color::Black));
                    brother.0.set_color(parent.color());
                    parent.set_color(Color::Black);

                    (brother.0, Balance::Ok)
                } else if alter_nephew.map(|ptr| Bucket::color(ptr.as_ref())) == Some(Color::Red) {
                    let nephew = alter_nephew.unwrap().as_mut();
                    parent.set_child(nephew.child(lacking.1), brother.1);
                    brother.0.set_child(nephew.child(brother.1), lacking.1);

                    nephew.set_child(NonNull::new(parent), lacking.1);
                    nephew.set_child(NonNull::new(brother.0), brother.1);

                    nephew.set_color(parent.color());
                    parent.set_color(Color::Black);

                    (nephew, Balance::Ok)
                } else {
                    let balance = (parent.color() == Color::Red).into();
                    parent.set_color(Color::Black);
                    brother.0.set_color(Color::Red);
                    (parent, balance)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cmp::Ordering;

    struct B {
        left_: Link<Self>,
        right_: Link<Self>,
        color_: Color,
        v: usize,
    }

    impl B {
        fn build(n: usize) -> Vec<B> {
            let mut ret: Vec<B> = Vec::with_capacity(n);

            unsafe {
                ret.set_len(n);
                (0..n).for_each(|i| ret[i].v = i);
            }

            ret
        }
    }

    impl Bucket for B {
        fn child(&self, direction: Direction) -> Link<Self> {
            match direction {
                Direction::Left => self.left_,
                Direction::Right => self.right_,
            }
        }
        fn set_child(&mut self, child: Link<Self>, direction: Direction) {
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

    impl PartialEq<usize> for B {
        fn eq(&self, other: &usize) -> bool {
            self.v == *other
        }
    }

    impl PartialOrd<usize> for B {
        fn partial_cmp(&self, other: &usize) -> Option<Ordering> {
            self.v.partial_cmp(other)
        }
    }

    fn check_tree(tree: &RBTree<B>) {
        unsafe {
            if tree.root.is_none() {
                return;
            }

            let root = tree.root.unwrap().as_ref();
            assert!(root.color() == Color::Black);

            check_black_count(root);
            check_not_red_red(root);
            check_order(root);
        }
    }

    unsafe fn check_black_count(b: &B) -> usize {
        let left = b.left().map_or(0, |ptr| check_black_count(ptr.as_ref()));
        let right = b.right().map_or(0, |ptr| check_black_count(ptr.as_ref()));

        assert_eq!(left, right);
        left + (b.color() == Color::Black) as usize
    }

    unsafe fn check_not_red_red(b: &B) {
        if let Some(left) = b.child(Direction::Left).map(|ptr| ptr.as_ref()) {
            if b.color() == Color::Red {
                assert_eq!(left.color(), Color::Black);
            }
            check_not_red_red(left);
        }
        if let Some(right) = b.child(Direction::Right).map(|ptr| ptr.as_ref()) {
            if b.color() == Color::Red {
                assert_eq!(right.color(), Color::Black);
            }
            check_not_red_red(right);
        }
    }

    unsafe fn check_order(b: &B) {
        if let Some(left) = b.child(Direction::Left).map(|ptr| ptr.as_ref()) {
            assert!(left <= b);
            check_order(left);
        }
        if let Some(right) = b.child(Direction::Right).map(|ptr| ptr.as_ref()) {
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

    #[test]
    fn test_remove_permutation() {
        const LEN: usize = 8;
        let mut insert_order: Vec<usize> = (0..LEN).collect();

        while {
            let mut remove_order: Vec<usize> = (0..LEN).collect();

            while {
                let mut tree = RBTree::new();
                let mut buckets = B::build(LEN);
                insert_order
                    .iter()
                    .for_each(|&i| tree.insert(&mut buckets[i]));

                for &i in remove_order.iter() {
                    let ptr = tree.remove(&i);
                    assert!(ptr == NonNull::new(&mut buckets[i]));

                    let ptr = tree.remove(&i);
                    assert!(ptr.is_none());

                    check_tree(&tree);
                }

                permutation_next(&mut remove_order)
            } {}

            permutation_next(&mut insert_order)
        } {}
    }

    #[test]
    fn test_insert_in_order_remove_in_order() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);
        buckets.iter_mut().for_each(|b| tree.insert(b));

        for i in 0..LEN {
            let ptr = tree.remove(&i);
            assert!(ptr == NonNull::new(&mut buckets[i]));

            let ptr = tree.remove(&i);
            assert!(ptr.is_none());

            check_tree(&tree);
        }
    }

    #[test]
    fn test_insert_in_order_remove_rev_order() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);
        buckets.iter_mut().for_each(|b| tree.insert(b));

        for i in (0..LEN).rev() {
            let ptr = tree.remove(&i);
            assert!(ptr == NonNull::new(&mut buckets[i]));

            let ptr = tree.remove(&i);
            assert!(ptr.is_none());

            check_tree(&tree);
        }
    }

    #[test]
    fn test_insert_in_order_remove_alternate_order() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);
        buckets.iter_mut().for_each(|b| tree.insert(b));

        let mut a = 0;
        let mut b = LEN - 1;
        while a < b {
            let ptr = tree.remove(&a);
            assert!(ptr == NonNull::new(&mut buckets[a]));

            let ptr = tree.remove(&a);
            assert!(ptr.is_none());

            check_tree(&tree);

            let ptr = tree.remove(&b);
            assert!(ptr == NonNull::new(&mut buckets[b]));

            let ptr = tree.remove(&b);
            assert!(ptr.is_none());

            check_tree(&tree);

            a += 1;
            b -= 1;
        }
    }

    #[test]
    fn test_insert_rev_order_remove_in_order() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);
        buckets.iter_mut().rev().for_each(|b| tree.insert(b));

        for i in 0..LEN {
            let ptr = tree.remove(&i);
            assert!(ptr == NonNull::new(&mut buckets[i]));

            let ptr = tree.remove(&i);
            assert!(ptr.is_none());

            check_tree(&tree);
        }
    }

    #[test]
    fn test_insert_rev_order_remove_rev_order() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);
        buckets.iter_mut().rev().for_each(|b| tree.insert(b));

        for i in (0..LEN).rev() {
            let ptr = tree.remove(&i);
            assert!(ptr == NonNull::new(&mut buckets[i]));

            let ptr = tree.remove(&i);
            assert!(ptr.is_none());

            check_tree(&tree);
        }
    }

    #[test]
    fn test_insert_rev_order_remove_alternate_order() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);
        buckets.iter_mut().rev().for_each(|b| tree.insert(b));

        let mut a = 0;
        let mut b = LEN - 1;
        while a < b {
            let ptr = tree.remove(&a);
            assert!(ptr == NonNull::new(&mut buckets[a]));

            let ptr = tree.remove(&a);
            assert!(ptr.is_none());

            check_tree(&tree);

            let ptr = tree.remove(&b);
            assert!(ptr == NonNull::new(&mut buckets[b]));

            let ptr = tree.remove(&b);
            assert!(ptr.is_none());

            check_tree(&tree);

            a += 1;
            b -= 1;
        }
    }

    #[test]
    fn test_insert_alternate_order_remove_in_order() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);

        let mut a = 0;
        let mut b = LEN - 1;
        while a < b {
            tree.insert(&mut buckets[a]);
            tree.insert(&mut buckets[b]);

            a += 1;
            b -= 1
        }

        for i in 0..LEN {
            let ptr = tree.remove(&i);
            assert!(ptr == NonNull::new(&mut buckets[i]));

            let ptr = tree.remove(&i);
            assert!(ptr.is_none());

            check_tree(&tree);
        }
    }

    #[test]
    fn test_insert_alternate_order_remove_rev_order() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);

        let mut a = 0;
        let mut b = LEN - 1;
        while a < b {
            tree.insert(&mut buckets[a]);
            tree.insert(&mut buckets[b]);

            a += 1;
            b -= 1;
        }

        for i in (0..LEN).rev() {
            let ptr = tree.remove(&i);
            assert!(ptr == NonNull::new(&mut buckets[i]));

            let ptr = tree.remove(&i);
            assert!(ptr.is_none());

            check_tree(&tree);
        }
    }

    #[test]
    fn test_insert_alternate_order_remove_alternative_order() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);

        let mut a = 0;
        let mut b = LEN - 1;
        while a < b {
            tree.insert(&mut buckets[a]);
            tree.insert(&mut buckets[b]);

            a += 1;
            b -= 1;
        }

        let mut a = 0;
        let mut b = LEN - 1;
        while a < b {
            let ptr = tree.remove(&a);
            assert!(ptr == NonNull::new(&mut buckets[a]));

            let ptr = tree.remove(&a);
            assert!(ptr.is_none());

            check_tree(&tree);

            let ptr = tree.remove(&b);
            assert!(ptr == NonNull::new(&mut buckets[b]));

            let ptr = tree.remove(&b);
            assert!(ptr.is_none());

            check_tree(&tree);

            a += 1;
            b -= 1;
        }
    }

    #[test]
    fn test_remove_lower_bound_permutation() {
        const LEN: usize = 12;
        let mut order: Vec<usize> = (0..LEN).collect();

        for i in 0..LEN {
            while {
                let mut tree = RBTree::new();
                let mut buckets = B::build(LEN);
                order.iter().for_each(|&i| tree.insert(&mut buckets[i]));

                for j in i..LEN {
                    let ptr = tree.remove_lower_bound(&i);
                    assert!(ptr == NonNull::new(&mut buckets[j]));
                    check_tree(&tree);
                }

                permutation_next(&mut order)
            } {}
        }
    }

    #[test]
    fn test_insert_in_order_remove_lower_bound() {
        const LEN: usize = 128;

        for i in 0..LEN {
            let mut tree = RBTree::new();
            let mut buckets = B::build(LEN);
            buckets.iter_mut().for_each(|b| tree.insert(b));

            for j in i..LEN {
                let ptr = tree.remove_lower_bound(&i);
                assert!(ptr == NonNull::new(&mut buckets[j]));
                check_tree(&tree);
            }
        }
    }

    #[test]
    fn test_insert_rev_order_remove_lower_bound() {
        const LEN: usize = 128;

        for i in 0..LEN {
            let mut tree = RBTree::new();
            let mut buckets = B::build(LEN);
            buckets.iter_mut().rev().for_each(|b| tree.insert(b));

            for j in i..LEN {
                let ptr = tree.remove_lower_bound(&i);
                assert!(ptr == NonNull::new(&mut buckets[j]));
                check_tree(&tree);
            }
        }
    }

    #[test]
    fn test_insert_alternate_order_remove_lower_bound() {
        const LEN: usize = 128;

        for i in 0..LEN {
            let mut tree = RBTree::new();
            let mut buckets = B::build(LEN);

            let mut a = 0;
            let mut b = LEN - 1;
            while a < b {
                tree.insert(&mut buckets[a]);
                tree.insert(&mut buckets[b]);

                a += 1;
                b -= 1;
            }

            for j in i..LEN {
                let ptr = tree.remove_lower_bound(&i);
                assert!(ptr == NonNull::new(&mut buckets[j]));
                check_tree(&tree);
            }
        }
    }

    #[test]
    fn test_permutation_find() {
        const LEN: usize = 12;
        let mut order: Vec<usize> = (0..LEN).collect();

        while {
            let mut tree = RBTree::new();
            let mut buckets = B::build(LEN);
            order.iter().for_each(|&i| tree.insert(&mut buckets[i]));

            for i in 0..LEN {
                let ptr = unsafe { tree.find(&i) };
                assert!(ptr == NonNull::new(&mut buckets[i]));
            }

            {
                let ptr = unsafe { tree.find(&LEN) };
                assert!(ptr.is_none());
            }

            permutation_next(&mut order)
        } {}
    }

    #[test]
    fn test_insert_in_order_find() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);
        buckets.iter_mut().for_each(|b| tree.insert(b));

        for i in 0..LEN {
            let ptr = unsafe { tree.find(&i) };
            assert!(ptr == NonNull::new(&mut buckets[i]));
        }

        {
            let ptr = unsafe { tree.find(&LEN) };
            assert!(ptr.is_none());
        }
    }

    #[test]
    fn test_insert_rev_order_find() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);
        buckets.iter_mut().rev().for_each(|b| tree.insert(b));

        for i in 0..LEN {
            let ptr = unsafe { tree.find(&i) };
            assert!(ptr == NonNull::new(&mut buckets[i]));
        }

        {
            let ptr = unsafe { tree.find(&LEN) };
            assert!(ptr.is_none());
        }
    }

    #[test]
    fn test_insert_alternate_find() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);

        let mut a = 0;
        let mut b = LEN - 1;
        while a < b {
            tree.insert(&mut buckets[a]);
            tree.insert(&mut buckets[b]);

            a += 1;
            b -= 1;
        }

        for i in 0..LEN {
            let ptr = unsafe { tree.find(&i) };
            assert!(ptr == NonNull::new(&mut buckets[i]));
        }

        {
            let ptr = unsafe { tree.find(&LEN) };
            assert!(ptr.is_none());
        }
    }

    #[test]
    fn test_insert_permutation_pop_one() {
        const LEN: usize = 12;
        let mut order: Vec<usize> = (0..LEN).collect();

        while {
            let mut tree = RBTree::new();
            let mut buckets = B::build(LEN);
            order.iter().for_each(|&i| tree.insert(&mut buckets[i]));

            for i in 0..LEN {
                let popped = tree.pop_one();
                check_tree(&tree);

                assert!(popped.is_some());

                let popped = popped.unwrap();
                assert!(popped == NonNull::from(&mut buckets[i]).cast());
            }

            assert!(tree.pop_one().is_none());

            permutation_next(&mut order)
        } {}
    }

    #[test]
    fn test_insert_in_order_pop_one() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);
        buckets.iter_mut().for_each(|b| tree.insert(b));

        for i in 0..LEN {
            let popped = tree.pop_one();
            check_tree(&tree);

            assert!(popped.is_some());

            let popped = popped.unwrap();
            assert!(popped == NonNull::from(&mut buckets[i]).cast());
        }

        assert!(tree.pop_one().is_none());
    }

    #[test]
    fn test_insert_rev_order_pop_one() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);
        buckets.iter_mut().rev().for_each(|b| tree.insert(b));

        for i in 0..LEN {
            let popped = tree.pop_one();
            check_tree(&tree);

            assert!(popped.is_some());

            let popped = popped.unwrap();
            assert!(popped == NonNull::from(&mut buckets[i]).cast());
        }

        assert!(tree.pop_one().is_none());
    }

    #[test]
    fn test_insert_alternate_pop_one() {
        const LEN: usize = 128;

        let mut tree = RBTree::new();
        let mut buckets = B::build(LEN);

        let mut a = 0;
        let mut b = LEN - 1;
        while a < b {
            tree.insert(&mut buckets[a]);
            tree.insert(&mut buckets[b]);

            a += 1;
            b -= 1;
        }

        for i in 0..LEN {
            let popped = tree.pop_one();
            check_tree(&tree);

            assert!(popped.is_some());

            let popped = popped.unwrap();
            assert!(popped == NonNull::from(&mut buckets[i]).cast());
        }

        assert!(tree.pop_one().is_none());
    }
}
