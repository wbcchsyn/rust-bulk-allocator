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

use core::ptr::NonNull;

/// Forming forward linked list
pub struct PtrList {
    next: Option<NonNull<PtrList>>,
}

impl Default for PtrList {
    fn default() -> Self {
        Self { next: None }
    }
}

impl PtrList {
    pub fn pop(&mut self) -> Option<NonNull<Self>> {
        match self.next {
            None => None,
            Some(nonnull) => {
                unsafe {
                    self.next = nonnull.as_ref().next;
                }
                Some(nonnull)
            }
        }
    }

    pub fn push<T>(&mut self, ptr: NonNull<T>) {
        let mut ptr = ptr.cast::<Self>();

        unsafe {
            ptr.as_mut().next = self.next;
        }

        self.next = Some(ptr);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pop_and_push() {
        let mut head = PtrList::default();
        let mut fst = PtrList::default();
        let mut snd = PtrList::default();

        let fst = NonNull::new(&mut fst).unwrap();
        let snd = NonNull::new(&mut snd).unwrap();

        {
            debug_assert_eq!(None, head.pop());
        }

        {
            head.push(fst);
            debug_assert_eq!(Some(fst), head.pop());
            debug_assert_eq!(None, head.pop());
        }

        {
            head.push(fst);
            head.push(snd);
            debug_assert_eq!(Some(snd), head.pop());
            debug_assert_eq!(Some(fst), head.pop());
            debug_assert_eq!(None, head.pop());
        }
    }
}