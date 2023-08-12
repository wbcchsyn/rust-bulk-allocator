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

use super::large_cache;
use std::ptr::{null_mut, NonNull};

type Link<T> = Option<NonNull<T>>;

const ALIGN: usize = super::ALIGN;
const MAX_CACHE_SIZE: usize = INNER_CACEH_SIZE * ALIGN;
const INNER_CACEH_SIZE: usize = (large_cache::MIN_CACHE_SIZE - 1) / ALIGN;

pub struct SmallCache([Link<u8>; INNER_CACEH_SIZE]);

impl SmallCache {
    pub const fn new() -> Self {
        Self([None; INNER_CACEH_SIZE])
    }

    pub fn alloc(&mut self, size: usize) -> Option<(NonNull<u8>, usize)> {
        debug_assert!(size % ALIGN == 0);

        if size == 0 {
            let ptr = NonNull::<Link<u8>>::dangling();
            Some((ptr.cast(), 0))
        } else {
            let index = (size / ALIGN) - 1;
            for i in index..INNER_CACEH_SIZE {
                if let Some(ptr) = self.0[i] {
                    self.0[i] = unsafe { NonNull::new(*ptr.cast().as_ref()) };
                    return Some((ptr, (i + 1) * ALIGN));
                }
            }

            None
        }
    }

    /// Does nothing and returns `false` if `size` is too large to cache; otherwise, caches ptr
    /// and returns `true`.
    pub fn dealloc(&mut self, ptr: NonNull<u8>, size: usize) -> bool {
        debug_assert!(ptr.as_ptr() as usize % ALIGN == 0);
        debug_assert!(size % ALIGN == 0);

        if MAX_CACHE_SIZE < size {
            return false;
        }
        if size == 0 {
            return true;
        }

        let index = (size / ALIGN) - 1;
        unsafe { *ptr.cast().as_mut() = self.0[index].map(NonNull::as_ptr).unwrap_or(null_mut()) };
        self.0[index] = Some(ptr);

        true
    }

    #[cfg(test)]
    pub fn is_empty(&self) -> bool {
        self.0.iter().all(Option::is_none)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alloc_dealloc() {
        const LEN: usize = 4096;

        let mut cache = SmallCache::new();

        unsafe {
            let mut buffer: Vec<usize> = Vec::with_capacity(LEN);
            buffer.set_len(LEN);

            // 1st deallocation
            let count = {
                let mut ptr = buffer.as_mut_ptr().cast::<u8>();
                let end = buffer.as_ptr().add(LEN).cast::<u8>();
                let mut count = 0;

                for size in (0..=MAX_CACHE_SIZE).step_by(ALIGN).cycle() {
                    if end < ptr.add(size) {
                        break;
                    }

                    cache.dealloc(NonNull::new(ptr).unwrap(), size);

                    count += 1;
                    ptr = ptr.add(size);
                }

                count
            };

            // Repeat allocation and deallocation
            for _ in 0..16 {
                let mut pointers = Vec::new();

                for size in (0..=MAX_CACHE_SIZE).step_by(ALIGN).cycle().take(count) {
                    let result = cache.alloc(size);
                    assert!(result.is_some());

                    let (ptr, s) = result.unwrap();
                    assert_eq!(s, size);

                    ptr.as_ptr().write_bytes(0xff, size);
                    pointers.push((ptr, size));
                }

                assert!(cache.is_empty());

                for (ptr, size) in pointers {
                    cache.dealloc(ptr, size);
                }
            }
        }
    }

    #[test]
    fn test_dealloc() {
        const LEN: usize = 1024;

        let mut cache = SmallCache::new();

        unsafe {
            let mut buffer: Vec<usize> = Vec::with_capacity(LEN);
            buffer.set_len(LEN);

            let mut ptr = buffer.as_mut_ptr().cast::<u8>();
            let end = buffer.as_ptr().add(LEN).cast::<u8>();

            for size in (0..=MAX_CACHE_SIZE).step_by(ALIGN).cycle() {
                if end < ptr.add(size) {
                    break;
                }

                cache.dealloc(NonNull::new(ptr).unwrap(), size);
                ptr = ptr.add(size);
            }
        }
    }
}
