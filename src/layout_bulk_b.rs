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

// TODO: Finish this module and replace into layout_bulk_a

use crate::MEMORY_CHUNK_SIZE;
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::mem::{align_of, size_of};
use std::ptr::{null_mut, NonNull};

type Link<T> = Option<NonNull<T>>;
type PointerList = Link<u8>;

/// `UnsafeLayoutBulkAlloc` is an implementation of `GlobalAlloc`.
///
/// Each instance owns cache for a specific layout, and releases all of them on the drop at once.
///
/// Method [`dealloc`] stores the passed pointer into the cache.
/// i.e. [`dealloc`] does not release the memory immediately.
/// It is when the object is dropped to free the memory.
///
/// Method [`alloc`] tries to search the cache at first, and returns the pointer if found;
/// otherwise, allocates a memory chunk via the backend, stores the chunk into the cache, and
/// dispatches a memory block from the cache.
///
/// To cache effectively, each instance assumes that the requested [`Layout`] is always same.
/// The behavior is undefined if a different [`Layout`] is passed to method [`alloc`] or
/// [`dealloc`]. (This is why named as `Unsafe`.)
///
/// # Warnings
///
/// Instance drop releases all the memory, and the all the pointers allocated via the instance
/// will be invalid after then. Accessing such a pointer may lead memory unsafety even if the
/// pointer itself is not deallocated.
///
/// # Safety
///
/// The behavior is undefined if the same instance is passed a different [`Layout`] as the
/// argument.
///
/// # Panics
///
/// Panics if different [`Layout`] is passed to method [`alloc`] or [`dealloc`] on debug mode.
///
/// [`Layout`]: std::alloc::Layout
/// [`alloc`]: #impl-GlobalAlloc-for-UnsafeLayoutBulkAlloc%3CB%3E
/// [`dealloc`]: #impl-GlobalAlloc-for-UnsafeLayoutBulkAlloc%3CB%3E
pub struct UnsafeLayoutBulkAlloc<B = System>
where
    B: GlobalAlloc,
{
    layout: Cell<Layout>, // Layout for u8 before initialized.
    to_free_list: Cell<PointerList>,
    cache: Cell<Link<MemBlock>>,
    backend: B,
}

impl<B> Drop for UnsafeLayoutBulkAlloc<B>
where
    B: GlobalAlloc,
{
    fn drop(&mut self) {
        let mut it = self.to_free_list.get();

        if it.is_none() {
            return;
        }

        debug_assert_eq!(self.is_initialized(), true);
        let layout = Self::chunk_layout(self.layout.get());
        let offset = -1 * (layout.size() - size_of::<PointerList>()) as isize;

        while let Some(ptr) = it {
            unsafe {
                it = NonNull::new(*ptr.cast().as_mut());
                self.backend.dealloc(ptr.as_ptr().offset(offset), layout);
            }
        }
    }
}

impl<B> Default for UnsafeLayoutBulkAlloc<B>
where
    B: GlobalAlloc + Default,
{
    fn default() -> Self {
        Self::new(B::default())
    }
}

unsafe impl<B> GlobalAlloc for UnsafeLayoutBulkAlloc<B>
where
    B: GlobalAlloc,
{
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if !self.is_initialized() {
            self.layout.set(Self::block_layout(layout));
        } else if self.layout.get() != Self::block_layout(layout) {
            panic!("Bad layout is passed to argument UnsafeLayoutBulkAlloc::alloc().");
        }
        self.do_alloc().map(NonNull::as_ptr).unwrap_or(null_mut())
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if self.layout.get() != Self::block_layout(layout) {
            panic!("Bad layout is passed to argument UnsafeLayoutBulkAlloc::dealloc().");
        }

        self.do_dealloc(NonNull::new_unchecked(ptr));
    }

    unsafe fn realloc(&self, _: *mut u8, _: Layout, _: usize) -> *mut u8 {
        panic!("Method UnsafeLayoutBulkAlloc::realloc() is called.");
    }
}

impl<B> UnsafeLayoutBulkAlloc<B>
where
    B: GlobalAlloc,
{
    /// Creates a new instance.
    pub const fn new(backend: B) -> Self {
        Self {
            layout: Cell::new(Layout::new::<u8>()),
            to_free_list: Cell::new(None),
            cache: Cell::new(None),
            backend,
        }
    }

    unsafe fn do_alloc(&self) -> Link<u8> {
        debug_assert!(self.is_initialized());
        let block_layout = self.layout.get();

        if self.cache.get().is_none() {
            // No memory is cached.
            // Acquire a memory chunk from backend and cache it at first.

            let chunk_layout = Self::chunk_layout(block_layout);
            let ptr = NonNull::new(self.backend.alloc(chunk_layout))?;

            // Take the end of the memory chunk as PointerList and append to self.to_free_list.
            {
                let offset = chunk_layout.size() - size_of::<PointerList>();
                let pointer_list = ptr.as_ptr().add(offset);
                *pointer_list.cast() = self
                    .to_free_list
                    .get()
                    .map(NonNull::as_ptr)
                    .unwrap_or(null_mut());
                self.to_free_list.set(NonNull::new(pointer_list));
            }

            // Cache the rest of memory chunk
            {
                debug_assert_eq!(ptr.as_ptr() as usize % align_of::<MemBlock>(), 0);
                let mut block = ptr.cast::<MemBlock>();

                let len = chunk_layout.size() - size_of::<PointerList>();
                debug_assert!(size_of::<MemBlock>() <= len);

                block.as_mut().next = None;
                block.as_mut().len = chunk_layout.size() - size_of::<PointerList>();

                self.cache.set(Some(block));
            }
        }

        let block = self.cache.get().unwrap();
        if 2 * block_layout.size() <= (block.as_ref()).len {
            // Push back the rest of memory block.
            let rest: *mut MemBlock = block.cast::<u8>().as_ptr().add(block_layout.size()).cast();

            debug_assert!(size_of::<MemBlock>() <= block.as_ref().len - block_layout.size());
            debug_assert_eq!(rest as usize % align_of::<MemBlock>(), 0);

            (*rest).next = block.as_ref().next;
            (*rest).len = block.as_ref().len - block_layout.size();
            self.cache.set(NonNull::new(rest));
        } else {
            self.cache.set(block.as_ref().next);
        }

        Some(block.cast())
    }

    unsafe fn do_dealloc(&self, ptr: NonNull<u8>) {
        debug_assert!(self.is_initialized());

        let layout = self.layout.get();
        let block: &mut MemBlock = ptr.cast().as_mut();
        block.next = self.cache.get();
        block.len = layout.size();
        self.cache.set(Some(block.into()));
    }

    fn is_initialized(&self) -> bool {
        self.layout.get() != Layout::new::<u8>()
    }

    /// Calculates the layout that method alloc() returns.    
    fn block_layout(layout: Layout) -> Layout {
        let size = std::cmp::max(layout.size(), size_of::<MemBlock>());
        let align = std::cmp::max(layout.align(), align_of::<MemBlock>());

        let not_padded = unsafe { Layout::from_size_align_unchecked(size, align) };
        let padded = not_padded.pad_to_align();

        if MEMORY_CHUNK_SIZE < 2 * padded.size() + size_of::<PointerList>() {
            not_padded
        } else {
            padded
        }
    }

    /// Calculate the layout to allocate chunk memory from backend.
    fn chunk_layout(block_layout: Layout) -> Layout {
        debug_assert!(size_of::<MemBlock>() <= block_layout.size());
        debug_assert!(align_of::<MemBlock>() <= block_layout.align());

        if (0 < block_layout.size() % block_layout.align())
            || (MEMORY_CHUNK_SIZE < 2 * block_layout.size() + size_of::<PointerList>())
        {
            // Not padded.
            let size = unsafe {
                Layout::from_size_align_unchecked(
                    block_layout.size() + size_of::<PointerList>(),
                    align_of::<PointerList>(),
                )
                .pad_to_align()
                .size()
            };
            let align = block_layout.align();

            let ret = unsafe { Layout::from_size_align_unchecked(size, align) };
            debug_assert!(ret.size() % align_of::<PointerList>() == 0);
            ret
        } else {
            let size = MEMORY_CHUNK_SIZE;
            let align = block_layout.align();
            unsafe { Layout::from_size_align_unchecked(size, align) }
        }
    }
}

#[cfg(test)]
mod unsafe_layout_bulk_alloc_tests {
    use super::*;
    use gharial::GAlloc;

    type A = UnsafeLayoutBulkAlloc<GAlloc>;

    #[test]
    fn test_new() {
        let backend = GAlloc::default();
        let _ = A::new(backend);
    }

    #[test]
    fn test_block_layout() {
        let check = |size, align| -> Layout {
            let layout = Layout::from_size_align(size, align).unwrap();
            let layout = A::block_layout(layout);

            assert!(size <= layout.size());
            assert!(size_of::<MemBlock>() <= layout.size());
            assert!(align <= layout.align());
            assert!(align_of::<MemBlock>() <= layout.align());

            let max_size = std::cmp::max(size, size_of::<MemBlock>());
            if max_size < layout.size() {
                assert!(layout.size() % layout.align() == 0);
                assert!(layout.size() - max_size < layout.align());
            }

            layout
        };

        for size in (1..64)
            .chain(MEMORY_CHUNK_SIZE / 2 - 16..MEMORY_CHUNK_SIZE / 2 + 16)
            .chain(MEMORY_CHUNK_SIZE - 16..MEMORY_CHUNK_SIZE + 16)
        {
            for align in [
                1,
                2,
                4,
                8,
                16,
                32,
                MEMORY_CHUNK_SIZE / 2,
                MEMORY_CHUNK_SIZE,
                2 * MEMORY_CHUNK_SIZE,
            ] {
                check(size, align);
            }
        }
    }

    #[test]
    fn test_chunk_layout() {
        let check = |size, align| -> Layout {
            let layout = Layout::from_size_align(size, align).unwrap();
            let block_layout = A::block_layout(layout);
            let chunk_layout = A::chunk_layout(block_layout);

            assert!(size + size_of::<PointerList>() <= chunk_layout.size());
            assert!(size_of::<MemBlock>() + size_of::<PointerList>() <= chunk_layout.size());

            assert!(align <= chunk_layout.align());
            assert!(align_of::<MemBlock>() <= chunk_layout.align());
            assert!(chunk_layout.size() % align_of::<PointerList>() == 0);

            if chunk_layout.size() != MEMORY_CHUNK_SIZE {
                assert_eq!(
                    (block_layout.size() + size_of::<PointerList>() + align_of::<PointerList>()
                        - 1)
                        / align_of::<PointerList>(),
                    chunk_layout.size() / align_of::<PointerList>()
                );

                let padded = chunk_layout.pad_to_align();
                assert!(MEMORY_CHUNK_SIZE < 2 * padded.size() + size_of::<PointerList>());
            }

            chunk_layout
        };

        for size in (1..64)
            .chain(MEMORY_CHUNK_SIZE / 2 - 16..MEMORY_CHUNK_SIZE / 2 + 16)
            .chain(MEMORY_CHUNK_SIZE - 16..MEMORY_CHUNK_SIZE + 16)
        {
            for align in [
                1,
                2,
                4,
                8,
                16,
                32,
                MEMORY_CHUNK_SIZE / 2,
                MEMORY_CHUNK_SIZE,
                2 * MEMORY_CHUNK_SIZE,
            ] {
                check(size, align);
            }
        }
    }

    #[test]
    fn test_alloc() {
        let backend = GAlloc::default();

        for size in (1..64)
            .chain(MEMORY_CHUNK_SIZE / 2 - 16..MEMORY_CHUNK_SIZE / 2 + 16)
            .chain(MEMORY_CHUNK_SIZE - 16..MEMORY_CHUNK_SIZE + 16)
        {
            for align in [
                1,
                2,
                4,
                8,
                16,
                32,
                MEMORY_CHUNK_SIZE / 2,
                MEMORY_CHUNK_SIZE,
                2 * MEMORY_CHUNK_SIZE,
            ] {
                let layout = Layout::from_size_align(size, align).unwrap();
                let alloc = A::new(backend.clone());

                let blocks_in_chunk = {
                    let block_layout = A::block_layout(layout);
                    let chunk_layout = A::chunk_layout(block_layout);
                    let blocks_in_chunk =
                        (chunk_layout.size() - size_of::<PointerList>()) / block_layout.size();
                    assert!(0 < blocks_in_chunk);
                    blocks_in_chunk
                };

                unsafe {
                    let mut pointers = Vec::new();
                    for _ in 0..blocks_in_chunk {
                        let ptr = alloc.alloc(layout);
                        assert_eq!(ptr.is_null(), false);
                        pointers.push(ptr);
                    }

                    assert_eq!(backend.providing_pointers().len(), 1);

                    for ptr in pointers {
                        alloc.dealloc(ptr, layout);
                    }

                    let mut pointers = Vec::new();
                    for _ in 0..blocks_in_chunk {
                        let ptr = alloc.alloc(layout);
                        assert_eq!(ptr.is_null(), false);
                        pointers.push(ptr);
                    }
                    assert_eq!(backend.providing_pointers().len(), 1);

                    {
                        let ptr = alloc.alloc(layout);
                        assert_eq!(ptr.is_null(), false);
                        pointers.push(ptr);
                    }
                    assert_eq!(backend.providing_pointers().len(), 2);

                    for ptr in pointers {
                        alloc.dealloc(ptr, layout);
                    }
                }
            }
        }
    }

    #[test]
    fn test_alloc_and_use() {
        let backend = GAlloc::default();

        unsafe {
            let alloc = A::new(backend.clone());
            let layout = Layout::new::<u8>();
            let mut pointers = Vec::new();

            for i in (0..=255).cycle().take(65535) {
                let ptr = alloc.alloc(layout);
                *ptr = i;
                pointers.push(ptr);
            }

            for i in 0..65535 {
                let ptr = pointers[i];
                assert_eq!(*ptr, i as u8);
                alloc.dealloc(ptr, layout);
            }
        }

        unsafe {
            let alloc = A::new(backend.clone());
            let layout = Layout::new::<u128>();
            let mut pointers = Vec::new();

            for i in 0..65535 {
                let ptr = alloc.alloc(layout);
                *(ptr.cast::<u128>()) = i;
                pointers.push(ptr);
            }

            for i in 0..65535 {
                let ptr = pointers[i as usize];
                assert_eq!(*(ptr.cast::<u128>()), i);
                alloc.dealloc(ptr, layout);
            }
        }
    }
}

/// `LayoutBulkAlloc` is an implementation of `GlobalAlloc`.
///
/// This struct owns a cache for memory block.
/// Method [`alloc`] checks whether the required `layout` fits to the cache or not.
///
/// If the `layout` fits to the cache, [`alloc`] dispatches a memory block from the cache.
/// (If the cache was empty, it allocates a memory chunk from the backend and make cache at first.)
/// Otherwise, i.e. the `layout` does not fit to the cache, delegating the request to the backend.
///
/// Method [`dealloc`] caches the passed pointer if possible; otherwise, delegate the request to
/// the backend. It is when the instance is dropped to free the cached memory.
///
/// Instance drop releases all the cached memory. All the pointers allocated via the instance will
/// be invalid after then. Accessing such a pointer may lead memory unsafety even if the pointer
/// itself is not deallocated.
///
/// # Warnings
///
/// The allocated pointers via `LayoutBulkAlloc` will be invalid after the instance is
/// dropped. Accessing such a pointer may lead memory unsafety evenn if the pointer itself is
/// not deallocated.
///
/// [`alloc`]: #impl-GlobalAlloc-for-LayoutBulkAlloc<B>
/// [`dealloc`]: #impl-GlobalAlloc-for-LayoutBulkAlloc<B>

/// `LayoutBulkAlloc` is an implementation of `GlobalAlloc`.
///
/// The constractor takes a [`Layout`] as the argument, and each instance owns cache for the
/// layout.
///
/// Method [`dealloc`] checks whether the passed [`Layout`] matches that passed to the constructor
/// or not.
/// If they are different, [`dealloc`] delegates the request to the backend; otherwise, it stores
/// the pointer into the cache. i.e. [`dealloc`] does not release the memory immediately.
/// It is when the object is dropped to free the cached memory.
///
/// Method [`alloc`] checks whether the passed [`Layout`] matches that passed to the constructor
/// or not.
/// If they are different, [`alloc`] delegates the request to the backend; otherwise, it tries
/// to search the cache at first, and returns the pointer if found, or allocates a memory chunk
/// via the backend, stores the chunk into the cache, and dispatches a memory block from the cache.
///
/// # Warnings
///
/// Instance drop releases all the memory, and the all the pointers allocated via the instance
/// will be invalid after then. Accessing such a pointer may lead memory unsafety even if the
/// pointer itself is not deallocated.
///
/// [`Layout`]: std::alloc::Layout
/// [`alloc`]: #impl-GlobalAlloc-for-LayoutBulkAlloc%3CB%3E
/// [`dealloc`]: #impl-GlobalAlloc-for-LayoutBulkAlloc%3CB%3E
pub struct LayoutBulkAlloc<B = System>
where
    B: GlobalAlloc,
{
    backend: UnsafeLayoutBulkAlloc<B>,
}

unsafe impl<B> GlobalAlloc for LayoutBulkAlloc<B>
where
    B: GlobalAlloc,
{
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if UnsafeLayoutBulkAlloc::<B>::block_layout(layout) == self.backend.layout.get() {
            self.backend
                .do_alloc()
                .map(NonNull::as_ptr)
                .unwrap_or(null_mut())
        } else {
            self.backend.backend.alloc(layout)
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if UnsafeLayoutBulkAlloc::<B>::block_layout(layout) == self.backend.layout.get() {
            self.backend.do_dealloc(NonNull::new_unchecked(ptr))
        } else {
            self.backend.backend.dealloc(ptr, layout)
        }
    }
}

impl<B> LayoutBulkAlloc<B>
where
    B: GlobalAlloc,
{
    /// Creates a new instance.
    pub fn new(layout: Layout, backend: B) -> Self {
        let backend = UnsafeLayoutBulkAlloc::<B>::new(backend);
        let layout = UnsafeLayoutBulkAlloc::<B>::block_layout(layout);
        backend.layout.set(layout);

        Self { backend }
    }
}

#[cfg(test)]
mod layout_bulk_alloc_tests {
    use super::*;
    use gharial::GAlloc;

    type A = LayoutBulkAlloc<GAlloc>;

    #[test]
    fn test_new() {
        for size in (1..64)
            .chain(MEMORY_CHUNK_SIZE / 2 - 16..MEMORY_CHUNK_SIZE / 2 + 16)
            .chain(MEMORY_CHUNK_SIZE - 16..MEMORY_CHUNK_SIZE + 16)
        {
            for align in [
                1,
                2,
                4,
                8,
                16,
                32,
                MEMORY_CHUNK_SIZE / 2,
                MEMORY_CHUNK_SIZE,
                2 * MEMORY_CHUNK_SIZE,
            ] {
                let layout = Layout::from_size_align(size, align).unwrap();
                let _ = LayoutBulkAlloc::new(layout, System);
            }
        }
    }

    #[test]
    fn test_alloc() {
        let backend = GAlloc::default();

        for size in (1..64)
            .chain(MEMORY_CHUNK_SIZE / 2 - 16..MEMORY_CHUNK_SIZE / 2 + 16)
            .chain(MEMORY_CHUNK_SIZE - 16..MEMORY_CHUNK_SIZE + 16)
        {
            for align in [
                1,
                2,
                4,
                8,
                16,
                32,
                MEMORY_CHUNK_SIZE / 2,
                MEMORY_CHUNK_SIZE,
                2 * MEMORY_CHUNK_SIZE,
            ] {
                let layout = Layout::from_size_align(size, align).unwrap();
                let alloc = A::new(layout, backend.clone());

                let blocks_in_chunk = {
                    let block_layout = UnsafeLayoutBulkAlloc::<System>::block_layout(layout);
                    let chunk_layout = UnsafeLayoutBulkAlloc::<System>::chunk_layout(block_layout);
                    let blocks_in_chunk =
                        (chunk_layout.size() - size_of::<PointerList>()) / block_layout.size();
                    assert!(0 < blocks_in_chunk);
                    blocks_in_chunk
                };

                unsafe {
                    for _ in 0..2 {
                        let mut pointers = Vec::new();
                        for _ in 0..blocks_in_chunk {
                            let ptr = alloc.alloc(layout);
                            assert_eq!(ptr.is_null(), false);
                            pointers.push(ptr);
                        }

                        for s in 1..32 {
                            let layout = Layout::from_size_align(s, align).unwrap();
                            let ptr = alloc.alloc(layout);
                            assert_eq!(ptr.is_null(), false);
                            pointers.push(ptr);
                        }

                        for i in 0..blocks_in_chunk {
                            let ptr = pointers[i];
                            alloc.dealloc(ptr, layout);
                        }

                        for s in 1..32 {
                            let layout = Layout::from_size_align(s, align).unwrap();
                            let i = blocks_in_chunk + s - 1;
                            let ptr = pointers[i];
                            alloc.dealloc(ptr, layout);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_alloc_and_use() {
        let backend = GAlloc::default();

        unsafe {
            let alloc = A::new(Layout::new::<u8>(), backend.clone());
            let mut pointers = Vec::new();

            for i in 0..65535 {
                let ptr = alloc.alloc(Layout::new::<u8>());
                *ptr = i as u8;
                pointers.push(ptr);
            }

            for i in 0..65535 {
                let ptr = alloc.alloc(Layout::new::<u128>());
                *(ptr.cast::<u128>()) = i;
                pointers.push(ptr);
            }

            for i in 0..65535 {
                let ptr = pointers[i];
                assert_eq!(*ptr, i as u8);
                alloc.dealloc(ptr, Layout::new::<u8>());
            }

            for i in 0..65535 {
                let ptr = pointers[i + 65535];
                assert_eq!(*(ptr.cast::<u128>()), i as u128);
                alloc.dealloc(ptr, Layout::new::<u128>());
            }
        }
    }
}

struct MemBlock {
    next: Link<Self>,
    len: usize,
    _pinned: std::marker::PhantomPinned,
}
