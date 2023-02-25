# bulk\_allocator

bulk-allocator provides implementations of `GlobalAlloc` holding memory cache.
The instance acquires memory chunks from the backend and frees them on the drop at once for
the performance.

Method `dealloc` does not free the specified pointer immediately, but pools in the cache.

Method `alloc` acquires a memory chunk from the backend and stores into the cache if the cache
is empty, and then pops and returns a pointer from the cache.

It is when the instance is dropped that the memory chunks are deallocated.

License: LGPL-3.0-or-later OR Apache-2.0
