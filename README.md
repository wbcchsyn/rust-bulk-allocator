[![Build Status](https://travis-ci.org/wbcchsyn/rust-bulk-allocator.svg?branch=master)](https://travis-ci.org/wbcchsyn/rust-bulk-allocator)

# bulk_allocator

bulk-allocator is implementations for GlobalAlloc holding memory cache.
The instance acquires bulk memories from the backend, and frees them on the drop at once for
the performance.

Method `dealloc` does not free the specified pointer soon, but pools in the cache.

Method `alloc` pops and returns from the cache if not empty; otherwise, `alloc` allocates a
bulk memory from the backend, splits into pieces to make cache at first.

It is when the instance is dropped that the memory chunks are deallocated.

License: LGPL-3.0-or-later OR Apache-2.0
