# bulk_allocator

bulk_allocator is implementations for AllocRef.
They pool allocated memory and release them on the destruction.

Method `dealloc` caches the released memory and `alloc` reuses it.
If no cache is left, `alloc` acquires a memory chunk from the backend and make cache at first.

Using cache effectively, the performance is better compared to the same name functions in `std::alloc`.

## Note

Trait `AllocRef` is defined only in Rust nightly toolchain so far.
It is required to enable feathre `allocator_api` to use this crate and `AllocRef`.

## Implementations

### BulkAllocator

`AllocRef` method `alloc` and `dealloc` delegate the request to the backend if the argument `layout`
is too large to cache; otherwise, `dealloc` stores the released memory and `alloc` dispatches it and return.

If the argument `layout` is always same, probably `LayoutBulkAllocator` is better.

All methods in `AllocRef` are thread unsafe.

### LayoutBulkAllocator

`LayoutBulkAllocator` behaves like `BulkAllocator` except for the constructor requires `Layout` as the argument.

The instance uses cache only when the argument `layout` is same to what the constructor is passed; otherwise,
the requests are delegated to the backend.