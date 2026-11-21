//! The bump allocator behind the crate's `alloc` feature: allocations come from the caller's heap,
//! the region every entry point receives and hands to `reset`; nothing is freed within a call, and
//! a request past the region's end fails, which Rust's allocation-failure handler turns into a
//! panic. The theorems require a heap of at least the call's `heapBytes`, so that never happens.

#[cfg(not(test))]
struct Heap {
    base: usize,
    length: usize,
    offset: usize,
}

#[cfg(not(test))]
static mut HEAP: Heap = Heap { base: 0, length: 0, offset: 0 };

/// Serve allocations from the `length` bytes at `base`, from their start
pub fn reset(base: *mut u8, length: usize) {
    #[cfg(not(test))]
    unsafe {
        HEAP = Heap { base: base as usize, length, offset: 0 };
    }
    #[cfg(test)]
    let _ = (base, length);
}

#[cfg(not(test))]
struct Bump;

#[cfg(not(test))]
unsafe impl core::alloc::GlobalAlloc for Bump {
    unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
        let heap = &raw mut HEAP;
        unsafe {
            let (base, length, offset) = ((*heap).base, (*heap).length, (*heap).offset);
            let Some(limit) = base.checked_add(length) else {
                return core::ptr::null_mut();
            };
            let start = match base.checked_add(offset).and_then(|a| a.checked_next_multiple_of(layout.align())) {
                Some(start) => start,
                None => return core::ptr::null_mut(),
            };
            match start.checked_add(layout.size()) {
                Some(end) if end <= limit => {
                    (*heap).offset = end - base;
                    start as *mut u8
                }
                _ => core::ptr::null_mut(),
            }
        }
    }

    unsafe fn dealloc(&self, _: *mut u8, _: core::alloc::Layout) {}
}

#[cfg(not(test))]
#[global_allocator]
static ALLOCATOR: Bump = Bump;
