#![no_std]

//! C-ABI wrappers for RustCrypto `p256` 0.14.0, one per extracted entry point.
//!
//! The modules below hold the wrappers: each calls one public function of the crate at one
//! generic instance, with the calling convention of `abi`.

extern crate alloc;

mod abi;
mod arena;
mod extras;
mod keys;
mod points;
mod signatures;

#[cfg(not(test))]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

