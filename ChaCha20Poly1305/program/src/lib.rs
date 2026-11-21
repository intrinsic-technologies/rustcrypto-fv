#![no_std]

//! C-ABI entry points into `chacha20poly1305` 0.11.0 for extraction, at the `ChaCha20Poly1305` type
//! only. Each exported function is an `[entries]` symbol in `extraction.toml`;
//! `ChaCha20Poly1305/Spec/Program.lean` specifies the calls the theorems make.
//!
//! Every wrapper takes its pointers first (key, nonce, associated data, the message or in-place
//! buffer, then tag, heap and output where present) and their lengths after them, in the same
//! order, so that every address is in a register and only lengths are passed on the stack. Each
//! wrapper builds the cipher with `KeyInit::new` from the caller's 32 key bytes. A wrapper returns
//! 0 when the crate returns `Ok` and 1 when it returns its error. The detached encryption writes
//! the tag it returns right after the ciphertext in its output, so each call has one output.

extern crate alloc;

use core::alloc::{GlobalAlloc, Layout};
use core::slice;
use core::sync::atomic::{AtomicUsize, Ordering::Relaxed};

use chacha20poly1305::aead::{Aead, AeadInOut, Buffer, Error, Payload, inout::InOutBuf};
use chacha20poly1305::{ChaCha20Poly1305, Key, KeyInit, Nonce, Tag};

/// Bump allocator over the caller's heap, which `Aead::encrypt` and `Aead::decrypt` need.
struct Heap {
    next: AtomicUsize,
    end: AtomicUsize,
}

unsafe impl GlobalAlloc for Heap {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mask = layout.align() - 1;
        let Some(start) = self.next.load(Relaxed).checked_add(mask) else {
            return core::ptr::null_mut();
        };
        let start = start & !mask;
        match start.checked_add(layout.size()) {
            Some(end) if end <= self.end.load(Relaxed) => {
                self.next.store(end, Relaxed);
                start as *mut u8
            }
            _ => core::ptr::null_mut(),
        }
    }

    unsafe fn dealloc(&self, _: *mut u8, _: Layout) {}
}

#[global_allocator]
static HEAP: Heap = Heap { next: AtomicUsize::new(0), end: AtomicUsize::new(0) };

/// An `aead::Buffer` over caller memory: the first `len` bytes of `bytes` are its contents, and
/// `extend_from_slice` fails if the rest of `bytes` cannot hold the extension (aes-gcm's form).
struct SliceBuffer<'a> {
    bytes: &'a mut [u8],
    len: usize,
}

impl AsRef<[u8]> for SliceBuffer<'_> {
    fn as_ref(&self) -> &[u8] {
        self.bytes.get(..self.len).unwrap_or_default()
    }
}

impl AsMut<[u8]> for SliceBuffer<'_> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.bytes.get_mut(..self.len).unwrap_or_default()
    }
}

impl Buffer for SliceBuffer<'_> {
    fn extend_from_slice(&mut self, other: &[u8]) -> Result<(), Error> {
        let end = self.len.checked_add(other.len()).ok_or(Error)?;
        let space = self.bytes.get_mut(self.len..end).ok_or(Error)?;
        space.copy_from_slice(other);
        self.len = end;
        Ok(())
    }

    fn truncate(&mut self, len: usize) {
        self.len = self.len.min(len);
    }
}

fn status<T, E>(result: Result<T, E>) -> u32 {
    if result.is_ok() { 0 } else { 1 }
}

/// `AeadInOut::encrypt_inout_detached` from `input[..len]` to `output[..len]`, then the tag to
/// `output[len..len + 16]`; `output` must not overlap any input.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn chacha20poly1305_encrypt_inout_detached(
    key: *const Key,
    nonce: *const Nonce,
    associated_data: *const u8,
    input: *const u8,
    output: *mut u8,
    associated_data_len: usize,
    len: usize,
) -> u32 {
    let cipher = ChaCha20Poly1305::new(unsafe { &*key });
    let associated_data = unsafe { slice::from_raw_parts(associated_data, associated_data_len) };
    let buffer = unsafe { InOutBuf::from_raw(input, output, len) };
    match cipher.encrypt_inout_detached(unsafe { &*nonce }, associated_data, buffer) {
        Ok(tag) => {
            unsafe { output.add(len).cast::<Tag>().write(tag) };
            0
        }
        Err(_) => 1,
    }
}

/// `AeadInOut::decrypt_inout_detached` from `input[..len]` to `output[..len]`, with the 16-byte
/// tag at `tag`; `output` must not overlap any input.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn chacha20poly1305_decrypt_inout_detached(
    key: *const Key,
    nonce: *const Nonce,
    associated_data: *const u8,
    input: *const u8,
    tag: *const Tag,
    output: *mut u8,
    associated_data_len: usize,
    len: usize,
) -> u32 {
    let cipher = ChaCha20Poly1305::new(unsafe { &*key });
    let associated_data = unsafe { slice::from_raw_parts(associated_data, associated_data_len) };
    let buffer = unsafe { InOutBuf::from_raw(input, output, len) };
    let nonce = unsafe { &*nonce };
    status(cipher.decrypt_inout_detached(nonce, associated_data, buffer, unsafe { &*tag }))
}

unsafe fn reset_heap(heap: *mut u8, heap_len: usize) {
    HEAP.next.store(heap as usize, Relaxed);
    HEAP.end.store((heap as usize).saturating_add(heap_len), Relaxed);
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn chacha20poly1305_encrypt(
    key: *const Key,
    nonce: *const Nonce,
    associated_data: *const u8,
    message: *const u8,
    heap: *mut u8,
    output: *mut u8,
    associated_data_len: usize,
    message_len: usize,
    heap_len: usize,
    output_len: usize,
) -> u32 {
    unsafe { reset_heap(heap, heap_len) };
    let cipher = ChaCha20Poly1305::new(unsafe { &*key });
    let aad = unsafe { slice::from_raw_parts(associated_data, associated_data_len) };
    let msg = unsafe { slice::from_raw_parts(message, message_len) };
    let output = unsafe { slice::from_raw_parts_mut(output, output_len) };
    match cipher.encrypt(unsafe { &*nonce }, Payload { msg, aad }) {
        Ok(ciphertext) => {
            output[..ciphertext.len()].copy_from_slice(&ciphertext);
            0
        }
        Err(_) => 1,
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn chacha20poly1305_decrypt(
    key: *const Key,
    nonce: *const Nonce,
    associated_data: *const u8,
    ciphertext: *const u8,
    heap: *mut u8,
    output: *mut u8,
    associated_data_len: usize,
    ciphertext_len: usize,
    heap_len: usize,
    output_len: usize,
) -> u32 {
    unsafe { reset_heap(heap, heap_len) };
    let cipher = ChaCha20Poly1305::new(unsafe { &*key });
    let aad = unsafe { slice::from_raw_parts(associated_data, associated_data_len) };
    let msg = unsafe { slice::from_raw_parts(ciphertext, ciphertext_len) };
    let output = unsafe { slice::from_raw_parts_mut(output, output_len) };
    match cipher.decrypt(unsafe { &*nonce }, Payload { msg, aad }) {
        Ok(plaintext) => {
            output[..plaintext.len()].copy_from_slice(&plaintext);
            0
        }
        Err(_) => 1,
    }
}

/// `AeadInOut::encrypt_in_place` on a `SliceBuffer` holding `buffer[..len]` within
/// `buffer[..capacity]`; `len <= capacity`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn chacha20poly1305_encrypt_in_place(
    key: *const Key,
    nonce: *const Nonce,
    associated_data: *const u8,
    buffer: *mut u8,
    associated_data_len: usize,
    len: usize,
    capacity: usize,
) -> u32 {
    let cipher = ChaCha20Poly1305::new(unsafe { &*key });
    let associated_data = unsafe { slice::from_raw_parts(associated_data, associated_data_len) };
    let bytes = unsafe { slice::from_raw_parts_mut(buffer, capacity) };
    let mut buffer = SliceBuffer { bytes, len };
    let nonce = unsafe { &*nonce };
    status(AeadInOut::encrypt_in_place(&cipher, nonce, associated_data, &mut buffer))
}

/// `AeadInOut::decrypt_in_place` on a `SliceBuffer` holding `buffer[..len]`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn chacha20poly1305_decrypt_in_place(
    key: *const Key,
    nonce: *const Nonce,
    associated_data: *const u8,
    buffer: *mut u8,
    associated_data_len: usize,
    len: usize,
) -> u32 {
    let cipher = ChaCha20Poly1305::new(unsafe { &*key });
    let associated_data = unsafe { slice::from_raw_parts(associated_data, associated_data_len) };
    let bytes = unsafe { slice::from_raw_parts_mut(buffer, len) };
    let mut buffer = SliceBuffer { bytes, len };
    let nonce = unsafe { &*nonce };
    status(AeadInOut::decrypt_in_place(&cipher, nonce, associated_data, &mut buffer))
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
