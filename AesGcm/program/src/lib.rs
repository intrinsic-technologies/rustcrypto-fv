#![no_std]

//! C-ABI entry points into `aes-gcm` 0.11.1 for extraction, four for each of `Aes128Gcm` and
//! `Aes256Gcm`, each an `[entries]` symbol in `extraction.toml`; `AesGcm/Spec/Program.lean`
//! specifies the calls the theorems make. Each entry keys a new cipher from `key` (16 or 32 bytes);
//! `nonce` points to the 12 nonce bytes and `aad` to `aad_len` bytes of associated data. Every
//! slice address, empty slices included, must be non-null. A status of 0 is `Ok` and 1 is `Err`.
//! Nothing allocates, so the program has no allocator.

use aes_gcm::aead::consts::U12;
use aes_gcm::aead::{AeadInOut, Buffer, Error, Key, KeyInit, inout::InOutBuf};
use aes_gcm::{Aes128Gcm, Aes256Gcm, Nonce, Tag};
use core::slice;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

/// An `aead::Buffer` over caller memory: the first `len` bytes of `bytes` are its contents, and
/// `extend_from_slice` fails if the rest of `bytes` cannot hold the extension.
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

fn status(result: Result<(), Error>) -> u32 {
    match result {
        Ok(()) => 0,
        Err(_) => 1,
    }
}

/// Defines the four entry points of one AES-GCM type.
macro_rules! entries {
    (
        $gcm:ty,
        $encrypt_inout_detached:ident, $decrypt_inout_detached:ident,
        $encrypt_in_place:ident, $decrypt_in_place:ident
    ) => {
        /// `AeadInOut::encrypt_inout_detached` from `input[..len]` to `output[..len]`, then the
        /// tag to `output[len..len + 16]`; `input` and `output` must not overlap.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $encrypt_inout_detached(
            key: *const Key<$gcm>,
            nonce: *const Nonce<U12>,
            aad: *const u8,
            aad_len: usize,
            input: *const u8,
            output: *mut u8,
            len: usize,
        ) -> u32 {
            let cipher = <$gcm>::new(unsafe { &*key });
            let aad = unsafe { slice::from_raw_parts(aad, aad_len) };
            let buffer = unsafe { InOutBuf::from_raw(input, output, len) };
            match cipher.encrypt_inout_detached(unsafe { &*nonce }, aad, buffer) {
                Ok(computed) => {
                    unsafe { slice::from_raw_parts_mut(output.add(len), 16) }
                        .copy_from_slice(&computed);
                    0
                }
                Err(_) => 1,
            }
        }

        /// `AeadInOut::decrypt_inout_detached` from `input[..len]` to `output[..len]`, with the
        /// tag `input[len..len + 16]`; `input` and `output` must not overlap.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $decrypt_inout_detached(
            key: *const Key<$gcm>,
            nonce: *const Nonce<U12>,
            aad: *const u8,
            aad_len: usize,
            input: *const u8,
            output: *mut u8,
            len: usize,
        ) -> u32 {
            let cipher = <$gcm>::new(unsafe { &*key });
            let aad = unsafe { slice::from_raw_parts(aad, aad_len) };
            let tag = unsafe { &*input.add(len).cast::<Tag>() };
            let buffer = unsafe { InOutBuf::from_raw(input, output, len) };
            status(cipher.decrypt_inout_detached(unsafe { &*nonce }, aad, buffer, tag))
        }

        /// `AeadInOut::encrypt_in_place` on a `SliceBuffer` holding `buffer[..len]` within
        /// `buffer[..capacity]`; `len <= capacity`.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $encrypt_in_place(
            key: *const Key<$gcm>,
            nonce: *const Nonce<U12>,
            aad: *const u8,
            aad_len: usize,
            buffer: *mut u8,
            len: usize,
            capacity: usize,
        ) -> u32 {
            let cipher = <$gcm>::new(unsafe { &*key });
            let aad = unsafe { slice::from_raw_parts(aad, aad_len) };
            let bytes = unsafe { slice::from_raw_parts_mut(buffer, capacity) };
            let mut buffer = SliceBuffer { bytes, len };
            let nonce = unsafe { &*nonce };
            status(<$gcm as AeadInOut>::encrypt_in_place(&cipher, nonce, aad, &mut buffer))
        }

        /// `AeadInOut::decrypt_in_place` on a `SliceBuffer` holding `buffer[..len]`.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $decrypt_in_place(
            key: *const Key<$gcm>,
            nonce: *const Nonce<U12>,
            aad: *const u8,
            aad_len: usize,
            buffer: *mut u8,
            len: usize,
        ) -> u32 {
            let cipher = <$gcm>::new(unsafe { &*key });
            let aad = unsafe { slice::from_raw_parts(aad, aad_len) };
            let bytes = unsafe { slice::from_raw_parts_mut(buffer, len) };
            let mut buffer = SliceBuffer { bytes, len };
            let nonce = unsafe { &*nonce };
            status(<$gcm as AeadInOut>::decrypt_in_place(&cipher, nonce, aad, &mut buffer))
        }
    };
}

entries!(
    Aes128Gcm,
    aes128gcm_encrypt_inout_detached, aes128gcm_decrypt_inout_detached,
    aes128gcm_encrypt_in_place, aes128gcm_decrypt_in_place
);

entries!(
    Aes256Gcm,
    aes256gcm_encrypt_inout_detached, aes256gcm_decrypt_inout_detached,
    aes256gcm_encrypt_in_place, aes256gcm_decrypt_in_place
);
