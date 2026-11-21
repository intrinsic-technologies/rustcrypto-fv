#![no_std]

//! C-ABI entry points into `sha2` 0.11.1 for extraction; `Sha2/Spec/Program.lean` specifies them.
//! A table call passes `count` slices as a pointer table, the count and a length table.

use core::slice;
use sha2::block_api::{compress256, compress512};
use sha2::digest::{FixedOutput, FixedOutputReset, Output, Reset, Update};
use sha2::{Digest, Sha224, Sha256, Sha384, Sha512, Sha512_224, Sha512_256};

/// The `count` slices whose addresses are at `table` and whose lengths are at `lengths`.
unsafe fn slices<'a>(
    table: *const *const u8,
    count: usize,
    lengths: *const usize,
) -> impl Iterator<Item = &'a [u8]> {
    let pointers = unsafe { slice::from_raw_parts(table, count) };
    let lengths = unsafe { slice::from_raw_parts(lengths, count) };
    pointers
        .iter()
        .zip(lengths)
        .map(|(&pointer, &length)| unsafe { slice::from_raw_parts(pointer, length) })
}

macro_rules! hasher {
    ($t:ty, $digest:ident, $digest_slices:ident, $reset:ident, $into_reset:ident,
     $trait_fixed_reset:ident, $trait_into_reset:ident) => {
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $digest(data: *const u8, length: usize, out: *mut Output<$t>) {
            let data = unsafe { slice::from_raw_parts(data, length) };
            unsafe { *out = <$t>::digest(data) };
        }

        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $digest_slices(
            table: *const *const u8,
            count: usize,
            lengths: *const usize,
            out: *mut Output<$t>,
        ) {
            let mut hasher = <$t>::new();
            for data in unsafe { slices(table, count, lengths) } {
                Digest::update(&mut hasher, data);
            }
            unsafe { *out = hasher.finalize() };
        }

        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $reset(
            table: *const *const u8,
            count: usize,
            lengths: *const usize,
            out: *mut Output<$t>,
            second_out: *mut Output<$t>,
        ) {
            let mut hasher = <$t>::new();
            for data in unsafe { slices(table, count, lengths) } {
                Digest::update(&mut hasher, data);
            }
            Digest::reset(&mut hasher);
            for data in unsafe { slices(table, count, lengths) } {
                Digest::update(&mut hasher, data);
            }
            unsafe { *out = Digest::finalize_reset(&mut hasher) };
            for data in unsafe { slices(table, count, lengths) } {
                Digest::update(&mut hasher, data);
            }
            unsafe { *second_out = Digest::finalize_reset(&mut hasher) };
        }

        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $into_reset(
            table: *const *const u8,
            count: usize,
            lengths: *const usize,
            out: *mut Output<$t>,
            second_out: *mut Output<$t>,
        ) {
            let mut hasher = <$t>::new();
            for data in unsafe { slices(table, count, lengths) } {
                Digest::update(&mut hasher, data);
            }
            Digest::finalize_into_reset(&mut hasher, unsafe { &mut *out });
            for data in unsafe { slices(table, count, lengths) } {
                Digest::update(&mut hasher, data);
            }
            unsafe { *second_out = FixedOutput::finalize_fixed(hasher) };
        }

        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $trait_fixed_reset(
            table: *const *const u8,
            count: usize,
            lengths: *const usize,
            out: *mut Output<$t>,
            second_out: *mut Output<$t>,
        ) {
            let mut hasher = <$t>::new();
            for data in unsafe { slices(table, count, lengths) } {
                Update::update(&mut hasher, data);
            }
            Reset::reset(&mut hasher);
            for data in unsafe { slices(table, count, lengths) } {
                Update::update(&mut hasher, data);
            }
            unsafe { *out = FixedOutputReset::finalize_fixed_reset(&mut hasher) };
            for data in unsafe { slices(table, count, lengths) } {
                Update::update(&mut hasher, data);
            }
            unsafe { *second_out = FixedOutputReset::finalize_fixed_reset(&mut hasher) };
        }

        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $trait_into_reset(
            table: *const *const u8,
            count: usize,
            lengths: *const usize,
            out: *mut Output<$t>,
            second_out: *mut Output<$t>,
        ) {
            let mut hasher = <$t>::new();
            for data in unsafe { slices(table, count, lengths) } {
                hasher = Update::chain(hasher, data);
            }
            FixedOutputReset::finalize_into_reset(&mut hasher, unsafe { &mut *out });
            for data in unsafe { slices(table, count, lengths) } {
                hasher = Update::chain(hasher, data);
            }
            FixedOutput::finalize_into(hasher, unsafe { &mut *second_out });
        }
    };
}

hasher!(Sha224, sha224_digest, sha224_digest_slices, sha224_reset, sha224_finalize_into_reset,
    sha224_trait_finalize_fixed_reset, sha224_trait_finalize_into_reset);
hasher!(Sha256, sha256_digest, sha256_digest_slices, sha256_reset, sha256_finalize_into_reset,
    sha256_trait_finalize_fixed_reset, sha256_trait_finalize_into_reset);
hasher!(Sha384, sha384_digest, sha384_digest_slices, sha384_reset, sha384_finalize_into_reset,
    sha384_trait_finalize_fixed_reset, sha384_trait_finalize_into_reset);
hasher!(Sha512, sha512_digest, sha512_digest_slices, sha512_reset, sha512_finalize_into_reset,
    sha512_trait_finalize_fixed_reset, sha512_trait_finalize_into_reset);
hasher!(Sha512_224, sha512_224_digest, sha512_224_digest_slices, sha512_224_reset,
    sha512_224_finalize_into_reset, sha512_224_trait_finalize_fixed_reset,
    sha512_224_trait_finalize_into_reset);
hasher!(Sha512_256, sha512_256_digest, sha512_256_digest_slices, sha512_256_reset,
    sha512_256_finalize_into_reset, sha512_256_trait_finalize_fixed_reset,
    sha512_256_trait_finalize_into_reset);

#[unsafe(no_mangle)]
pub unsafe extern "C" fn sha2_compress256(
    state: *mut [u32; 8],
    blocks: *const [u8; 64],
    block_count: usize,
) {
    compress256(unsafe { &mut *state }, unsafe { slice::from_raw_parts(blocks, block_count) });
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn sha2_compress512(
    state: *mut [u64; 8],
    blocks: *const [u8; 128],
    block_count: usize,
) {
    compress512(unsafe { &mut *state }, unsafe { slice::from_raw_parts(blocks, block_count) });
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
