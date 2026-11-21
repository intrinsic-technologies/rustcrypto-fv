#![no_std]

//! C-ABI entry points into `md-5` 0.11.0 (library `md5`), with its `oid` feature and without its
//! default `alloc` feature, for extraction. Each exported function is an `[entries]` symbol in
//! `extraction.toml`; `Md5/Spec/Program.lean` specifies its calls. A message given as slices is a
//! table of `num_inputs` addresses at `input` and one of their lengths at `input_lens`.

use md5::Md5;
use md5::block_api::compress;
use md5::digest::array::Array;
use md5::digest::{Digest, FixedOutput, FixedOutputReset, Reset, Update};

/// The `num_inputs` slices whose addresses are at `input` and whose lengths are at `input_lens`.
///
/// # Safety
///
/// The tables must be non-null, aligned and readable for `num_inputs` words each, and each slice
/// non-null and readable for its length.
unsafe fn inputs<'a>(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
) -> impl Iterator<Item = &'a [u8]> {
    let pointers = unsafe { core::slice::from_raw_parts(input, num_inputs) };
    let lengths = unsafe { core::slice::from_raw_parts(input_lens, num_inputs) };
    pointers
        .iter()
        .zip(lengths)
        .map(|(&pointer, &length)| unsafe { core::slice::from_raw_parts(pointer, length) })
}

/// `Md5::digest` of the `input_len` bytes at `input`, written to `output`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn md5_digest(input: *const u8, input_len: usize, output: *mut [u8; 16]) {
    let input = unsafe { core::slice::from_raw_parts(input, input_len) };
    unsafe { *output = Md5::digest(input).into() };
}

/// `Md5::new`, `Digest::update` per slice, then `Digest::finalize` into `output`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn md5_digest_slices(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    output: *mut [u8; 16],
) {
    let mut hasher = Md5::new();
    for slice in unsafe { inputs(input, num_inputs, input_lens) } {
        Digest::update(&mut hasher, slice);
    }
    unsafe { *output = Digest::finalize(hasher).into() };
}

/// The first `num_first` slices by `Digest::update`, `Digest::finalize_reset` into `output[0]`,
/// the rest by `Digest::update`, then `Digest::finalize` into `output[1]`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn md5_digest_slices_reset(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    num_first: usize,
    output: *mut [[u8; 16]; 2],
) {
    let mut inputs = unsafe { inputs(input, num_inputs, input_lens) };
    let output = unsafe { &mut *output };
    let mut hasher = Md5::new();
    for slice in inputs.by_ref().take(num_first) {
        Digest::update(&mut hasher, slice);
    }
    output[0] = Digest::finalize_reset(&mut hasher).into();
    for slice in inputs {
        Digest::update(&mut hasher, slice);
    }
    output[1] = Digest::finalize(hasher).into();
}

/// `Md5::new`, `Update::update` per slice, then `FixedOutput::finalize_into` into `output`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn md5_update_finalize_into(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    output: *mut [u8; 16],
) {
    let mut hasher = Md5::new();
    for slice in unsafe { inputs(input, num_inputs, input_lens) } {
        Update::update(&mut hasher, slice);
    }
    FixedOutput::finalize_into(hasher, Array::cast_from_core_mut(unsafe { &mut *output }));
}

/// The first `num_first` slices by `Digest::update`, `Digest::finalize_into_reset` into
/// `output[0]`, the rest by `Digest::update`, then `Digest::finalize` into `output[1]`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn md5_finalize_into_reset_slices(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    num_first: usize,
    output: *mut [[u8; 16]; 2],
) {
    let mut inputs = unsafe { inputs(input, num_inputs, input_lens) };
    let output = unsafe { &mut *output };
    let mut hasher = Md5::new();
    for slice in inputs.by_ref().take(num_first) {
        Digest::update(&mut hasher, slice);
    }
    Digest::finalize_into_reset(&mut hasher, Array::cast_from_core_mut(&mut output[0]));
    for slice in inputs {
        Digest::update(&mut hasher, slice);
    }
    output[1] = Digest::finalize(hasher).into();
}

/// The first `num_first` slices by `Update::update`, `FixedOutputReset::finalize_into_reset` into
/// `output[0]`, the rest by `Update::update`, then `Digest::finalize` into `output[1]`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn md5_fixed_finalize_into_reset_slices(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    num_first: usize,
    output: *mut [[u8; 16]; 2],
) {
    let mut inputs = unsafe { inputs(input, num_inputs, input_lens) };
    let output = unsafe { &mut *output };
    let mut hasher = Md5::new();
    for slice in inputs.by_ref().take(num_first) {
        Update::update(&mut hasher, slice);
    }
    FixedOutputReset::finalize_into_reset(&mut hasher, Array::cast_from_core_mut(&mut output[0]));
    for slice in inputs {
        Update::update(&mut hasher, slice);
    }
    output[1] = Digest::finalize(hasher).into();
}

/// The first `num_first` slices by `Update::update`, `FixedOutputReset::finalize_fixed_reset`
/// into `output[0]`, the rest by `Update::update`, then `Digest::finalize` into `output[1]`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn md5_finalize_fixed_reset_slices(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    num_first: usize,
    output: *mut [[u8; 16]; 2],
) {
    let mut inputs = unsafe { inputs(input, num_inputs, input_lens) };
    let output = unsafe { &mut *output };
    let mut hasher = Md5::new();
    for slice in inputs.by_ref().take(num_first) {
        Update::update(&mut hasher, slice);
    }
    output[0] = FixedOutputReset::finalize_fixed_reset(&mut hasher).into();
    for slice in inputs {
        Update::update(&mut hasher, slice);
    }
    output[1] = Digest::finalize(hasher).into();
}

/// The first `num_first` slices by `Digest::update`, then `Digest::reset`, the rest by
/// `Digest::update`, then `Digest::finalize` into `output`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn md5_reset_slices(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    num_first: usize,
    output: *mut [u8; 16],
) {
    let mut inputs = unsafe { inputs(input, num_inputs, input_lens) };
    let mut hasher = Md5::new();
    for slice in inputs.by_ref().take(num_first) {
        Digest::update(&mut hasher, slice);
    }
    Digest::reset(&mut hasher);
    for slice in inputs {
        Digest::update(&mut hasher, slice);
    }
    unsafe { *output = Digest::finalize(hasher).into() };
}

/// The first `num_first` slices by `Update::update`, then `Reset::reset`, the rest by
/// `Update::update`, then `Digest::finalize` into `output`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn md5_update_reset_slices(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    num_first: usize,
    output: *mut [u8; 16],
) {
    let mut inputs = unsafe { inputs(input, num_inputs, input_lens) };
    let mut hasher = Md5::new();
    for slice in inputs.by_ref().take(num_first) {
        Update::update(&mut hasher, slice);
    }
    Reset::reset(&mut hasher);
    for slice in inputs {
        Update::update(&mut hasher, slice);
    }
    unsafe { *output = Digest::finalize(hasher).into() };
}

/// `md5::block_api::compress` of the state at `state` with the `num_blocks` blocks at `blocks`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn md5_compress(
    state: *mut [u32; 4],
    blocks: *const [u8; 64],
    num_blocks: usize,
) {
    let blocks = unsafe { core::slice::from_raw_parts(blocks, num_blocks) };
    compress(unsafe { &mut *state }, blocks);
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
