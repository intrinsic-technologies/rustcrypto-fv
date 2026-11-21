#![no_std]

//! C-ABI entry points into `sha1` 0.11.0 for extraction. Each exported function is an `[entries]`
//! symbol in `extraction.toml`, and `Sha1/Spec/Program.lean` specifies its calls.
//!
//! Every entry taking `input`, `num_inputs` and `input_lens` takes `num_inputs` byte slices: slice
//! `i` is the `input_lens[i]` bytes at `input[i]`.

use sha1::block_api;
use sha1::digest::{self, Output};
use sha1::{Digest, Sha1};

/// Writes `Sha1::digest` of the `input_len` bytes at `input` to the 20 bytes at `output`.
///
/// # Safety
///
/// `input` must be non-null, even when `input_len` is zero, and readable for `input_len` bytes;
/// `output` must be non-null and writable for 20 bytes; and the two must not overlap.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sha1_digest(input: *const u8, input_len: usize, output: *mut u8) {
    let input = unsafe { core::slice::from_raw_parts(input, input_len) };
    let output = unsafe { core::slice::from_raw_parts_mut(output, 20) };
    output.copy_from_slice(&Sha1::digest(input));
}

/// Applies `sha1::block_api::compress` to the five-word state at `state` and the `num_blocks`
/// 64-byte blocks at `blocks`.
///
/// # Safety
///
/// `state` must be non-null and valid for reads and writes of 5 aligned `u32`s, `blocks` must be
/// non-null, even when `num_blocks` is zero, and readable for `64 * num_blocks` bytes, and the two
/// must not overlap.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sha1_compress(state: *mut u32, blocks: *const u8, num_blocks: usize) {
    let state = unsafe { &mut *(state as *mut [u32; 5]) };
    let blocks = unsafe { core::slice::from_raw_parts(blocks as *const [u8; 64], num_blocks) };
    block_api::compress(state, blocks);
}

/// The `num_inputs` slices whose addresses are at `input` and whose lengths are at `input_lens`.
///
/// # Safety
///
/// `input` and `input_lens` must be non-null, aligned for their element types, and readable for
/// `num_inputs` words each, even when `num_inputs` is zero, and each slice address must be
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

/// Updates one `Sha1` hasher from `Sha1::new` with each slice in order and writes its 20-byte
/// `finalize` to `output`.
///
/// # Safety
///
/// As for `inputs`; `output` must be non-null and writable for 20 bytes and must not overlap the
/// tables or the slices.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sha1_update_finalize(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    output: *mut u8,
) {
    let inputs = unsafe { inputs(input, num_inputs, input_lens) };
    let output = unsafe { core::slice::from_raw_parts_mut(output, 20) };
    let mut hasher = Sha1::new();
    for slice in inputs {
        hasher.update(slice);
    }
    output.copy_from_slice(&hasher.finalize());
}

/// Updates one `Sha1` hasher with the first `split` slices, calls `Digest::reset`, updates it with
/// the remaining slices, and writes its 20-byte `finalize` to `output`. If `split` exceeds
/// `num_inputs`, every slice comes before the reset.
///
/// # Safety
///
/// As for `inputs`; `output` must be non-null and writable for 20 bytes and must not overlap the
/// tables or the slices.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sha1_reset(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    split: usize,
    output: *mut u8,
) {
    let mut inputs = unsafe { inputs(input, num_inputs, input_lens) };
    let output = unsafe { core::slice::from_raw_parts_mut(output, 20) };
    let mut hasher = Sha1::new();
    for slice in inputs.by_ref().take(split) {
        hasher.update(slice);
    }
    Digest::reset(&mut hasher);
    for slice in inputs {
        hasher.update(slice);
    }
    output.copy_from_slice(&hasher.finalize());
}

/// Updates one `Sha1` hasher with the first `split` slices, writes its digest to `output[..20]`
/// with `finalize_reset`, updates the same hasher with the remaining slices, and writes its digest
/// to `output[20..40]` with `finalize`. If `split` exceeds `num_inputs`, every slice is in the
/// first message.
///
/// # Safety
///
/// As for `inputs`; `output` must be non-null and writable for 40 bytes and must not overlap the
/// tables or the slices.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sha1_finalize_reset(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    split: usize,
    output: *mut u8,
) {
    let mut inputs = unsafe { inputs(input, num_inputs, input_lens) };
    let output = unsafe { core::slice::from_raw_parts_mut(output, 40) };
    let mut hasher = Sha1::new();
    for slice in inputs.by_ref().take(split) {
        hasher.update(slice);
    }
    output[..20].copy_from_slice(&hasher.finalize_reset());
    for slice in inputs {
        hasher.update(slice);
    }
    output[20..].copy_from_slice(&hasher.finalize());
}

/// As `sha1_reset` from `Default::default`, with `Update::update`, `Reset::reset`, and
/// `FixedOutput::finalize_into`.
///
/// # Safety
///
/// As for `sha1_reset`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sha1_update_reset(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    split: usize,
    output: *mut u8,
) {
    let mut inputs = unsafe { inputs(input, num_inputs, input_lens) };
    let output = unsafe { &mut *(output as *mut Output<Sha1>) };
    let mut hasher = Sha1::default();
    for slice in inputs.by_ref().take(split) {
        digest::Update::update(&mut hasher, slice);
    }
    digest::Reset::reset(&mut hasher);
    for slice in inputs {
        digest::Update::update(&mut hasher, slice);
    }
    digest::FixedOutput::finalize_into(hasher, output);
}

/// As `sha1_finalize_reset` from `Default::default`, writing the first digest with
/// `Digest::finalize_into_reset` and the second with `FixedOutputReset::finalize_into_reset`.
///
/// # Safety
///
/// As for `sha1_finalize_reset`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sha1_finalize_into_reset(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    split: usize,
    output: *mut u8,
) {
    let mut inputs = unsafe { inputs(input, num_inputs, input_lens) };
    let [first, second] = unsafe { &mut *(output as *mut [Output<Sha1>; 2]) };
    let mut hasher = Sha1::default();
    for slice in inputs.by_ref().take(split) {
        hasher.update(slice);
    }
    Digest::finalize_into_reset(&mut hasher, first);
    for slice in inputs {
        hasher.update(slice);
    }
    digest::FixedOutputReset::finalize_into_reset(&mut hasher, second);
}

/// As `sha1_finalize_reset` from `Default::default`, writing both digests with
/// `FixedOutputReset::finalize_fixed_reset`.
///
/// # Safety
///
/// As for `sha1_finalize_reset`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sha1_finalize_fixed_reset(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    split: usize,
    output: *mut u8,
) {
    let mut inputs = unsafe { inputs(input, num_inputs, input_lens) };
    let [first, second] = unsafe { &mut *(output as *mut [Output<Sha1>; 2]) };
    let mut hasher = Sha1::default();
    for slice in inputs.by_ref().take(split) {
        hasher.update(slice);
    }
    *first = digest::FixedOutputReset::finalize_fixed_reset(&mut hasher);
    for slice in inputs {
        hasher.update(slice);
    }
    *second = digest::FixedOutputReset::finalize_fixed_reset(&mut hasher);
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
