//! Prints `crate_generated.txt`: answers of the real `sha1` 0.11.0, not published vectors.
//!
//! Each record names the entry point of `Sha1/program/src/lib.rs` whose calls it repeats:
//!
//! * `Compress`: `block_api::compress` from the state words `State` on the block bytes `Blocks`,
//!   giving `Out`, the `[u32; 5]` result's bytes in memory, least significant byte first;
//! * `UpdateFinalize`: `update` once per slice of `Slices` (hex, separated by `,`, `-` for an empty
//!   slice), then `finalize`, giving `Out`;
//! * `Reset`: as `UpdateFinalize` with `Digest::reset` after the first `Split` slices;
//! * `FinalizeReset`: as `UpdateFinalize` with `finalize_reset` after the first `Split` slices,
//!   then `finalize`, giving the two digests in `Out`;
//! * `UpdateReset`: as `Reset` from `Default::default` with `Update::update`, `Reset::reset`, and
//!   `FixedOutput::finalize_into`;
//! * `FinalizeIntoReset`: as `FinalizeReset` from `Default::default` with
//!   `Digest::finalize_into_reset` for the first digest and `FixedOutputReset::finalize_into_reset`
//!   for the second;
//! * `FinalizeFixedReset`: as `FinalizeReset` from `Default::default` with
//!   `FixedOutputReset::finalize_fixed_reset` for both digests.

use sha1::block_api;
use sha1::digest::{self, Output};
use sha1::{Digest, Sha1};

/// xorshift64, for reproducible inputs
fn next(state: &mut u64) -> u8 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    (*state >> 32) as u8
}

fn bytes(seed: &mut u64, count: usize) -> Vec<u8> {
    (0..count).map(|_| next(seed)).collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn slices_hex(slices: &[Vec<u8>]) -> String {
    let parts: Vec<String> = slices
        .iter()
        .map(|s| if s.is_empty() { "-".to_string() } else { hex(s) })
        .collect();
    parts.join(",")
}

fn compress(state: [u32; 5], blocks: &[u8]) {
    let mut out = state;
    let chunks: Vec<[u8; 64]> = blocks
        .chunks_exact(64)
        .map(|chunk| chunk.try_into().unwrap())
        .collect();
    block_api::compress(&mut out, &chunks);
    let state_hex: Vec<String> = state.iter().map(|word| format!("{word:08x}")).collect();
    let out_bytes: Vec<u8> = out.iter().flat_map(|word| word.to_le_bytes()).collect();
    println!("Compress");
    println!("State = {}", state_hex.join(""));
    println!("Blocks = {}", hex(blocks));
    println!("Out = {}\n", hex(&out_bytes));
}

fn update_finalize(slices: &[Vec<u8>]) {
    let mut hasher = Sha1::new();
    for slice in slices {
        hasher.update(slice);
    }
    let out = hasher.finalize();
    println!("UpdateFinalize");
    println!("Slices = {}", slices_hex(slices));
    println!("Out = {}\n", hex(&out));
}

fn reset(slices: &[Vec<u8>], split: usize) {
    let mut hasher = Sha1::new();
    for slice in slices.iter().take(split) {
        hasher.update(slice);
    }
    Digest::reset(&mut hasher);
    for slice in slices.iter().skip(split) {
        hasher.update(slice);
    }
    let out = hasher.finalize();
    println!("Reset");
    println!("Slices = {}", slices_hex(slices));
    println!("Split = {split}");
    println!("Out = {}\n", hex(&out));
}

fn finalize_reset(slices: &[Vec<u8>], split: usize) {
    let mut hasher = Sha1::new();
    for slice in slices.iter().take(split) {
        hasher.update(slice);
    }
    let first = hasher.finalize_reset();
    for slice in slices.iter().skip(split) {
        hasher.update(slice);
    }
    let second = hasher.finalize();
    println!("FinalizeReset");
    println!("Slices = {}", slices_hex(slices));
    println!("Split = {split}");
    println!("Out = {}{}\n", hex(&first), hex(&second));
}

fn update_reset(slices: &[Vec<u8>], split: usize) {
    let mut hasher = Sha1::default();
    for slice in slices.iter().take(split) {
        digest::Update::update(&mut hasher, slice);
    }
    digest::Reset::reset(&mut hasher);
    for slice in slices.iter().skip(split) {
        digest::Update::update(&mut hasher, slice);
    }
    let mut out = Output::<Sha1>::default();
    digest::FixedOutput::finalize_into(hasher, &mut out);
    println!("UpdateReset");
    println!("Slices = {}", slices_hex(slices));
    println!("Split = {split}");
    println!("Out = {}\n", hex(&out));
}

fn finalize_into_reset(slices: &[Vec<u8>], split: usize) {
    let mut hasher = Sha1::default();
    for slice in slices.iter().take(split) {
        hasher.update(slice);
    }
    let mut first = Output::<Sha1>::default();
    Digest::finalize_into_reset(&mut hasher, &mut first);
    for slice in slices.iter().skip(split) {
        hasher.update(slice);
    }
    let mut second = Output::<Sha1>::default();
    digest::FixedOutputReset::finalize_into_reset(&mut hasher, &mut second);
    println!("FinalizeIntoReset");
    println!("Slices = {}", slices_hex(slices));
    println!("Split = {split}");
    println!("Out = {}{}\n", hex(&first), hex(&second));
}

fn finalize_fixed_reset(slices: &[Vec<u8>], split: usize) {
    let mut hasher = Sha1::default();
    for slice in slices.iter().take(split) {
        hasher.update(slice);
    }
    let first = digest::FixedOutputReset::finalize_fixed_reset(&mut hasher);
    for slice in slices.iter().skip(split) {
        hasher.update(slice);
    }
    let second = digest::FixedOutputReset::finalize_fixed_reset(&mut hasher);
    println!("FinalizeFixedReset");
    println!("Slices = {}", slices_hex(slices));
    println!("Split = {split}");
    println!("Out = {}{}\n", hex(&first), hex(&second));
}

fn main() {
    println!("# Generated by generator/ from the real sha1 0.11.0; not published vectors.\n");
    let mut seed = 0x5348_4131_2d30_3131u64;

    let h0 = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];
    let extreme = [[0; 5], [u32::MAX; 5], h0];
    for state in extreme {
        for count in [0, 1, 2, 3] {
            let blocks = bytes(&mut seed, 64 * count);
            compress(state, &blocks);
        }
    }
    for count in [1, 5] {
        let state: [u32; 5] = core::array::from_fn(|_| {
            u32::from_be_bytes(bytes(&mut seed, 4).try_into().unwrap())
        });
        let blocks = bytes(&mut seed, 64 * count);
        compress(state, &blocks);
    }

    let shapes: [&[usize]; 7] = [
        &[],
        &[0],
        &[0, 0, 3],
        &[1, 63, 1, 0, 64],
        &[55, 1, 8, 64, 65],
        &[64, 64, 128],
        &[200, 3, 0, 120, 57, 56],
    ];
    for shape in shapes {
        let slices: Vec<Vec<u8>> = shape.iter().map(|&n| bytes(&mut seed, n)).collect();
        update_finalize(&slices);
        for split in [0, 1, shape.len() / 2, shape.len(), shape.len() + 1, usize::MAX] {
            reset(&slices, split);
            finalize_reset(&slices, split);
        }
    }

    for shape in shapes {
        let slices: Vec<Vec<u8>> = shape.iter().map(|&n| bytes(&mut seed, n)).collect();
        for split in [0, 1, shape.len() / 2, shape.len(), shape.len() + 1, usize::MAX] {
            update_reset(&slices, split);
            finalize_into_reset(&slices, split);
            finalize_fixed_reset(&slices, split);
        }
    }
}
