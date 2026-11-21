//! Entry point of the P-256 group law: primeorder's `ProjectivePoint` at p256's `NistP256`.
//!
//! Points cross the boundary as SEC 1 bytes: an input point is decoded with the crate's
//! `Sec1Point::from_bytes` and `FromSec1Point` and made projective, and the result is written
//! through `to_affine` with `to_sec1_point(false)`: `00` for the identity, else `04 ‖ x ‖ y`.
//! The decoders check nothing of their own: bytes that are no value of the argument are outside
//! the call's contract (`abi::outside`).

use crate::abi::{self, Inputs, Output};
use p256::{
    AffinePoint, ProjectivePoint, Sec1Point,
    elliptic_curve::sec1::{FromSec1Point, ToSec1Point},
};

fn sec1(inputs: &Inputs, i: usize) -> Result<Sec1Point, u32> {
    Ok(Sec1Point::from_bytes(inputs.get(i)?).unwrap_or_else(|_| abi::outside()))
}

fn affine(inputs: &Inputs, i: usize) -> Result<AffinePoint, u32> {
    let point = AffinePoint::from_sec1_point(&sec1(inputs, i)?).into_option();
    Ok(point.unwrap_or_else(|| abi::outside()))
}

fn projective(inputs: &Inputs, i: usize) -> Result<ProjectivePoint, u32> {
    Ok(ProjectivePoint::from(affine(inputs, i)?))
}

fn put_affine(output: &mut Output, point: &AffinePoint) -> Result<(), u32> {
    output.push(point.to_sec1_point(false).as_bytes())
}

fn put_projective(output: &mut Output, point: &ProjectivePoint) -> Result<(), u32> {
    put_affine(output, &point.to_affine())
}

/// `ProjectivePoint::add` (`P256.Spec.Program.Routines.projectivePointAdd`)
///
/// # Safety
///
/// As for `abi::call`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn p256_projective_point_add(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    output: *mut u8,
    capacity: usize,
    heap: *mut u8,
    heap_len: usize,
) -> u32 {
    unsafe {
        abi::call(
            input,
            num_inputs,
            input_lens,
            output,
            capacity,
            heap,
            heap_len,
            |inputs, output| {
                put_projective(output, &ProjectivePoint::add(&projective(inputs, 0)?, &projective(inputs, 1)?))
            },
        )
    }
}
