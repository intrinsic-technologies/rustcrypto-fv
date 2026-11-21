//! Entry points for ECDH and key generation from random bytes.
//!
//! Scalars are 32 bytes big-endian, points SEC 1 bytes written uncompressed. The decoders check
//! nothing of their own: bytes that are no value of the argument are outside the call's contract
//! (`ValidCall`), and random bytes that run out before the key is drawn are outside the theorem's
//! premises (`signingKeyGenerateFromRng.arguments`: enough bytes to reach an accepted block);
//! either way the call panics (`abi::outside`).

use crate::abi::{self, ByteRng, Inputs};
use p256::{
    AffinePoint, NonZeroScalar, Sec1Point,
    ecdh::{SharedSecret, diffie_hellman},
    ecdsa::SigningKey,
    elliptic_curve::{Generate, sec1::FromSec1Point},
};
use rand_core::UnwrapErr;

fn nonzero_scalar(inputs: &Inputs, i: usize) -> Result<NonZeroScalar, u32> {
    let scalar = Option::from(NonZeroScalar::from_repr(inputs.array::<32>(i)?.into()));
    Ok(scalar.unwrap_or_else(|| abi::outside()))
}

fn sec1_point(inputs: &Inputs, i: usize) -> Result<Sec1Point, u32> {
    Ok(Sec1Point::from_bytes(inputs.get(i)?).unwrap_or_else(|_| abi::outside()))
}

fn affine_point(inputs: &Inputs, i: usize) -> Result<AffinePoint, u32> {
    let point = AffinePoint::from_sec1_point(&sec1_point(inputs, i)?).into_option();
    Ok(point.unwrap_or_else(|| abi::outside()))
}

/// `Generate::generate_from_rng` for `SigningKey`
/// (`P256.Spec.Program.Routines.signingKeyGenerateFromRng`): the key's scalar, then its verifying
/// key uncompressed
///
/// # Safety
///
/// As for `abi::call`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn p256_signing_key_generate_from_rng(
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
                let bytes = inputs.get(0)?;
                let v = SigningKey::generate_from_rng(&mut UnwrapErr(ByteRng::new(bytes)));
                output.push(&v.to_bytes())?;
                output.push(v.verifying_key().to_sec1_point(false).as_bytes())
            },
        )
    }
}

/// `ecdh::diffie_hellman` at `NistP256` (`P256.Spec.Program.Routines.ecdhDiffieHellman`)
///
/// # Safety
///
/// As for `abi::call`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn p256_ecdh_diffie_hellman(
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
                let shared: SharedSecret =
                    diffie_hellman(nonzero_scalar(inputs, 0)?, affine_point(inputs, 1)?);
                output.push(shared.raw_secret_bytes())
            },
        )
    }
}
