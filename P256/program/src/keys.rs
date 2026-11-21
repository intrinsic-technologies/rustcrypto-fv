//! Entry points of p256's keys: secret keys from bytes, public keys from secret keys and SEC 1
//! bytes, and the SPKI DER public key file.
//!
//! Inputs: a secret key is 32 bytes big-endian; a public key is its SEC 1 encoding, decoded by
//! the crate. A public key is written back uncompressed. That each slice is a value of its
//! argument is the caller's duty (`ValidCall`); the helpers below panic through `abi::outside`
//! otherwise.

use crate::abi::{self, CRATE, Inputs, Output};
use p256::{
    PublicKey, SecretKey,
    ecdsa::VerifyingKey,
    elliptic_curve::{pkcs8::DecodePublicKey, sec1::ToSec1Point},
};

/// Slice `i` as a secret key (`ValidCall`: a valid one)
fn secret(inputs: &Inputs, i: usize) -> Result<SecretKey, u32> {
    Ok(SecretKey::from_bytes(&inputs.array::<32>(i)?.into()).unwrap_or_else(|_| abi::outside()))
}

/// Slice `i` as a public key (`ValidCall`: a valid one)
fn public(inputs: &Inputs, i: usize) -> Result<PublicKey, u32> {
    Ok(PublicKey::from_sec1_bytes(inputs.get(i)?).unwrap_or_else(|_| abi::outside()))
}

/// The crate's error as status 1
fn crate_err<T, E>(result: Result<T, E>) -> Result<T, u32> {
    result.map_err(|_| CRATE)
}

fn push_public(output: &mut Output<'_>, key: &PublicKey) -> Result<(), u32> {
    output.push(key.to_sec1_point(false).as_bytes())
}

/// `SecretKey::from_bytes`
///
/// # Safety
///
/// As for `abi::call`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn p256_secret_key_from_bytes(
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
                let key = crate_err(SecretKey::from_bytes(&inputs.array::<32>(0)?.into()))?;
                output.push(&key.to_bytes())
            },
        )
    }
}

/// `SecretKey::public_key`
///
/// # Safety
///
/// As for `abi::call`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn p256_secret_key_public_key(
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
                push_public(output, &secret(inputs, 0)?.public_key())
            },
        )
    }
}

/// `PublicKey::from_sec1_bytes` (`P256.Spec.Program.Routines.publicKeyFromSec1Bytes`)
///
/// # Safety
///
/// As for `abi::call`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn p256_public_key_from_sec1_bytes(
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
                push_public(output, &crate_err(PublicKey::from_sec1_bytes(inputs.get(0)?))?)
            },
        )
    }
}

/// `PublicKey::to_sec1_bytes`
///
/// # Safety
///
/// As for `abi::call`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn p256_public_key_to_sec1_bytes(
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
                output.push(&public(inputs, 0)?.to_sec1_bytes())
            },
        )
    }
}

/// `DecodePublicKey::from_public_key_der` for `VerifyingKey`
///
/// # Safety
///
/// As for `abi::call`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn p256_verifying_key_from_public_key_der(
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
                let key = crate_err(VerifyingKey::from_public_key_der(inputs.get(0)?))?;
                output.push(key.to_sec1_point(false).as_bytes())
            },
        )
    }
}
