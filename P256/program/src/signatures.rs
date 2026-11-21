//! Entry points of ECDSA/P-256 (ecdsa 0.17.0 at `NistP256`, SHA-256): signing, verification,
//! key recovery, and decoding a DER or a raw `r ‖ s` signature.
//!
//! Arguments: a secret key is its 32-byte scalar, built with `SigningKey::from_bytes`; a public
//! key is its 65-byte uncompressed SEC 1 encoding, built with `VerifyingKey::from_sec1_bytes`; a
//! signature is `r ‖ s` (64 bytes, `Signature::from_slice`); a recovery ID is one byte
//! (`RecoveryId::from_byte`); a message is one slice. The wrapper checks none of them: the caller
//! supplies values these constructors accept (`ValidCall`), and on anything else the call panics
//! (`abi::outside`). Results: a signature as `r ‖ s`, a public key uncompressed, a verdict as no
//! bytes.

use crate::abi::{self, CRATE, Inputs, Output};
use p256::ecdsa::{
    RecoveryId, Signature, SigningKey, VerifyingKey,
    signature::{Signer, Verifier},
};

fn signing_key(inputs: &Inputs, i: usize) -> Result<SigningKey, u32> {
    Ok(SigningKey::from_bytes(&inputs.array::<32>(i)?.into()).unwrap_or_else(|_| abi::outside()))
}

fn verifying_key(inputs: &Inputs, i: usize) -> Result<VerifyingKey, u32> {
    Ok(VerifyingKey::from_sec1_bytes(&inputs.array::<65>(i)?).unwrap_or_else(|_| abi::outside()))
}

fn signature(inputs: &Inputs, i: usize) -> Result<Signature, u32> {
    Ok(Signature::from_slice(inputs.get(i)?).unwrap_or_else(|_| abi::outside()))
}

fn recovery_id(inputs: &Inputs, i: usize) -> Result<RecoveryId, u32> {
    Ok(RecoveryId::from_byte(inputs.array::<1>(i)?[0]).unwrap_or_else(|| abi::outside()))
}

fn crate_result<T, E>(result: Result<T, E>) -> Result<T, u32> {
    result.map_err(|_| CRATE)
}

fn push_signature(output: &mut Output, signature: &Signature) -> Result<(), u32> {
    output.push(&signature.to_bytes())
}

/// `Signer::try_sign` for `SigningKey` at `Signature` (`P256.Spec.Program.Routines.signingKeyTrySign`)
///
/// # Safety
///
/// As for `abi::call`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn p256_signing_key_try_sign(
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
                let key = signing_key(inputs, 0)?;
                let msg = inputs.get(1)?;
                let signed: Signature = crate_result(key.try_sign(msg))?;
                push_signature(output, &signed)
            },
        )
    }
}

/// `Verifier<Signature>::verify` for `VerifyingKey` (`P256.Spec.Program.Routines.verifyingKeyVerify`)
///
/// # Safety
///
/// As for `abi::call`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn p256_verifying_key_verify(
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
            |inputs, _output| {
                let key = verifying_key(inputs, 0)?;
                let signature = signature(inputs, 1)?;
                let msg = inputs.get(2)?;
                crate_result(key.verify(msg, &signature))
            },
        )
    }
}

/// `VerifyingKey::recover_from_msg`
///
/// # Safety
///
/// As for `abi::call`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn p256_verifying_key_recover_from_msg(
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
                let signature = signature(inputs, 0)?;
                let id = recovery_id(inputs, 1)?;
                let key = crate_result(VerifyingKey::recover_from_msg(inputs.get(2)?, &signature, id))?;
                output.push(key.to_sec1_point(false).as_bytes())
            },
        )
    }
}

/// `Signature::from_der`
///
/// # Safety
///
/// As for `abi::call`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn p256_signature_from_der(
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
                let signed = crate_result(Signature::from_der(inputs.get(0)?))?;
                push_signature(output, &signed)
            },
        )
    }
}

/// `Signature::from_slice` (`P256.Spec.Program.Routines.signatureFromSlice`)
///
/// # Safety
///
/// As for `abi::call`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn p256_signature_from_slice(
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
                let signed = crate_result(Signature::from_slice(inputs.get(0)?))?;
                push_signature(output, &signed)
            },
        )
    }
}
