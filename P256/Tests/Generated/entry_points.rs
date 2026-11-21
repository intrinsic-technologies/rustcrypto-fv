//! The entry point of each name, for the native generators of `P256/Tests/Generated/`, which
//! name every call by its entry point (its `extraction.toml` name). `generate.sh` of each generator
//! installs this file as a test module of a scratch copy of `P256/program`.

use crate::{extras::*, keys::*, points::*, signatures::*};

/// An entry point: the slice tables, the output and its capacity, then the heap and its length
pub type Entry = unsafe extern "C" fn(*const *const u8, usize, *const usize, *mut u8, usize, *mut u8, usize) -> u32;

/// The entry point named `name`
pub fn by_name(name: &str) -> Option<Entry> {
    Some(match name {
        "secretKeyFromBytes" => p256_secret_key_from_bytes,
        "secretKeyPublicKey" => p256_secret_key_public_key,
        "publicKeyFromSec1Bytes" => p256_public_key_from_sec1_bytes,
        "publicKeyToSec1Bytes" => p256_public_key_to_sec1_bytes,
        "verifyingKeyFromPublicKeyDer" => p256_verifying_key_from_public_key_der,
        "projectivePointAdd" => p256_projective_point_add,
        "signingKeyTrySign" => p256_signing_key_try_sign,
        "verifyingKeyVerify" => p256_verifying_key_verify,
        "verifyingKeyRecoverFromMsg" => p256_verifying_key_recover_from_msg,
        "signatureFromDer" => p256_signature_from_der,
        "signatureFromSlice" => p256_signature_from_slice,
        "signingKeyGenerateFromRng" => p256_signing_key_generate_from_rng,
        "ecdhDiffieHellman" => p256_ecdh_diffie_hellman,
        _ => return None,
    })
}
