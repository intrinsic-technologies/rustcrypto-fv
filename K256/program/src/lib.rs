#![no_std]

//! C-ABI entry points into `k256` 0.14.0 for extraction, one per crate function. Each exported
//! function is an `[entries]` symbol in `extraction.toml`; `K256/Spec/Program.lean` specifies the
//! calls the theorems make.
//!
//! A wrapper copies the caller's bytes into the crate's types, calls the one function and copies
//! the result out. A typed argument that the function under specification does not decode itself
//! (a key, a signature, a point) is built with the crate's own decoder; the call contract requires
//! those bytes to be a valid encoding, so `invalid_input` is never reached under it. A
//! function that can fail gives status 0 for `Ok` and 1 for `Err` in EAX (for a verifier: 0 for a
//! valid signature), and writes its output only on `Ok`; a function that cannot fail returns
//! nothing. Output buffers are the first argument. A wrapper whose call allocates takes the
//! caller's heap and resets the bump allocator `HEAP` over it on entry.

extern crate alloc;

use core::{
    alloc::{GlobalAlloc, Layout},
    cell::UnsafeCell,
    convert::Infallible,
    ptr,
};
use k256::{
    AffinePoint, CompressedPoint, FieldBytes, NonZeroScalar, ProjectivePoint, PublicKey, SecretKey,
    ecdh::diffie_hellman,
    ecdsa::{
        RecoveryId, Signature, SigningKey, VerifyingKey,
        signature::{Signer, Verifier},
    },
    elliptic_curve::{
        Generate,
        group::GroupEncoding,
        rand_core::{TryCryptoRng, TryRng},
        sec1::ToSec1Point,
    },
    schnorr,
};

/// Never returns: reached only on an input the call contract (`ValidCall`) requires to be valid.
#[inline(never)]
fn invalid_input() -> ! {
    loop {}
}

/// The value of a decoder the call contract requires to succeed.
fn valid<T>(value: Option<T>) -> T {
    match value {
        Some(value) => value,
        None => invalid_input(),
    }
}

/// Reads `N` bytes at `pointer`.
unsafe fn array<'a, const N: usize>(pointer: *const u8) -> &'a [u8; N] {
    unsafe { &*pointer.cast::<[u8; N]>() }
}

/// Reads `len` bytes at `pointer`.
unsafe fn slice<'a>(pointer: *const u8, len: usize) -> &'a [u8] {
    unsafe { core::slice::from_raw_parts(pointer, len) }
}

/// Copies `bytes` to `output`.
unsafe fn put(output: *mut u8, bytes: &[u8]) {
    unsafe { core::slice::from_raw_parts_mut(output, bytes.len()) }.copy_from_slice(bytes);
}

/// Status of a `Result`: 0 for `Ok`, 1 for `Err`.
fn status<T, E>(result: &Result<T, E>) -> u32 {
    u32::from(result.is_err())
}

/// The ECDSA signing key of 32 big-endian bytes.
unsafe fn signing_key(secret: *const u8) -> SigningKey {
    valid(SigningKey::from_bytes(unsafe { array::<32>(secret) }.into()).ok())
}

/// The secret key of 32 big-endian bytes.
unsafe fn secret_key(secret: *const u8) -> SecretKey {
    valid(SecretKey::from_bytes(unsafe { array::<32>(secret) }.into()).ok())
}

/// The public key of a 65-byte uncompressed SEC 1 encoding.
unsafe fn public_key(bytes: *const u8) -> PublicKey {
    valid(PublicKey::from_sec1_bytes(unsafe { array::<65>(bytes) }).ok())
}

/// The ECDSA signature `r || s` of 64 bytes.
unsafe fn ecdsa_signature(signature: *const u8) -> Signature {
    valid(Signature::from_bytes(unsafe { array::<64>(signature) }.into()).ok())
}

/// The recovery identifier in a byte.
fn recovery_id(byte: u8) -> RecoveryId {
    valid(RecoveryId::from_byte(byte))
}

/// The point of a 33-byte `GroupEncoding`: compressed SEC 1, compact `05 ‖ x`, or 33 zero bytes.
unsafe fn projective_point(bytes: *const u8) -> ProjectivePoint {
    let bytes = CompressedPoint::from(*unsafe { array::<33>(bytes) });
    valid(ProjectivePoint::from_bytes(&bytes).into_option())
}

/// `Signer::try_sign` for ECDSA's `SigningKey`: the 64-byte signature `r || s` of `msg`. No
/// status: for this key type `try_sign` returns `Ok` whenever it returns.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn k256_signing_key_try_sign(
    signature: *mut u8,
    secret: *const u8,
    msg: *const u8,
    msg_len: usize,
) {
    let key = unsafe { signing_key(secret) };
    let result: Result<Signature, _> = key.try_sign(unsafe { slice(msg, msg_len) });
    if let Ok(value) = &result {
        unsafe { put(signature, &value.to_bytes()) };
    }
}

/// `Verifier::verify` for ECDSA's `VerifyingKey`: 0 for a valid signature of `msg`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn k256_verifying_key_verify(
    public_key: *const u8,
    msg: *const u8,
    msg_len: usize,
    signature: *const u8,
) -> u32 {
    let key = valid(VerifyingKey::from_sec1_bytes(unsafe { array::<65>(public_key) }).ok());
    let signature = unsafe { ecdsa_signature(signature) };
    status(&key.verify(unsafe { slice(msg, msg_len) }, &signature))
}

/// `VerifyingKey::recover_from_prehash`: the 65-byte uncompressed key recovered from `prehash`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn k256_verifying_key_recover_from_prehash(
    verifying_key: *mut u8,
    prehash: *const u8,
    prehash_len: usize,
    signature: *const u8,
    recovery: u8,
) -> u32 {
    let signature = unsafe { ecdsa_signature(signature) };
    let result = VerifyingKey::recover_from_prehash(
        unsafe { slice(prehash, prehash_len) },
        &signature,
        recovery_id(recovery),
    );
    if let Ok(key) = &result {
        unsafe { put(verifying_key, key.to_sec1_point(false).as_bytes()) };
    }
    status(&result)
}

/// `Signature::from_der`: the signature `r || s` (64 bytes) of an ASN.1 DER encoding.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn k256_signature_from_der(
    signature: *mut u8,
    der: *const u8,
    der_len: usize,
) -> u32 {
    let result = Signature::from_der(unsafe { slice(der, der_len) });
    if let Ok(value) = &result {
        unsafe { put(signature, &value.to_bytes()) };
    }
    status(&result)
}

/// `Signature::from_slice`: the signature `r || s` (64 bytes) of a slice of bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn k256_signature_from_slice(
    signature: *mut u8,
    bytes: *const u8,
    bytes_len: usize,
) -> u32 {
    let result = Signature::from_slice(unsafe { slice(bytes, bytes_len) });
    if let Ok(value) = &result {
        unsafe { put(signature, &value.to_bytes()) };
    }
    status(&result)
}

/// The BIP 340 signing key of 32 big-endian bytes.
unsafe fn schnorr_signing_key(secret: *const u8) -> schnorr::SigningKey {
    let bytes: &FieldBytes = unsafe { array::<32>(secret) }.into();
    valid(schnorr::SigningKey::from_bytes(bytes).ok())
}

/// The BIP 340 verifying key of a 32-byte x-coordinate.
unsafe fn schnorr_verifying_key(public_key: *const u8) -> schnorr::VerifyingKey {
    let bytes: &FieldBytes = unsafe { array::<32>(public_key) }.into();
    valid(schnorr::VerifyingKey::from_bytes(bytes).ok())
}

/// The BIP 340 signature `r || s` of 64 bytes.
unsafe fn schnorr_signature(signature: *const u8) -> schnorr::Signature {
    valid(schnorr::Signature::from_bytes(unsafe { array::<64>(signature) }).ok())
}

/// `schnorr::SigningKey::sign_raw`: the 64-byte BIP 340 signature of `msg` with `aux_rand`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn k256_schnorr_sign_raw(
    signature: *mut u8,
    secret: *const u8,
    msg: *const u8,
    msg_len: usize,
    aux_rand: *const u8,
) -> u32 {
    let key = unsafe { schnorr_signing_key(secret) };
    let result = key.sign_raw(unsafe { slice(msg, msg_len) }, unsafe { array::<32>(aux_rand) });
    if let Ok(value) = &result {
        unsafe { put(signature, &value.to_bytes()) };
    }
    status(&result)
}

/// `schnorr::VerifyingKey::verify_raw`: 0 for a valid BIP 340 signature of `message`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn k256_schnorr_verify_raw(
    public_key: *const u8,
    message: *const u8,
    message_len: usize,
    signature: *const u8,
) -> u32 {
    let key = unsafe { schnorr_verifying_key(public_key) };
    let signature = unsafe { schnorr_signature(signature) };
    status(&key.verify_raw(unsafe { slice(message, message_len) }, &signature))
}

/// A random number generator serving the caller's bytes in order; it never returns once they
/// run out, which the theorems' premise excludes.
struct CallerBytes<'a> {
    rest: &'a [u8],
}

impl TryRng for CallerBytes<'_> {
    type Error = Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Infallible> {
        let mut bytes = [0; 4];
        self.try_fill_bytes(&mut bytes)?;
        Ok(u32::from_le_bytes(bytes))
    }

    fn try_next_u64(&mut self) -> Result<u64, Infallible> {
        let mut bytes = [0; 8];
        self.try_fill_bytes(&mut bytes)?;
        Ok(u64::from_le_bytes(bytes))
    }

    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Infallible> {
        if dst.len() > self.rest.len() {
            invalid_input();
        }
        let (taken, rest) = self.rest.split_at(dst.len());
        dst.copy_from_slice(taken);
        self.rest = rest;
        Ok(())
    }
}

impl TryCryptoRng for CallerBytes<'_> {}

/// `Generate::generate_from_rng` for `SigningKey`: the key drawn from the caller's bytes, written
/// as its 32-byte secret scalar, then its verifying key's 65-byte uncompressed SEC 1 encoding.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn k256_signing_key_generate_from_rng(
    signing_key: *mut u8,
    random: *const u8,
    random_len: usize,
) {
    let mut rng = CallerBytes { rest: unsafe { slice(random, random_len) } };
    let key = SigningKey::generate_from_rng(&mut rng);
    unsafe { put(signing_key, &key.to_bytes()) };
    let public = key.verifying_key().to_sec1_point(false);
    unsafe { put(signing_key.add(32), public.as_bytes()) };
}

/// `SecretKey::from_bytes`: the secret key of 32 big-endian bytes, written back as 32 bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn k256_secret_key_from_bytes(secret: *mut u8, bytes: *const u8) -> u32 {
    let result = SecretKey::from_bytes(unsafe { array::<32>(bytes) }.into());
    if let Ok(key) = &result {
        unsafe { put(secret, &key.to_bytes()) };
    }
    status(&result)
}

/// `SecretKey::public_key`: the 65-byte uncompressed SEC 1 public key of a secret key.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn k256_secret_key_public_key(public_key: *mut u8, secret: *const u8) {
    let key = unsafe { secret_key(secret) }.public_key();
    unsafe { put(public_key, key.to_sec1_point(false).as_bytes()) };
}

/// `PublicKey::from_sec1_bytes`: the public key of a SEC 1 encoding, as 65 uncompressed bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn k256_public_key_from_sec1_bytes(
    public_key: *mut u8,
    bytes: *const u8,
    bytes_len: usize,
) -> u32 {
    let result = PublicKey::from_sec1_bytes(unsafe { slice(bytes, bytes_len) });
    if let Ok(key) = &result {
        unsafe { put(public_key, key.to_sec1_point(false).as_bytes()) };
    }
    status(&result)
}

/// `PublicKey::to_sec1_bytes`: the SEC 1 encoding the crate chooses (compressed, 33 bytes).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn k256_public_key_to_sec1_bytes(
    sec1: *mut u8,
    public_key: *const u8,
    heap: *mut u8,
    heap_len: usize,
) {
    HEAP.reset(heap, heap_len);
    let encoded = unsafe { self::public_key(public_key) }.to_sec1_bytes();
    unsafe { put(sec1, &encoded) };
}

/// `SecretKey::from_sec1_der`: the 32-byte secret scalar of a SEC 1 `ECPrivateKey` DER document.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn k256_secret_key_from_sec1_der(
    secret: *mut u8,
    der: *const u8,
    der_len: usize,
) -> u32 {
    let result = SecretKey::from_sec1_der(unsafe { slice(der, der_len) });
    if let Ok(key) = &result {
        unsafe { put(secret, &key.to_bytes()) };
    }
    status(&result)
}

/// `ecdh::diffie_hellman`: the 32 bytes of the x-coordinate of the secret scalar times the point,
/// an `AffinePoint` given as its 33-byte `GroupEncoding` (the identity included).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn k256_ecdh_diffie_hellman(
    shared: *mut u8,
    secret: *const u8,
    public_key: *const u8,
) {
    let bytes: FieldBytes = (*unsafe { array::<32>(secret) }).into();
    let scalar = valid(NonZeroScalar::from_repr(bytes).into_option());
    let bytes = CompressedPoint::from(*unsafe { array::<33>(public_key) });
    let point = valid(AffinePoint::from_bytes(&bytes).into_option());
    let secret = diffie_hellman(scalar, point);
    unsafe { put(shared, secret.raw_secret_bytes()) };
}

/// `Add<ProjectivePoint>` for `ProjectivePoint`: the sum, as a 33-byte `GroupEncoding`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn k256_projective_point_add(
    sum: *mut u8,
    left: *const u8,
    right: *const u8,
) {
    let value = unsafe { projective_point(left) } + unsafe { projective_point(right) };
    unsafe { put(sum, &value.to_bytes()) };
}

/// The bump allocator over the caller's heap: `alloc` hands out the next aligned block, or null
/// when it does not fit, and `dealloc` does nothing. A wrapper that allocates resets it on entry.
struct Heap {
    next: UnsafeCell<usize>,
    end: UnsafeCell<usize>,
}

// SAFETY: the extracted program runs on one thread, and no entry point is reentrant.
unsafe impl Sync for Heap {}

impl Heap {
    /// Serves blocks from the `len` bytes at `start`.
    fn reset(&self, start: *mut u8, len: usize) {
        unsafe { *self.next.get() = start as usize };
        unsafe { *self.end.get() = (start as usize).wrapping_add(len) };
    }
}

// SAFETY: blocks are aligned as requested, lie in the caller's heap and are not reused before a
// reset.
unsafe impl GlobalAlloc for Heap {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let next = unsafe { *self.next.get() };
        let start = next.next_multiple_of(layout.align());
        match start.checked_add(layout.size()) {
            Some(end) if start >= next && end <= unsafe { *self.end.get() } => {
                unsafe { *self.next.get() = end };
                start as *mut u8
            }
            _ => ptr::null_mut(),
        }
    }

    unsafe fn dealloc(&self, _: *mut u8, _: Layout) {}
}

#[global_allocator]
static HEAP: Heap = Heap {
    next: UnsafeCell::new(0),
    end: UnsafeCell::new(0),
};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
