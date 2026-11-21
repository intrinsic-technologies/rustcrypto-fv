#![no_std]

//! C-ABI entry points into `hkdf` 0.13.0 with `sha1` 0.11.0's `Sha1` and `sha2` 0.11.1's `Sha256`,
//! `Sha384` and `Sha512`, for extraction. Each exported function is an `[entries]` symbol in
//! `extraction.toml`; `Hkdf/Spec/Program.lean` specifies the calls the theorems make. The `hkdf_`
//! entries use `Hkdf` and `HkdfExtract` (`GenericHkdf<Hmac<_>>`, `GenericHkdfExtract<Hmac<_>>`),
//! the `simple_hkdf_` entries `SimpleHkdf` and `SimpleHkdfExtract`, the same types over
//! `SimpleHmac`. The SHA-1, SHA-384 and SHA-512 entries repeat SHA-256's (`entry_points!`).
//!
//! A null `salt` pointer passes `None` to `new`, and any other pointer `Some` of the `salt_len`
//! bytes there. `extract`, `finalize_expand` and `input_ikm_derive_key` take their IKM slices as a
//! table of addresses and one of lengths; `expand` passes its table of `&[u8]` to
//! `expand_multi_info` unchanged.

use hkdf::hmac::digest::Output;
use hkdf::hmac::{Hmac, SimpleHmac};
use hkdf::{GenericHkdf, GenericHkdfExtract, HmacImpl, Kdf};
use sha1::Sha1;
use sha2::{Sha256, Sha384, Sha512};

/// `None` for a null `salt`, otherwise `Some` of the `salt_len` bytes at `salt`.
unsafe fn salt<'a>(salt: *const u8, salt_len: usize) -> Option<&'a [u8]> {
    if salt.is_null() {
        None
    } else {
        Some(unsafe { core::slice::from_raw_parts(salt, salt_len) })
    }
}

/// `new(salt)`, then `input_ikm` once per slice in order.
#[inline(always)]
unsafe fn context<H: HmacImpl>(
    ikm: *const *const u8,
    num_ikm: usize,
    ikm_lens: *const usize,
    salt: *const u8,
    salt_len: usize,
) -> GenericHkdfExtract<H> {
    let mut context = GenericHkdfExtract::<H>::new(unsafe { self::salt(salt, salt_len) });
    let addresses = unsafe { core::slice::from_raw_parts(ikm, num_ikm) };
    let lengths = unsafe { core::slice::from_raw_parts(ikm_lens, num_ikm) };
    for (&address, &length) in addresses.iter().zip(lengths) {
        context.input_ikm(unsafe { core::slice::from_raw_parts(address, length) });
    }
    context
}

/// `new(salt)`, `input_ikm` once per slice in order, then `finalize`; writes the PRK to `prk`.
#[inline(always)]
unsafe fn extract<H: HmacImpl>(
    ikm: *const *const u8,
    num_ikm: usize,
    ikm_lens: *const usize,
    salt: *const u8,
    salt_len: usize,
    prk: *mut u8,
) {
    let context = unsafe { self::context::<H>(ikm, num_ikm, ikm_lens, salt, salt_len) };
    let (key, _): (Output<H>, GenericHkdf<H>) = context.finalize();
    unsafe { core::slice::from_raw_parts_mut(prk, key.len()) }.copy_from_slice(&key);
}

/// `from_prk`, then `expand_multi_info`; returns 0, or 1 for `InvalidPrkLength`, 2 for
/// `InvalidLength`.
#[inline(always)]
unsafe fn expand<H: HmacImpl>(
    prk: *const u8,
    prk_len: usize,
    info: *const &[u8],
    num_info: usize,
    okm: *mut u8,
    okm_len: usize,
) -> u32 {
    let prk = unsafe { core::slice::from_raw_parts(prk, prk_len) };
    let Ok(hkdf) = GenericHkdf::<H>::from_prk(prk) else {
        return 1;
    };
    let info = unsafe { core::slice::from_raw_parts(info, num_info) };
    let okm = unsafe { core::slice::from_raw_parts_mut(okm, okm_len) };
    match hkdf.expand_multi_info(info, okm) {
        Ok(()) => 0,
        Err(_) => 2,
    }
}

/// `new(salt)`, then `Kdf::derive_key`; returns 0, or 1 for `kdf::Error`.
#[inline(always)]
unsafe fn derive_key<H: HmacImpl>(
    salt: *const u8,
    salt_len: usize,
    secret: *const u8,
    secret_len: usize,
    info: *const u8,
    info_len: usize,
    out: *mut u8,
    out_len: usize,
) -> u32 {
    let context = GenericHkdfExtract::<H>::new(unsafe { self::salt(salt, salt_len) });
    let secret = unsafe { core::slice::from_raw_parts(secret, secret_len) };
    let info = unsafe { core::slice::from_raw_parts(info, info_len) };
    let out = unsafe { core::slice::from_raw_parts_mut(out, out_len) };
    match context.derive_key(secret, info, out) {
        Ok(()) => 0,
        Err(_) => 1,
    }
}

/// `expand(info, okm)`; returns 0, or 2 for `InvalidLength`.
#[inline(always)]
unsafe fn expand_one<H: HmacImpl>(
    hkdf: &GenericHkdf<H>,
    info: *const u8,
    info_len: usize,
    okm: *mut u8,
    okm_len: usize,
) -> u32 {
    let info = unsafe { core::slice::from_raw_parts(info, info_len) };
    let okm = unsafe { core::slice::from_raw_parts_mut(okm, okm_len) };
    match hkdf.expand(info, okm) {
        Ok(()) => 0,
        Err(_) => 2,
    }
}

/// `GenericHkdf::extract`, the PRK written to `prk`, then `expand`; 0, or 2 for `InvalidLength`.
#[inline(always)]
unsafe fn extract_expand<H: HmacImpl>(
    salt: *const u8,
    salt_len: usize,
    ikm: *const u8,
    ikm_len: usize,
    info: *const u8,
    info_len: usize,
    okm: *mut u8,
    okm_len: usize,
    prk: *mut u8,
) -> u32 {
    let ikm = unsafe { core::slice::from_raw_parts(ikm, ikm_len) };
    let (key, hkdf): (Output<H>, GenericHkdf<H>) =
        GenericHkdf::<H>::extract(unsafe { self::salt(salt, salt_len) }, ikm);
    unsafe { core::slice::from_raw_parts_mut(prk, key.len()) }.copy_from_slice(&key);
    unsafe { expand_one(&hkdf, info, info_len, okm, okm_len) }
}

/// `GenericHkdf::new(salt, ikm)`, then `expand`; returns 0, or 2 for `InvalidLength`.
#[inline(always)]
unsafe fn new_expand<H: HmacImpl>(
    salt: *const u8,
    salt_len: usize,
    ikm: *const u8,
    ikm_len: usize,
    info: *const u8,
    info_len: usize,
    okm: *mut u8,
    okm_len: usize,
) -> u32 {
    let ikm = unsafe { core::slice::from_raw_parts(ikm, ikm_len) };
    let hkdf = GenericHkdf::<H>::new(unsafe { self::salt(salt, salt_len) }, ikm);
    unsafe { expand_one(&hkdf, info, info_len, okm, okm_len) }
}

/// `new(salt)`, `input_ikm` per slice, the `GenericHkdf` of `finalize`, then `expand`; returns 0,
/// or 2 for `InvalidLength`.
#[inline(always)]
unsafe fn finalize_expand<H: HmacImpl>(
    ikm: *const *const u8,
    num_ikm: usize,
    ikm_lens: *const usize,
    salt: *const u8,
    salt_len: usize,
    info: *const u8,
    info_len: usize,
    okm: *mut u8,
    okm_len: usize,
) -> u32 {
    let context = unsafe { self::context::<H>(ikm, num_ikm, ikm_lens, salt, salt_len) };
    let (_, hkdf): (Output<H>, GenericHkdf<H>) = context.finalize();
    unsafe { expand_one(&hkdf, info, info_len, okm, okm_len) }
}

/// `new(salt)`, `input_ikm` per slice, then `Kdf::derive_key`; returns 0, or 1 for `kdf::Error`.
#[inline(always)]
unsafe fn input_ikm_derive_key<H: HmacImpl>(
    ikm: *const *const u8,
    num_ikm: usize,
    ikm_lens: *const usize,
    salt: *const u8,
    salt_len: usize,
    secret: *const u8,
    secret_len: usize,
    info: *const u8,
    info_len: usize,
    out: *mut u8,
    out_len: usize,
) -> u32 {
    let context = unsafe { self::context::<H>(ikm, num_ikm, ikm_lens, salt, salt_len) };
    let secret = unsafe { core::slice::from_raw_parts(secret, secret_len) };
    let info = unsafe { core::slice::from_raw_parts(info, info_len) };
    let out = unsafe { core::slice::from_raw_parts_mut(out, out_len) };
    match context.derive_key(secret, info, out) {
        Ok(()) => 0,
        Err(_) => 1,
    }
}

/// `HkdfExtract<Sha256>`: writes the 32-byte PRK of the salt and the IKM slices.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn hkdf_sha256_extract(
    ikm: *const *const u8,
    num_ikm: usize,
    ikm_lens: *const usize,
    salt: *const u8,
    salt_len: usize,
    prk: *mut u8,
) {
    unsafe { extract::<Hmac<Sha256>>(ikm, num_ikm, ikm_lens, salt, salt_len, prk) }
}

/// `SimpleHkdfExtract<Sha256>`: writes the 32-byte PRK of the salt and the IKM slices.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn simple_hkdf_sha256_extract(
    ikm: *const *const u8,
    num_ikm: usize,
    ikm_lens: *const usize,
    salt: *const u8,
    salt_len: usize,
    prk: *mut u8,
) {
    unsafe { extract::<SimpleHmac<Sha256>>(ikm, num_ikm, ikm_lens, salt, salt_len, prk) }
}

/// `Hkdf<Sha256>::from_prk`, then `expand_multi_info` into the `okm_len` bytes at `okm`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn hkdf_sha256_expand(
    prk: *const u8,
    prk_len: usize,
    info: *const &[u8],
    num_info: usize,
    okm: *mut u8,
    okm_len: usize,
) -> u32 {
    unsafe { expand::<Hmac<Sha256>>(prk, prk_len, info, num_info, okm, okm_len) }
}

/// `SimpleHkdf<Sha256>::from_prk`, then `expand_multi_info` into the `okm_len` bytes at `okm`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn simple_hkdf_sha256_expand(
    prk: *const u8,
    prk_len: usize,
    info: *const &[u8],
    num_info: usize,
    okm: *mut u8,
    okm_len: usize,
) -> u32 {
    unsafe { expand::<SimpleHmac<Sha256>>(prk, prk_len, info, num_info, okm, okm_len) }
}

/// `HkdfExtract<Sha256>::new`, then `Kdf::derive_key` into the `out_len` bytes at `out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn hkdf_sha256_derive_key(
    salt: *const u8,
    salt_len: usize,
    secret: *const u8,
    secret_len: usize,
    info: *const u8,
    info_len: usize,
    out: *mut u8,
    out_len: usize,
) -> u32 {
    unsafe {
        derive_key::<Hmac<Sha256>>(
            salt, salt_len, secret, secret_len, info, info_len, out, out_len,
        )
    }
}

/// `SimpleHkdfExtract<Sha256>::new`, then `Kdf::derive_key` into the `out_len` bytes at `out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn simple_hkdf_sha256_derive_key(
    salt: *const u8,
    salt_len: usize,
    secret: *const u8,
    secret_len: usize,
    info: *const u8,
    info_len: usize,
    out: *mut u8,
    out_len: usize,
) -> u32 {
    unsafe {
        derive_key::<SimpleHmac<Sha256>>(
            salt, salt_len, secret, secret_len, info, info_len, out, out_len,
        )
    }
}

/// `Hkdf<Sha256>::extract`, the PRK to `prk`, then `expand` into the bytes at `okm`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn hkdf_sha256_extract_expand(
    salt: *const u8,
    salt_len: usize,
    ikm: *const u8,
    ikm_len: usize,
    info: *const u8,
    info_len: usize,
    okm: *mut u8,
    okm_len: usize,
    prk: *mut u8,
) -> u32 {
    unsafe {
        extract_expand::<Hmac<Sha256>>(
            salt, salt_len, ikm, ikm_len, info, info_len, okm, okm_len, prk,
        )
    }
}

/// `Hkdf<Sha256>::new`, then `expand` into the `okm_len` bytes at `okm`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn hkdf_sha256_new_expand(
    salt: *const u8,
    salt_len: usize,
    ikm: *const u8,
    ikm_len: usize,
    info: *const u8,
    info_len: usize,
    okm: *mut u8,
    okm_len: usize,
) -> u32 {
    unsafe {
        new_expand::<Hmac<Sha256>>(
            salt, salt_len, ikm, ikm_len, info, info_len, okm, okm_len,
        )
    }
}

/// `HkdfExtract<Sha256>`, `input_ikm` per slice, `finalize`, then `expand` into `okm`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn hkdf_sha256_finalize_expand(
    ikm: *const *const u8,
    num_ikm: usize,
    ikm_lens: *const usize,
    salt: *const u8,
    salt_len: usize,
    info: *const u8,
    info_len: usize,
    okm: *mut u8,
    okm_len: usize,
) -> u32 {
    unsafe {
        finalize_expand::<Hmac<Sha256>>(
            ikm, num_ikm, ikm_lens, salt, salt_len, info, info_len, okm, okm_len,
        )
    }
}

/// `HkdfExtract<Sha256>`, `input_ikm` per slice, then `Kdf::derive_key` into `out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn hkdf_sha256_input_ikm_derive_key(
    ikm: *const *const u8,
    num_ikm: usize,
    ikm_lens: *const usize,
    salt: *const u8,
    salt_len: usize,
    secret: *const u8,
    secret_len: usize,
    info: *const u8,
    info_len: usize,
    out: *mut u8,
    out_len: usize,
) -> u32 {
    unsafe {
        input_ikm_derive_key::<Hmac<Sha256>>(
            ikm, num_ikm, ikm_lens, salt, salt_len, secret, secret_len, info, info_len, out,
            out_len,
        )
    }
}

/// `SimpleHkdf<Sha256>::extract`, the PRK to `prk`, then `expand` into the bytes at `okm`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn simple_hkdf_sha256_extract_expand(
    salt: *const u8,
    salt_len: usize,
    ikm: *const u8,
    ikm_len: usize,
    info: *const u8,
    info_len: usize,
    okm: *mut u8,
    okm_len: usize,
    prk: *mut u8,
) -> u32 {
    unsafe {
        extract_expand::<SimpleHmac<Sha256>>(
            salt, salt_len, ikm, ikm_len, info, info_len, okm, okm_len, prk,
        )
    }
}

/// `SimpleHkdf<Sha256>::new`, then `expand` into the `okm_len` bytes at `okm`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn simple_hkdf_sha256_new_expand(
    salt: *const u8,
    salt_len: usize,
    ikm: *const u8,
    ikm_len: usize,
    info: *const u8,
    info_len: usize,
    okm: *mut u8,
    okm_len: usize,
) -> u32 {
    unsafe {
        new_expand::<SimpleHmac<Sha256>>(
            salt, salt_len, ikm, ikm_len, info, info_len, okm, okm_len,
        )
    }
}

/// `SimpleHkdfExtract<Sha256>`, `input_ikm` per slice, `finalize`, then `expand` into `okm`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn simple_hkdf_sha256_finalize_expand(
    ikm: *const *const u8,
    num_ikm: usize,
    ikm_lens: *const usize,
    salt: *const u8,
    salt_len: usize,
    info: *const u8,
    info_len: usize,
    okm: *mut u8,
    okm_len: usize,
) -> u32 {
    unsafe {
        finalize_expand::<SimpleHmac<Sha256>>(
            ikm, num_ikm, ikm_lens, salt, salt_len, info, info_len, okm, okm_len,
        )
    }
}

/// `SimpleHkdfExtract<Sha256>`, `input_ikm` per slice, then `Kdf::derive_key` into `out`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn simple_hkdf_sha256_input_ikm_derive_key(
    ikm: *const *const u8,
    num_ikm: usize,
    ikm_lens: *const usize,
    salt: *const u8,
    salt_len: usize,
    secret: *const u8,
    secret_len: usize,
    info: *const u8,
    info_len: usize,
    out: *mut u8,
    out_len: usize,
) -> u32 {
    unsafe {
        input_ikm_derive_key::<SimpleHmac<Sha256>>(
            ikm, num_ikm, ikm_lens, salt, salt_len, secret, secret_len, info, info_len, out,
            out_len,
        )
    }
}

/// The seven entry points over the HMAC type `$h`, with the names given, as for `Sha256` above.
macro_rules! entry_points {
    ($h:ty: $extract:ident, $expand:ident, $derive_key:ident, $extract_expand:ident,
        $new_expand:ident, $finalize_expand:ident, $input_ikm_derive_key:ident) => {
        /// The `extract` shape over this HMAC type.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $extract(
            ikm: *const *const u8,
            num_ikm: usize,
            ikm_lens: *const usize,
            salt: *const u8,
            salt_len: usize,
            prk: *mut u8,
        ) {
            unsafe { extract::<$h>(ikm, num_ikm, ikm_lens, salt, salt_len, prk) }
        }

        /// The `expand` shape over this HMAC type.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $expand(
            prk: *const u8,
            prk_len: usize,
            info: *const &[u8],
            num_info: usize,
            okm: *mut u8,
            okm_len: usize,
        ) -> u32 {
            unsafe { expand::<$h>(prk, prk_len, info, num_info, okm, okm_len) }
        }

        /// The `derive_key` shape over this HMAC type.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $derive_key(
            salt: *const u8,
            salt_len: usize,
            secret: *const u8,
            secret_len: usize,
            info: *const u8,
            info_len: usize,
            out: *mut u8,
            out_len: usize,
        ) -> u32 {
            unsafe {
                derive_key::<$h>(salt, salt_len, secret, secret_len, info, info_len, out, out_len)
            }
        }

        /// The `extract_expand` shape over this HMAC type.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $extract_expand(
            salt: *const u8,
            salt_len: usize,
            ikm: *const u8,
            ikm_len: usize,
            info: *const u8,
            info_len: usize,
            okm: *mut u8,
            okm_len: usize,
            prk: *mut u8,
        ) -> u32 {
            unsafe {
                extract_expand::<$h>(
                    salt, salt_len, ikm, ikm_len, info, info_len, okm, okm_len, prk,
                )
            }
        }

        /// The `new_expand` shape over this HMAC type.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $new_expand(
            salt: *const u8,
            salt_len: usize,
            ikm: *const u8,
            ikm_len: usize,
            info: *const u8,
            info_len: usize,
            okm: *mut u8,
            okm_len: usize,
        ) -> u32 {
            unsafe { new_expand::<$h>(salt, salt_len, ikm, ikm_len, info, info_len, okm, okm_len) }
        }

        /// The `finalize_expand` shape over this HMAC type.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $finalize_expand(
            ikm: *const *const u8,
            num_ikm: usize,
            ikm_lens: *const usize,
            salt: *const u8,
            salt_len: usize,
            info: *const u8,
            info_len: usize,
            okm: *mut u8,
            okm_len: usize,
        ) -> u32 {
            unsafe {
                finalize_expand::<$h>(
                    ikm, num_ikm, ikm_lens, salt, salt_len, info, info_len, okm, okm_len,
                )
            }
        }

        /// The `input_ikm_derive_key` shape over this HMAC type.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $input_ikm_derive_key(
            ikm: *const *const u8,
            num_ikm: usize,
            ikm_lens: *const usize,
            salt: *const u8,
            salt_len: usize,
            secret: *const u8,
            secret_len: usize,
            info: *const u8,
            info_len: usize,
            out: *mut u8,
            out_len: usize,
        ) -> u32 {
            unsafe {
                input_ikm_derive_key::<$h>(
                    ikm, num_ikm, ikm_lens, salt, salt_len, secret, secret_len, info, info_len,
                    out, out_len,
                )
            }
        }
    };
}

entry_points!(Hmac<Sha1>:
    hkdf_sha1_extract,
    hkdf_sha1_expand,
    hkdf_sha1_derive_key,
    hkdf_sha1_extract_expand,
    hkdf_sha1_new_expand,
    hkdf_sha1_finalize_expand,
    hkdf_sha1_input_ikm_derive_key
);

entry_points!(SimpleHmac<Sha1>:
    simple_hkdf_sha1_extract,
    simple_hkdf_sha1_expand,
    simple_hkdf_sha1_derive_key,
    simple_hkdf_sha1_extract_expand,
    simple_hkdf_sha1_new_expand,
    simple_hkdf_sha1_finalize_expand,
    simple_hkdf_sha1_input_ikm_derive_key
);

entry_points!(Hmac<Sha384>:
    hkdf_sha384_extract,
    hkdf_sha384_expand,
    hkdf_sha384_derive_key,
    hkdf_sha384_extract_expand,
    hkdf_sha384_new_expand,
    hkdf_sha384_finalize_expand,
    hkdf_sha384_input_ikm_derive_key
);

entry_points!(SimpleHmac<Sha384>:
    simple_hkdf_sha384_extract,
    simple_hkdf_sha384_expand,
    simple_hkdf_sha384_derive_key,
    simple_hkdf_sha384_extract_expand,
    simple_hkdf_sha384_new_expand,
    simple_hkdf_sha384_finalize_expand,
    simple_hkdf_sha384_input_ikm_derive_key
);

entry_points!(Hmac<Sha512>:
    hkdf_sha512_extract,
    hkdf_sha512_expand,
    hkdf_sha512_derive_key,
    hkdf_sha512_extract_expand,
    hkdf_sha512_new_expand,
    hkdf_sha512_finalize_expand,
    hkdf_sha512_input_ikm_derive_key
);

entry_points!(SimpleHmac<Sha512>:
    simple_hkdf_sha512_extract,
    simple_hkdf_sha512_expand,
    simple_hkdf_sha512_derive_key,
    simple_hkdf_sha512_extract_expand,
    simple_hkdf_sha512_new_expand,
    simple_hkdf_sha512_finalize_expand,
    simple_hkdf_sha512_input_ikm_derive_key
);

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
