#![no_std]

//! C-ABI wrappers of `base16ct` 1.0.0 for extraction, one per `[entries]` symbol in
//! `extraction.toml`; `Base16ct/Spec/Program.lean` specifies their calls. Arguments come in the
//! order `src, src_len, out_len, dst, dst_len`, each wrapper taking the ones it needs. Statuses:
//! 0 success, 1 `Error::InvalidLength`, 2 `Error::InvalidEncoding`.

use base16ct::{Error, lower, mixed, upper};
use core::slice;

unsafe fn input<'a>(src: *const u8, src_len: usize) -> &'a [u8] {
    unsafe { slice::from_raw_parts(src, src_len) }
}

unsafe fn buffer<'a>(dst: *mut u8, dst_len: usize) -> &'a mut [u8] {
    unsafe { slice::from_raw_parts_mut(dst, dst_len) }
}

fn error_status(error: Error) -> u32 {
    match error {
        Error::InvalidLength => 1,
        Error::InvalidEncoding => 2,
    }
}

/// Writes the length of the returned slice to `out_len` on success.
unsafe fn report(result: Result<&[u8], Error>, out_len: *mut usize) -> u32 {
    match result {
        Ok(output) => {
            unsafe { *out_len = output.len() };
            0
        }
        Err(error) => error_status(error),
    }
}

macro_rules! into_buffer {
    ($name:ident, $call:expr) => {
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $name(
            src: *const u8,
            src_len: usize,
            out_len: *mut usize,
            dst: *mut u8,
            dst_len: usize,
        ) -> u32 {
            let call: for<'a> fn(&[u8], &'a mut [u8]) -> Result<&'a [u8], Error> = $call;
            unsafe { report(call(input(src, src_len), buffer(dst, dst_len)), out_len) }
        }
    };
}

into_buffer!(base16ct_lower_encode, lower::encode);
into_buffer!(base16ct_upper_encode, upper::encode);
into_buffer!(base16ct_lower_encode_str, |s, d| lower::encode_str(s, d).map(str::as_bytes));
into_buffer!(base16ct_upper_encode_str, |s, d| upper::encode_str(s, d).map(str::as_bytes));
into_buffer!(base16ct_lower_decode, |s, d| lower::decode(s, d));
into_buffer!(base16ct_upper_decode, |s, d| upper::decode(s, d));
into_buffer!(base16ct_mixed_decode, |s, d| mixed::decode(s, d));

#[unsafe(no_mangle)]
pub unsafe extern "C" fn base16ct_decoded_len(
    src: *const u8,
    src_len: usize,
    out_len: *mut usize,
) -> u32 {
    match base16ct::decoded_len(unsafe { input(src, src_len) }) {
        Ok(length) => {
            unsafe { *out_len = length };
            0
        }
        Err(error) => error_status(error),
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn base16ct_encoded_len(src: *const u8, src_len: usize, out_len: *mut usize) {
    unsafe { *out_len = base16ct::encoded_len(input(src, src_len)) };
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}
