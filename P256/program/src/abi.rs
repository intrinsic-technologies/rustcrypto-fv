//! The calling convention of the one-function entry points. An entry point is `f(input,
//! num_inputs, input_lens, output, capacity, heap, heap_len) -> u32`: slice `i` the
//! `input_lens[i]` bytes at `input[i]`, an output buffer of `capacity` bytes, the caller's heap
//! (`src/arena.rs`). Status 0 is success: `output` holds the result's length, 8 bytes
//! little-endian, then the result. Status 1 is the called function's error, `None` or `false`, and
//! nothing is written to `output`. The wrapper checks nothing of its own: the caller passes as
//! many slices as the function has arguments, each a value of its Rust type, an output buffer that
//! holds the result and a heap that holds what the call allocates
//! (`P256/Spec/Program.lean`, `ValidCall`); on anything else it panics (`outside`), or its
//! behaviour is not specified.

use core::{fmt, slice};

/// Success
pub const OK: u32 = 0;
/// The crate's error, `None` or `false`
pub const CRATE: u32 = 1;

/// A call outside the contract of `call`: a missing slice, or one that is no value of its Rust
/// argument. `ValidCall` rules it out; the wrapper panics, and the panic handler loops.
#[cold]
pub fn outside() -> ! {
    panic!()
}

/// The input slices of one call
pub struct Inputs<'a> {
    pointers: &'a [*const u8],
    lengths: &'a [usize],
}

impl<'a> Inputs<'a> {
    /// Slice `i`
    pub fn get(&self, i: usize) -> Result<&'a [u8], u32> {
        match (self.pointers.get(i), self.lengths.get(i)) {
            (Some(&pointer), Some(&length)) => Ok(unsafe { slice::from_raw_parts(pointer, length) }),
            _ => outside(),
        }
    }

    /// Slice `i` as an `N`-byte array
    pub fn array<const N: usize>(&self, i: usize) -> Result<[u8; N], u32> {
        Ok(self.get(i)?.try_into().unwrap_or_else(|_| outside()))
    }

}

/// The result of one call, written into the caller's buffer after its eight-byte length
pub struct Output<'a> {
    bytes: &'a mut [u8],
    length: usize,
}

impl<'a> Output<'a> {
    fn new(bytes: &'a mut [u8]) -> Self {
        Self { bytes, length: 8 }
    }

    /// Append `bytes` (the caller's buffer holds the result: `ValidCall`)
    pub fn push(&mut self, bytes: &[u8]) -> Result<(), u32> {
        let end = self.length + bytes.len();
        self.bytes[self.length..end].copy_from_slice(bytes);
        self.length = end;
        Ok(())
    }

    /// Write the result's length before it
    fn finish(&mut self) {
        let length = (self.length - 8) as u64;
        self.bytes[..8].copy_from_slice(&length.to_le_bytes());
    }
}

impl fmt::Write for Output<'_> {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        self.push(text.as_bytes()).map_err(|_| fmt::Error)
    }
}

/// Run `body` on the call's slices and write its result out: the shared body of every
/// one-function entry point. The allocator serves from `heap_len` bytes at `heap`, from their
/// start, and the system random source starts empty, on every call. On success the output holds
/// the result's length, eight bytes little-endian, then the result; on failure nothing is written.
///
/// # Safety
///
/// `input` and `input_lens` must be non-null, aligned and readable for `num_inputs` words each,
/// each slice readable for its length at a non-null address and a value of its argument (as
/// `P256/Spec/Program.lean`'s `ValidCall` states), `output` writable for `capacity` bytes, at
/// least 8 more than the result, and `heap` writable for `heap_len` bytes (or `heap_len` zero),
/// at least what the call allocates, overlapping none of them.
pub unsafe fn call(
    input: *const *const u8,
    num_inputs: usize,
    input_lens: *const usize,
    output: *mut u8,
    capacity: usize,
    heap: *mut u8,
    heap_len: usize,
    body: fn(&Inputs, &mut Output) -> Result<(), u32>,
) -> u32 {
    crate::arena::reset(heap, heap_len);
    set_random(&[]);
    let inputs = Inputs {
        pointers: unsafe { slice::from_raw_parts(input, num_inputs) },
        lengths: unsafe { slice::from_raw_parts(input_lens, num_inputs) },
    };
    let mut result = Output::new(unsafe { slice::from_raw_parts_mut(output, capacity) });
    match body(&inputs, &mut result) {
        Ok(()) => {
            result.finish();
            OK
        }
        Err(status) => status,
    }
}

/// A random-number generator that hands out the caller's bytes in order. A request for more
/// bytes than remain fails, consuming nothing.
pub struct ByteRng<'a> {
    bytes: &'a [u8],
}

impl<'a> ByteRng<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { bytes }
    }

    fn take(&mut self, count: usize) -> Result<&'a [u8], Exhausted> {
        if self.bytes.len() < count {
            return Err(Exhausted);
        }
        let (taken, rest) = self.bytes.split_at(count);
        self.bytes = rest;
        Ok(taken)
    }
}

/// The caller's random bytes ran out
#[derive(Debug)]
pub struct Exhausted;

impl fmt::Display for Exhausted {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("random bytes exhausted")
    }
}

impl core::error::Error for Exhausted {}

impl rand_core::TryRng for ByteRng<'_> {
    type Error = Exhausted;

    fn try_next_u32(&mut self) -> Result<u32, Exhausted> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap_or_default()))
    }

    fn try_next_u64(&mut self) -> Result<u64, Exhausted> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap_or_default()))
    }

    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Exhausted> {
        dst.copy_from_slice(self.take(dst.len())?);
        Ok(())
    }
}

impl rand_core::TryCryptoRng for ByteRng<'_> {}

#[cfg(not(test))]
mod random {
    /// The caller's bytes that getrandom's custom backend hands out, as an address and a length
    static mut RANDOM: (usize, usize) = (0, 0);

    pub fn set(bytes: &[u8]) {
        unsafe { RANDOM = (bytes.as_ptr() as usize, bytes.len()) };
    }

    pub fn take(count: usize) -> Option<*const u8> {
        let (address, length) = unsafe { RANDOM };
        if length < count {
            return None;
        }
        unsafe { RANDOM = (address + count, length - count) };
        Some(address as *const u8)
    }
}

#[cfg(test)]
mod random {
    extern crate std;
    use std::cell::Cell;

    std::thread_local! {
        static RANDOM: Cell<(usize, usize)> = const { Cell::new((0, 0)) };
    }

    pub fn set(bytes: &[u8]) {
        RANDOM.set((bytes.as_ptr() as usize, bytes.len()));
    }

    pub fn take(count: usize) -> Option<*const u8> {
        let (address, length) = RANDOM.get();
        if length < count {
            return None;
        }
        RANDOM.set((address + count, length - count));
        Some(address as *const u8)
    }
}

/// Make `bytes` the system random source for the rest of this call
pub fn set_random(bytes: &[u8]) {
    random::set(bytes);
}

/// getrandom's custom backend (`getrandom_backend = "custom"`, `.cargo/config.toml`): fill `dest`
/// with the next `len` bytes of the caller's random bytes, or fail, consuming nothing, if fewer
/// remain
#[unsafe(no_mangle)]
unsafe extern "Rust" fn __getrandom_v03_custom(dest: *mut u8, len: usize) -> Result<(), getrandom::Error> {
    let source = random::take(len).ok_or(getrandom::Error::UNSUPPORTED)?;
    unsafe { core::ptr::copy_nonoverlapping(source, dest, len) };
    Ok(())
}
