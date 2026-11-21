//! The generator of `P256/Tests/Generated/B-points.txt`: calls of `ProjectivePoint::add`'s entry
//! point, run natively, written as `entry inputs status result` (`-` no slices, `~` an empty
//! slice or result). `generate.sh` installs this file as a test module of a scratch copy of
//! `P256/program` and runs it.
//! A call that panics in `abi::outside()` (outside the entry's contract) is left out of the table.

extern crate std;
use crate::entry_points::by_name;
use std::{format, string::String, vec, vec::Vec};

/// Call the entry point `name` on `args` with a heap: the status and, on success, the result;
/// `None` when the call panics in `abi::outside()`
fn call(name: &str, args: &[Vec<u8>]) -> Option<(u32, Vec<u8>)> {
    let entry = by_name(name).unwrap_or_else(|| panic!("no entry point {name}"));
    let run = || {
        let pointers: Vec<*const u8> =
            args.iter().map(|a| if a.is_empty() { [0u8; 1].as_ptr() } else { a.as_ptr() }).collect();
        let lengths: Vec<usize> = args.iter().map(Vec::len).collect();
        let mut output = vec![0xa5u8; 8 + 16384];
        let mut heap = vec![0u8; HEAP_BYTES];
        let capacity = output.len();
        let status = unsafe {
            entry(pointers.as_ptr(), args.len(), lengths.as_ptr(), output.as_mut_ptr(), capacity, heap.as_mut_ptr(), heap.len())
        };
        if status != 0 {
            return (status, Vec::new());
        }
        let length = u64::from_le_bytes(output[..8].try_into().unwrap()) as usize;
        (status, output[8..8 + length].to_vec())
    };
    if outside(|| {
        run();
    }) {
        return None;
    }
    Some(run())
}

/// Whether `body` panics in `abi::outside()` (the panic's location is in src/abi.rs). A panic
/// cannot unwind out of an `extern "C"` entry point (it aborts), so `body` runs in a forked child.
fn outside(body: impl FnOnce()) -> bool {
    unsafe extern "C" {
        fn fork() -> i32;
        fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
        fn _exit(status: i32) -> !;
    }
    let pid = unsafe { fork() };
    assert!(pid >= 0, "fork failed");
    if pid == 0 {
        std::panic::set_hook(std::boxed::Box::new(|info| {
            let outside = info.location().is_some_and(|l| l.file().ends_with("src/abi.rs"));
            unsafe { _exit(if outside { 3 } else { 4 }) }
        }));
        body();
        unsafe { _exit(0) }
    }
    let mut status = 0;
    assert_eq!(unsafe { waitpid(pid, &mut status, 0) }, pid);
    status == 3 << 8
}

/// The heap every call gets (the native build allocates from Rust's own allocator)
const HEAP_BYTES: usize = 1 << 16;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn be(text: &str) -> Vec<u8> {
    (0..text.len() / 2).map(|i| u8::from_str_radix(&text[2 * i..2 * i + 2], 16).unwrap()).collect()
}

fn cat(parts: &[&[u8]]) -> Vec<u8> {
    parts.concat()
}

struct Writer(String);

impl Writer {
    /// The line of the entry point `name` called on `args`
    fn line(&mut self, name: &str, args: &[Vec<u8>]) {
        let Some((status, output)) = call(name, args) else { return };
        let inputs = if args.is_empty() {
            String::from("-")
        } else {
            args.iter().map(|a| if a.is_empty() { String::from("~") } else { hex(a) }).collect::<Vec<_>>().join(",")
        };
        let result = if output.is_empty() { String::from("~") } else { hex(&output) };
        self.0 += &format!("{name} {inputs} {status} {result}\n");
    }

    /// `name` on every combination of one candidate per argument kind
    fn product(&mut self, name: &str, kinds: &[&[Vec<u8>]]) {
        let mut combos: Vec<Vec<Vec<u8>>> = vec![Vec::new()];
        for kind in kinds {
            combos = combos.iter().flat_map(|c| kind.iter().map(move |v| [c.clone(), vec![v.clone()]].concat())).collect();
        }
        for args in combos {
            self.line(name, &args);
        }
    }

    /// Each entry of `names` in turn: on every combination of `kinds`, then on no slices
    fn each(&mut self, names: &[&str], kinds: &[&[Vec<u8>]]) {
        for name in names {
            self.product(name, kinds);
            self.line(name, &[]);
        }
    }
}

const GX: &str = "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296";
const GY: &str = "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5";
const G2X: &str = "7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978";
const G2Y: &str = "07775510db8ed040293d9ac69f7430dbba7dade63ce982299e04b79d227873d1";

/// `value` plus `small`, as 32 big-endian bytes, `value` below 2^256 − small
fn plus(value: &str, small: u8) -> Vec<u8> {
    let mut v = be(value);
    let mut carry = small as u16;
    for byte in v.iter_mut().rev() {
        let sum = *byte as u16 + carry;
        *byte = sum as u8;
        carry = sum >> 8;
    }
    v
}

/// Write the vectors to the file `B_POINTS_VECTORS` names
#[test]
#[ignore]
fn generate() {
    let mut w = Writer(String::new());
    let g = cat(&[&[4], &be(GX), &be(GY)]);
    let gc = cat(&[&[3], &be(GX)]);
    let g2 = cat(&[&[4], &be(G2X), &be(G2Y)]);
    let identity = vec![0u8];
    let off_curve = cat(&[&[4], &be(GX), &plus(GY, 1)]);
    let few: Vec<Vec<u8>> = vec![g, gc, g2, identity, off_curve];
    w.each(&["projectivePointAdd"], &[&few, &few]);
    std::fs::write(std::env::var("B_POINTS_VECTORS").unwrap(), w.0).unwrap();
}
