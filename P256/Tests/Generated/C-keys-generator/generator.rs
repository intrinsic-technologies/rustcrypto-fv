//! The generator of `P256/Tests/Generated/C-keys-cases.txt`: the cases of `cases.txt` run natively
//! through the five key entry points (`P256/program/src/keys.rs`). `generate.sh` installs this
//! file as a test module of a scratch copy of `P256/program` and runs it.
//! A call that panics in `abi::outside()` (outside the entry's contract) is left out of the table.
//!
//! `cases.txt` holds `input <name> <hex>` lines, copied as they are, and `case <entry>
//! <names> <label>` lines, `names` the inputs joined by `+`. A `host` case is run and written as
//! `case <entry> <names> <status> host <result hex>`; a `crate-bug:<theorem>` case carries
//! the standard's status and result after its label, which are written instead, since the crate's
//! are wrong there. `-` stands for an empty field.

extern crate std;
use std::{collections::HashMap, format, string::String, vec, vec::Vec};

use crate::entry_points::{Entry, by_name};

fn unhex(text: &str) -> Vec<u8> {
    if text == "-" {
        return Vec::new();
    }
    (0..text.len()).step_by(2).map(|i| u8::from_str_radix(&text[i..i + 2], 16).unwrap()).collect()
}

fn hex(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        return String::from("-");
    }
    bytes.iter().map(|b| format!("{b:02X}")).collect()
}

/// Call `entry` on `slices` with a heap: the status and, on success, the result; `None` when the
/// call panics in `abi::outside()`
fn call(entry: Entry, slices: &[Vec<u8>]) -> Option<(u32, Vec<u8>)> {
    let run = || {
        let pointers: Vec<*const u8> =
            slices.iter().map(|s| if s.is_empty() { 1 as *const u8 } else { s.as_ptr() }).collect();
        let lengths: Vec<usize> = slices.iter().map(Vec::len).collect();
        let mut output = vec![0xa5u8; 8 + 4096];
        let mut heap = vec![0u8; 1 << 20];
        let capacity = output.len();
        let status = unsafe {
            entry(pointers.as_ptr(), slices.len(), lengths.as_ptr(), output.as_mut_ptr(), capacity, heap.as_mut_ptr(), heap.len())
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

/// Read `C_KEYS_CASES` and write the table to `C_KEYS_VECTORS`
#[test]
#[ignore]
fn generate() {
    let text = std::fs::read_to_string(std::env::var("C_KEYS_CASES").unwrap()).unwrap();
    let mut pool: HashMap<String, Vec<u8>> = HashMap::new();
    let mut out = String::new();
    for line in text.lines() {
        let fields: Vec<&str> = line.split(' ').collect();
        match fields.as_slice() {
            ["input", name, value] => {
                assert!(pool.insert(String::from(*name), unhex(value)).is_none(), "{name}");
                out += &format!("{line}\n");
            }
            ["case", name, names, label, rest @ ..] => {
                let (status, result) = if *label == "host" {
                    assert!(rest.is_empty(), "{line}");
                    let slices: Vec<Vec<u8>> = if *names == "-" {
                        Vec::new()
                    } else {
                        names.split('+').map(|name| pool[name].clone()).collect()
                    };
                    let entry = by_name(name).unwrap_or_else(|| panic!("{line}"));
                    let Some((status, result)) = call(entry, &slices) else { continue };
                    (format!("{status}"), hex(&result))
                } else {
                    assert!(label.starts_with("crate-bug:") && rest.len() == 2, "{line}");
                    (String::from(rest[0]), String::from(rest[1]))
                };
                out += &format!("case {name} {names} {status} {label} {result}\n");
            }
            _ => panic!("bad line {line}"),
        }
    }
    std::fs::write(std::env::var("C_KEYS_VECTORS").unwrap(), out).unwrap();
}
