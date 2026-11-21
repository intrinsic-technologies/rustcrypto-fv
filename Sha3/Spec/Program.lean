import Prelude
import Standards.NIST.SHA3.Digest
import Sha3.Spec.Program.Extracted.Image

/-!
# Call semantics of the extracted entry points

`Sha3/program/src/lib.rs` exports seven System V entry points for each of the nine hasher types of
`sha3` 0.12.0 (`Sha3_224`, `Sha3_256`, `Sha3_384`, `Sha3_512`, `Keccak224`, `Keccak256`,
`Keccak384`, `Keccak512`, `Keccak256Full`), named `<prefix>_<form>` with the prefixes `sha3_224`,
`sha3_256`, `sha3_384`, `sha3_512`, `keccak224`, `keccak256`, `keccak384`, `keccak512` and
`keccak256_full`. Each is one `Routine` below, with its entry address, its stack budget (the
extraction's estimate) and its output size. The forms are `digest`, `digest_slices`, `reset` and
the two-output forms `fixed_finalize_into_reset`, `finalize_fixed_reset`,
`digest_finalize_into_reset` and `digest_finalize_reset`. No form returns a status.

The call predicates state what a call needs: `ValidDigestCall` for `digest`, `ValidCall` for
`digest_slices`, `ValidSplitCall` for `reset` and `ValidTwoOutputCall` for the two-output forms.
Every form but `digest` takes its input slices as a pointer table, a count and a length table
(`ValidInputSlices`). `readDigestOutput` and `readOutput` read an output buffer
back from final memory. The machine environment a call assumes is lean-x86's
`Prelude.SupportedIntegerMachineState` and `Prelude.MachineRamUnitStrideDecodable`.

The arguments of the two forms with theorems, the machine assumptions and the build are in
`Sha3/README.md`.
-/

namespace Sha3.Spec.Program

open Prelude X86 Standards.NIST

/-- An extracted entry point: its address, stack budget and output size -/
structure Routine where
  /-- Link-time address of the exported function -/
  entryAddress : BitVec 64
  /--
  Stack budget, in bytes below entry RSP: the extraction's estimate, which includes 128 bytes of
  slack (the target disables the red zone). `ValidCall` and its siblings require at least this
  much, and a caller may provide more.
  -/
  minStackBytes : Nat
  /-- Number of bytes the function writes to its output buffer in RCX (or RDX for `digest`) -/
  outputBytes : Nat

/-- `sha3_224_digest`: `Digest::digest` of the data, for `Sha3_224`; 28 output bytes -/
def sha3_224_digest : Routine where
  entryAddress := Extracted.sha3_224_digestAddress
  minStackBytes := Extracted.sha3_224_digestStackBytes.get (by decide)
  outputBytes := 28

/--
`sha3_224_digest_slices`: `Digest::new`, `Digest::update` per slice, `Digest::finalize`, for
`Sha3_224`; 28 output bytes
-/
def sha3_224_digest_slices : Routine where
  entryAddress := Extracted.sha3_224_digest_slicesAddress
  minStackBytes := Extracted.sha3_224_digest_slicesStackBytes.get (by decide)
  outputBytes := 28

/--
`sha3_224_reset`: `Update::update` per slice with `Reset::reset` after the first `split`, then
`FixedOutput::finalize_into`, for `Sha3_224`; 28 output bytes
-/
def sha3_224_reset : Routine where
  entryAddress := Extracted.sha3_224_resetAddress
  minStackBytes := Extracted.sha3_224_resetStackBytes.get (by decide)
  outputBytes := 28

/--
`sha3_224_fixed_finalize_into_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_into_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Sha3_224`; 28 output bytes at RCX and 28 at R9
-/
def sha3_224_fixed_finalize_into_reset : Routine where
  entryAddress := Extracted.sha3_224_fixed_finalize_into_resetAddress
  minStackBytes := Extracted.sha3_224_fixed_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 28

/--
`sha3_224_finalize_fixed_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_fixed_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Sha3_224`; 28 output bytes at RCX and 28 at R9
-/
def sha3_224_finalize_fixed_reset : Routine where
  entryAddress := Extracted.sha3_224_finalize_fixed_resetAddress
  minStackBytes := Extracted.sha3_224_finalize_fixed_resetStackBytes.get (by decide)
  outputBytes := 28

/--
`sha3_224_digest_finalize_into_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_into_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Sha3_224`; 28 output
bytes at RCX and 28 at R9
-/
def sha3_224_digest_finalize_into_reset : Routine where
  entryAddress := Extracted.sha3_224_digest_finalize_into_resetAddress
  minStackBytes := Extracted.sha3_224_digest_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 28

/--
`sha3_224_digest_finalize_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Sha3_224`; 28 output
bytes at RCX and 28 at R9
-/
def sha3_224_digest_finalize_reset : Routine where
  entryAddress := Extracted.sha3_224_digest_finalize_resetAddress
  minStackBytes := Extracted.sha3_224_digest_finalize_resetStackBytes.get (by decide)
  outputBytes := 28

/-- `sha3_256_digest`: `Digest::digest` of the data, for `Sha3_256`; 32 output bytes -/
def sha3_256_digest : Routine where
  entryAddress := Extracted.sha3_256_digestAddress
  minStackBytes := Extracted.sha3_256_digestStackBytes.get (by decide)
  outputBytes := 32

/--
`sha3_256_digest_slices`: `Digest::new`, `Digest::update` per slice, `Digest::finalize`, for
`Sha3_256`; 32 output bytes
-/
def sha3_256_digest_slices : Routine where
  entryAddress := Extracted.sha3_256_digest_slicesAddress
  minStackBytes := Extracted.sha3_256_digest_slicesStackBytes.get (by decide)
  outputBytes := 32

/--
`sha3_256_reset`: `Update::update` per slice with `Reset::reset` after the first `split`, then
`FixedOutput::finalize_into`, for `Sha3_256`; 32 output bytes
-/
def sha3_256_reset : Routine where
  entryAddress := Extracted.sha3_256_resetAddress
  minStackBytes := Extracted.sha3_256_resetStackBytes.get (by decide)
  outputBytes := 32

/--
`sha3_256_fixed_finalize_into_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_into_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Sha3_256`; 32 output bytes at RCX and 32 at R9
-/
def sha3_256_fixed_finalize_into_reset : Routine where
  entryAddress := Extracted.sha3_256_fixed_finalize_into_resetAddress
  minStackBytes := Extracted.sha3_256_fixed_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 32

/--
`sha3_256_finalize_fixed_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_fixed_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Sha3_256`; 32 output bytes at RCX and 32 at R9
-/
def sha3_256_finalize_fixed_reset : Routine where
  entryAddress := Extracted.sha3_256_finalize_fixed_resetAddress
  minStackBytes := Extracted.sha3_256_finalize_fixed_resetStackBytes.get (by decide)
  outputBytes := 32

/--
`sha3_256_digest_finalize_into_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_into_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Sha3_256`; 32 output
bytes at RCX and 32 at R9
-/
def sha3_256_digest_finalize_into_reset : Routine where
  entryAddress := Extracted.sha3_256_digest_finalize_into_resetAddress
  minStackBytes := Extracted.sha3_256_digest_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 32

/--
`sha3_256_digest_finalize_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Sha3_256`; 32 output
bytes at RCX and 32 at R9
-/
def sha3_256_digest_finalize_reset : Routine where
  entryAddress := Extracted.sha3_256_digest_finalize_resetAddress
  minStackBytes := Extracted.sha3_256_digest_finalize_resetStackBytes.get (by decide)
  outputBytes := 32

/-- `sha3_384_digest`: `Digest::digest` of the data, for `Sha3_384`; 48 output bytes -/
def sha3_384_digest : Routine where
  entryAddress := Extracted.sha3_384_digestAddress
  minStackBytes := Extracted.sha3_384_digestStackBytes.get (by decide)
  outputBytes := 48

/--
`sha3_384_digest_slices`: `Digest::new`, `Digest::update` per slice, `Digest::finalize`, for
`Sha3_384`; 48 output bytes
-/
def sha3_384_digest_slices : Routine where
  entryAddress := Extracted.sha3_384_digest_slicesAddress
  minStackBytes := Extracted.sha3_384_digest_slicesStackBytes.get (by decide)
  outputBytes := 48

/--
`sha3_384_reset`: `Update::update` per slice with `Reset::reset` after the first `split`, then
`FixedOutput::finalize_into`, for `Sha3_384`; 48 output bytes
-/
def sha3_384_reset : Routine where
  entryAddress := Extracted.sha3_384_resetAddress
  minStackBytes := Extracted.sha3_384_resetStackBytes.get (by decide)
  outputBytes := 48

/--
`sha3_384_fixed_finalize_into_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_into_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Sha3_384`; 48 output bytes at RCX and 48 at R9
-/
def sha3_384_fixed_finalize_into_reset : Routine where
  entryAddress := Extracted.sha3_384_fixed_finalize_into_resetAddress
  minStackBytes := Extracted.sha3_384_fixed_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 48

/--
`sha3_384_finalize_fixed_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_fixed_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Sha3_384`; 48 output bytes at RCX and 48 at R9
-/
def sha3_384_finalize_fixed_reset : Routine where
  entryAddress := Extracted.sha3_384_finalize_fixed_resetAddress
  minStackBytes := Extracted.sha3_384_finalize_fixed_resetStackBytes.get (by decide)
  outputBytes := 48

/--
`sha3_384_digest_finalize_into_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_into_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Sha3_384`; 48 output
bytes at RCX and 48 at R9
-/
def sha3_384_digest_finalize_into_reset : Routine where
  entryAddress := Extracted.sha3_384_digest_finalize_into_resetAddress
  minStackBytes := Extracted.sha3_384_digest_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 48

/--
`sha3_384_digest_finalize_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Sha3_384`; 48 output
bytes at RCX and 48 at R9
-/
def sha3_384_digest_finalize_reset : Routine where
  entryAddress := Extracted.sha3_384_digest_finalize_resetAddress
  minStackBytes := Extracted.sha3_384_digest_finalize_resetStackBytes.get (by decide)
  outputBytes := 48

/-- `sha3_512_digest`: `Digest::digest` of the data, for `Sha3_512`; 64 output bytes -/
def sha3_512_digest : Routine where
  entryAddress := Extracted.sha3_512_digestAddress
  minStackBytes := Extracted.sha3_512_digestStackBytes.get (by decide)
  outputBytes := 64

/--
`sha3_512_digest_slices`: `Digest::new`, `Digest::update` per slice, `Digest::finalize`, for
`Sha3_512`; 64 output bytes
-/
def sha3_512_digest_slices : Routine where
  entryAddress := Extracted.sha3_512_digest_slicesAddress
  minStackBytes := Extracted.sha3_512_digest_slicesStackBytes.get (by decide)
  outputBytes := 64

/--
`sha3_512_reset`: `Update::update` per slice with `Reset::reset` after the first `split`, then
`FixedOutput::finalize_into`, for `Sha3_512`; 64 output bytes
-/
def sha3_512_reset : Routine where
  entryAddress := Extracted.sha3_512_resetAddress
  minStackBytes := Extracted.sha3_512_resetStackBytes.get (by decide)
  outputBytes := 64

/--
`sha3_512_fixed_finalize_into_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_into_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Sha3_512`; 64 output bytes at RCX and 64 at R9
-/
def sha3_512_fixed_finalize_into_reset : Routine where
  entryAddress := Extracted.sha3_512_fixed_finalize_into_resetAddress
  minStackBytes := Extracted.sha3_512_fixed_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 64

/--
`sha3_512_finalize_fixed_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_fixed_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Sha3_512`; 64 output bytes at RCX and 64 at R9
-/
def sha3_512_finalize_fixed_reset : Routine where
  entryAddress := Extracted.sha3_512_finalize_fixed_resetAddress
  minStackBytes := Extracted.sha3_512_finalize_fixed_resetStackBytes.get (by decide)
  outputBytes := 64

/--
`sha3_512_digest_finalize_into_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_into_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Sha3_512`; 64 output
bytes at RCX and 64 at R9
-/
def sha3_512_digest_finalize_into_reset : Routine where
  entryAddress := Extracted.sha3_512_digest_finalize_into_resetAddress
  minStackBytes := Extracted.sha3_512_digest_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 64

/--
`sha3_512_digest_finalize_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Sha3_512`; 64 output
bytes at RCX and 64 at R9
-/
def sha3_512_digest_finalize_reset : Routine where
  entryAddress := Extracted.sha3_512_digest_finalize_resetAddress
  minStackBytes := Extracted.sha3_512_digest_finalize_resetStackBytes.get (by decide)
  outputBytes := 64

/-- `keccak224_digest`: `Digest::digest` of the data, for `Keccak224`; 28 output bytes -/
def keccak224_digest : Routine where
  entryAddress := Extracted.keccak224_digestAddress
  minStackBytes := Extracted.keccak224_digestStackBytes.get (by decide)
  outputBytes := 28

/--
`keccak224_digest_slices`: `Digest::new`, `Digest::update` per slice, `Digest::finalize`, for
`Keccak224`; 28 output bytes
-/
def keccak224_digest_slices : Routine where
  entryAddress := Extracted.keccak224_digest_slicesAddress
  minStackBytes := Extracted.keccak224_digest_slicesStackBytes.get (by decide)
  outputBytes := 28

/--
`keccak224_reset`: `Update::update` per slice with `Reset::reset` after the first `split`, then
`FixedOutput::finalize_into`, for `Keccak224`; 28 output bytes
-/
def keccak224_reset : Routine where
  entryAddress := Extracted.keccak224_resetAddress
  minStackBytes := Extracted.keccak224_resetStackBytes.get (by decide)
  outputBytes := 28

/--
`keccak224_fixed_finalize_into_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_into_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Keccak224`; 28 output bytes at RCX and 28 at R9
-/
def keccak224_fixed_finalize_into_reset : Routine where
  entryAddress := Extracted.keccak224_fixed_finalize_into_resetAddress
  minStackBytes := Extracted.keccak224_fixed_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 28

/--
`keccak224_finalize_fixed_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_fixed_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Keccak224`; 28 output bytes at RCX and 28 at R9
-/
def keccak224_finalize_fixed_reset : Routine where
  entryAddress := Extracted.keccak224_finalize_fixed_resetAddress
  minStackBytes := Extracted.keccak224_finalize_fixed_resetStackBytes.get (by decide)
  outputBytes := 28

/--
`keccak224_digest_finalize_into_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_into_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Keccak224`; 28 output
bytes at RCX and 28 at R9
-/
def keccak224_digest_finalize_into_reset : Routine where
  entryAddress := Extracted.keccak224_digest_finalize_into_resetAddress
  minStackBytes := Extracted.keccak224_digest_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 28

/--
`keccak224_digest_finalize_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Keccak224`; 28 output
bytes at RCX and 28 at R9
-/
def keccak224_digest_finalize_reset : Routine where
  entryAddress := Extracted.keccak224_digest_finalize_resetAddress
  minStackBytes := Extracted.keccak224_digest_finalize_resetStackBytes.get (by decide)
  outputBytes := 28

/-- `keccak256_digest`: `Digest::digest` of the data, for `Keccak256`; 32 output bytes -/
def keccak256_digest : Routine where
  entryAddress := Extracted.keccak256_digestAddress
  minStackBytes := Extracted.keccak256_digestStackBytes.get (by decide)
  outputBytes := 32

/--
`keccak256_digest_slices`: `Digest::new`, `Digest::update` per slice, `Digest::finalize`, for
`Keccak256`; 32 output bytes
-/
def keccak256_digest_slices : Routine where
  entryAddress := Extracted.keccak256_digest_slicesAddress
  minStackBytes := Extracted.keccak256_digest_slicesStackBytes.get (by decide)
  outputBytes := 32

/--
`keccak256_reset`: `Update::update` per slice with `Reset::reset` after the first `split`, then
`FixedOutput::finalize_into`, for `Keccak256`; 32 output bytes
-/
def keccak256_reset : Routine where
  entryAddress := Extracted.keccak256_resetAddress
  minStackBytes := Extracted.keccak256_resetStackBytes.get (by decide)
  outputBytes := 32

/--
`keccak256_fixed_finalize_into_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_into_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Keccak256`; 32 output bytes at RCX and 32 at R9
-/
def keccak256_fixed_finalize_into_reset : Routine where
  entryAddress := Extracted.keccak256_fixed_finalize_into_resetAddress
  minStackBytes := Extracted.keccak256_fixed_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 32

/--
`keccak256_finalize_fixed_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_fixed_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Keccak256`; 32 output bytes at RCX and 32 at R9
-/
def keccak256_finalize_fixed_reset : Routine where
  entryAddress := Extracted.keccak256_finalize_fixed_resetAddress
  minStackBytes := Extracted.keccak256_finalize_fixed_resetStackBytes.get (by decide)
  outputBytes := 32

/--
`keccak256_digest_finalize_into_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_into_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Keccak256`; 32 output
bytes at RCX and 32 at R9
-/
def keccak256_digest_finalize_into_reset : Routine where
  entryAddress := Extracted.keccak256_digest_finalize_into_resetAddress
  minStackBytes := Extracted.keccak256_digest_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 32

/--
`keccak256_digest_finalize_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Keccak256`; 32 output
bytes at RCX and 32 at R9
-/
def keccak256_digest_finalize_reset : Routine where
  entryAddress := Extracted.keccak256_digest_finalize_resetAddress
  minStackBytes := Extracted.keccak256_digest_finalize_resetStackBytes.get (by decide)
  outputBytes := 32

/-- `keccak384_digest`: `Digest::digest` of the data, for `Keccak384`; 48 output bytes -/
def keccak384_digest : Routine where
  entryAddress := Extracted.keccak384_digestAddress
  minStackBytes := Extracted.keccak384_digestStackBytes.get (by decide)
  outputBytes := 48

/--
`keccak384_digest_slices`: `Digest::new`, `Digest::update` per slice, `Digest::finalize`, for
`Keccak384`; 48 output bytes
-/
def keccak384_digest_slices : Routine where
  entryAddress := Extracted.keccak384_digest_slicesAddress
  minStackBytes := Extracted.keccak384_digest_slicesStackBytes.get (by decide)
  outputBytes := 48

/--
`keccak384_reset`: `Update::update` per slice with `Reset::reset` after the first `split`, then
`FixedOutput::finalize_into`, for `Keccak384`; 48 output bytes
-/
def keccak384_reset : Routine where
  entryAddress := Extracted.keccak384_resetAddress
  minStackBytes := Extracted.keccak384_resetStackBytes.get (by decide)
  outputBytes := 48

/--
`keccak384_fixed_finalize_into_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_into_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Keccak384`; 48 output bytes at RCX and 48 at R9
-/
def keccak384_fixed_finalize_into_reset : Routine where
  entryAddress := Extracted.keccak384_fixed_finalize_into_resetAddress
  minStackBytes := Extracted.keccak384_fixed_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 48

/--
`keccak384_finalize_fixed_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_fixed_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Keccak384`; 48 output bytes at RCX and 48 at R9
-/
def keccak384_finalize_fixed_reset : Routine where
  entryAddress := Extracted.keccak384_finalize_fixed_resetAddress
  minStackBytes := Extracted.keccak384_finalize_fixed_resetStackBytes.get (by decide)
  outputBytes := 48

/--
`keccak384_digest_finalize_into_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_into_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Keccak384`; 48 output
bytes at RCX and 48 at R9
-/
def keccak384_digest_finalize_into_reset : Routine where
  entryAddress := Extracted.keccak384_digest_finalize_into_resetAddress
  minStackBytes := Extracted.keccak384_digest_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 48

/--
`keccak384_digest_finalize_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Keccak384`; 48 output
bytes at RCX and 48 at R9
-/
def keccak384_digest_finalize_reset : Routine where
  entryAddress := Extracted.keccak384_digest_finalize_resetAddress
  minStackBytes := Extracted.keccak384_digest_finalize_resetStackBytes.get (by decide)
  outputBytes := 48

/-- `keccak512_digest`: `Digest::digest` of the data, for `Keccak512`; 64 output bytes -/
def keccak512_digest : Routine where
  entryAddress := Extracted.keccak512_digestAddress
  minStackBytes := Extracted.keccak512_digestStackBytes.get (by decide)
  outputBytes := 64

/--
`keccak512_digest_slices`: `Digest::new`, `Digest::update` per slice, `Digest::finalize`, for
`Keccak512`; 64 output bytes
-/
def keccak512_digest_slices : Routine where
  entryAddress := Extracted.keccak512_digest_slicesAddress
  minStackBytes := Extracted.keccak512_digest_slicesStackBytes.get (by decide)
  outputBytes := 64

/--
`keccak512_reset`: `Update::update` per slice with `Reset::reset` after the first `split`, then
`FixedOutput::finalize_into`, for `Keccak512`; 64 output bytes
-/
def keccak512_reset : Routine where
  entryAddress := Extracted.keccak512_resetAddress
  minStackBytes := Extracted.keccak512_resetStackBytes.get (by decide)
  outputBytes := 64

/--
`keccak512_fixed_finalize_into_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_into_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Keccak512`; 64 output bytes at RCX and 64 at R9
-/
def keccak512_fixed_finalize_into_reset : Routine where
  entryAddress := Extracted.keccak512_fixed_finalize_into_resetAddress
  minStackBytes := Extracted.keccak512_fixed_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 64

/--
`keccak512_finalize_fixed_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_fixed_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Keccak512`; 64 output bytes at RCX and 64 at R9
-/
def keccak512_finalize_fixed_reset : Routine where
  entryAddress := Extracted.keccak512_finalize_fixed_resetAddress
  minStackBytes := Extracted.keccak512_finalize_fixed_resetStackBytes.get (by decide)
  outputBytes := 64

/--
`keccak512_digest_finalize_into_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_into_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Keccak512`; 64 output
bytes at RCX and 64 at R9
-/
def keccak512_digest_finalize_into_reset : Routine where
  entryAddress := Extracted.keccak512_digest_finalize_into_resetAddress
  minStackBytes := Extracted.keccak512_digest_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 64

/--
`keccak512_digest_finalize_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Keccak512`; 64 output
bytes at RCX and 64 at R9
-/
def keccak512_digest_finalize_reset : Routine where
  entryAddress := Extracted.keccak512_digest_finalize_resetAddress
  minStackBytes := Extracted.keccak512_digest_finalize_resetStackBytes.get (by decide)
  outputBytes := 64

/-- `keccak256_full_digest`: `Digest::digest` of the data, for `Keccak256Full`; 200 output bytes -/
def keccak256_full_digest : Routine where
  entryAddress := Extracted.keccak256_full_digestAddress
  minStackBytes := Extracted.keccak256_full_digestStackBytes.get (by decide)
  outputBytes := 200

/--
`keccak256_full_digest_slices`: `Digest::new`, `Digest::update` per slice, `Digest::finalize`, for
`Keccak256Full`; 200 output bytes
-/
def keccak256_full_digest_slices : Routine where
  entryAddress := Extracted.keccak256_full_digest_slicesAddress
  minStackBytes := Extracted.keccak256_full_digest_slicesStackBytes.get (by decide)
  outputBytes := 200

/--
`keccak256_full_reset`: `Update::update` per slice with `Reset::reset` after the first `split`, then
`FixedOutput::finalize_into`, for `Keccak256Full`; 200 output bytes
-/
def keccak256_full_reset : Routine where
  entryAddress := Extracted.keccak256_full_resetAddress
  minStackBytes := Extracted.keccak256_full_resetStackBytes.get (by decide)
  outputBytes := 200

/--
`keccak256_full_fixed_finalize_into_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_into_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Keccak256Full`; 200 output bytes at RCX and 200 at R9
-/
def keccak256_full_fixed_finalize_into_reset : Routine where
  entryAddress := Extracted.keccak256_full_fixed_finalize_into_resetAddress
  minStackBytes := Extracted.keccak256_full_fixed_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 200

/--
`keccak256_full_finalize_fixed_reset`: `Default::default`, `Update::update` per slice,
`FixedOutputReset::finalize_fixed_reset` after the first `split` into the first output,
`Update::update` per remaining slice, then `FixedOutput::finalize_into` into the second output, for
`Keccak256Full`; 200 output bytes at RCX and 200 at R9
-/
def keccak256_full_finalize_fixed_reset : Routine where
  entryAddress := Extracted.keccak256_full_finalize_fixed_resetAddress
  minStackBytes := Extracted.keccak256_full_finalize_fixed_resetStackBytes.get (by decide)
  outputBytes := 200

/--
`keccak256_full_digest_finalize_into_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_into_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Keccak256Full`; 200
output bytes at RCX and 200 at R9
-/
def keccak256_full_digest_finalize_into_reset : Routine where
  entryAddress := Extracted.keccak256_full_digest_finalize_into_resetAddress
  minStackBytes := Extracted.keccak256_full_digest_finalize_into_resetStackBytes.get (by decide)
  outputBytes := 200

/--
`keccak256_full_digest_finalize_reset`: `Digest::new`, `Digest::update` per slice,
`Digest::finalize_reset` after the first `split` into the first output, `Digest::update` per
remaining slice, then `Digest::finalize_into` into the second output, for `Keccak256Full`; 200
output bytes at RCX and 200 at R9
-/
def keccak256_full_digest_finalize_reset : Routine where
  entryAddress := Extracted.keccak256_full_digest_finalize_resetAddress
  minStackBytes := Extracted.keccak256_full_digest_finalize_resetStackBytes.get (by decide)
  outputBytes := 200

/-- One input slice of a call: the address in its pointer-table entry, and the bytes there -/
structure Input where
  /-- Address of the slice's first byte, the word in its pointer-table entry -/
  address : BitVec 64
  /-- The slice's bytes in address order; their number is the word in its length-table entry -/
  bytes : ByteArray

/-- Memory region of the slice's bytes -/
def Input.region (input : Input) : MemoryRegion :=
  ⟨input.address.toNat, input.bytes.size⟩

/-- The message a call hashes: the bytes of its input slices, concatenated in order -/
def message (inputs : Array Input) : ByteArray :=
  inputs.foldl (fun message input => message ++ input.bytes) ByteArray.empty

/-- The direction flag is clear, so string instructions advance their pointers. -/
abbrev DirectionFlagUnset (s : Machine.RamState) : Prop :=
  RFLAGS.DirectionFlagClear s.RFLAGS

/-- Physical RAM contains every extracted byte -/
def ProgramLoaded (s : Machine.RamState) : Prop :=
  ∀ address byte, (address, byte) ∈ Extracted.programImage → s.external[address]? = some byte

/-- `address` is contained by an extracted section -/
def InProgram (address : BitVec 64) : Prop :=
  ∃ byte, (address, byte) ∈ Extracted.programImage

/-- `address` holds one of the page-table bytes that `Prelude.IdentityMappedMemory` fixes -/
def InPageTables (address : BitVec 64) : Prop :=
  ∃ region ∈ #v[(⟨0x1000, 8⟩ : MemoryRegion), ⟨0x2000, 32⟩], region.Contains address.toNat

/-- Table of `count` eight-byte slice addresses supplied through the System V RDI argument -/
def pointerTable (s : Machine.RamState) (count : Nat) : MemoryRegion :=
  registerRegion s .rdi (8 * count)

/-- Table of `count` eight-byte slice lengths supplied through the System V RDX argument -/
def lengthTable (s : Machine.RamState) (count : Nat) : MemoryRegion :=
  registerRegion s .rdx (8 * count)

/-- The eight-byte entry `i` of a table, counting from zero at the table's start -/
def tableEntry (table : MemoryRegion) (i : Nat) : MemoryRegion :=
  ⟨table.start + 8 * i, 8⟩

/--
Validity conditions on a table in memory: at a nonzero address, even when empty, and below 4 GiB.
The compiled code reads no entry when the count is 0.
-/
def ValidTable (table : MemoryRegion) : Prop :=
  table.start ≠ 0 ∧
  table.Bounded

/--
Validity conditions on input slice `i`: entry `i` of the pointer table holds its address, which is
nonzero even for an empty slice, entry `i` of the length table holds its length, and its bytes are
in memory at that address, below 4 GiB
-/
def ValidInputSlice (s : Machine.RamState) (inputs : Array Input) (i : Fin inputs.size) : Prop :=
  let input := inputs[i]
  input.address ≠ 0 ∧
  (tableEntry (pointerTable s inputs.size) i).Word64At s.external input.address ∧
  (tableEntry (lengthTable s inputs.size) i).Word64At s.external
    (BitVec.ofNat 64 input.bytes.size) ∧
  input.region.Bounded ∧
  input.region.HasBytes s.external input.bytes

/--
Validity conditions on the input slices of a call: the slice count in RSI, the pointer table at
RDI, the length table at RDX, and every slice they describe
-/
structure ValidInputSlices (s : Machine.RamState) (inputs : Array Input) : Prop where
  countArgumentMatchesInputs : (s.regValue .rsi).toNat = inputs.size
  pointerTableValid : ValidTable (pointerTable s inputs.size)
  lengthTableValid : ValidTable (lengthTable s inputs.size)
  inputsInMemory : ∀ i, ValidInputSlice s inputs i

/-- The data of a `digest` call, supplied through the System V RDI argument -/
def inputRegion (s : Machine.RamState) (data : ByteArray) : MemoryRegion :=
  registerRegion s .rdi data.size

/-- Output buffer of a `digest` call, supplied through the System V RDX argument -/
def digestOutputRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .rdx routine.outputBytes

/--
Output buffer of every form but `digest`, supplied through the System V RCX argument; the first
output of the two-output forms
-/
def outputRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .rcx routine.outputBytes

/--
Second output buffer of the two-output forms, supplied through the System V R9 argument; a buffer
of its own, which need not follow the first
-/
def secondOutputRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .r9 routine.outputBytes

/--
Validity conditions on a read-only input buffer in memory: at a nonzero address, even when empty,
below 4 GiB, and holding `bytes`
-/
def ValidInput (s : Machine.RamState) (region : MemoryRegion) (bytes : ByteArray) : Prop :=
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.HasBytes s.external bytes

/--
Validity conditions on an output buffer in memory: at a nonzero address, below 4 GiB, and
present
-/
def ValidOutput (s : Machine.RamState) (output : MemoryRegion) : Prop :=
  output.start ≠ 0 ∧
  output.Bounded ∧
  output.Allocated s.external

/-- The regions a call reads through its tables: both tables and every input slice -/
def readRegions (s : Machine.RamState) (inputs : Array Input) : List MemoryRegion :=
  pointerTable s inputs.size :: lengthTable s inputs.size :: (inputs.map Input.region).toList

/--
The regions a call writes are pairwise disjoint, and each avoids every region the call only
reads, the program, and the page tables. The regions the call only reads may overlap one another.
-/
def MemorySeparation (reads : List MemoryRegion) (writable : Vector MemoryRegion n) : Prop :=
  MemoryRegion.PairwiseDisjoint writable ∧
  ∀ region ∈ writable,
    (∀ read ∈ reads, read.Disjoint region) ∧
    region.Avoids fun address => InProgram address ∨ InPageTables address

/--
The return address in the slot at RSP is below the user address limit and outside the program
image
-/
def ValidReturnAddress (s : Machine.RamState) : Prop :=
  ∃ address, (Stack.returnSlot s).Word64At s.external address ∧
    address.toNat < userAddressLimit ∧
    ¬ InProgram address

/--
Validity conditions for a System V call to a `digest` routine with data `data`:
- input: the data's bytes at RDI, at a nonzero address even when empty (`ValidInput`); its length
  in RSI
- output: `routine.outputBytes` allocated bytes at RDX, at a nonzero address (`ValidOutput`)
- stack (`Stack.Valid`): the `routine.minStackBytes` bytes below RSP and the 8-byte return slot at
  RSP allocated, with no underflow; RSP is 8 more than a multiple of 16
- low 4 GiB: the data, the output and the stack region each end strictly below `userAddressLimit`
  (2^32)
- return address: the 8 bytes at RSP hold an address below 2^32 outside the program
- program: loaded at its link-time addresses, RIP at `routine.entryAddress`, the direction flag
  clear
- separation: the output and the stack region are pairwise disjoint, disjoint from the data, and
  avoid the program and the page tables
-/
structure ValidDigestCall (routine : Routine) (s : Machine.RamState) (data : ByteArray) :
    Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  atEntryPoint : s.RIP = routine.entryAddress
  lengthArgumentMatchesData : (s.regValue .rsi).toNat = data.size
  inputInMemory : ValidInput s (inputRegion s data) data
  outputInMemory : ValidOutput s (digestOutputRegion routine s)
  stackAvailable : Stack.Valid s routine.minStackBytes
  separation :
    MemorySeparation [inputRegion s data]
      #v[digestOutputRegion routine s, Stack.region s routine.minStackBytes]
  returnAddress : ValidReturnAddress s

/--
Validity conditions for a System V call to a `digest_slices` routine with input slices `inputs`:
- inputs (`ValidInputSlices`): the slice count in RSI; at RDI a table of the slices' 8-byte
  addresses and at RDX a table of their 8-byte lengths, both at nonzero addresses even when empty
  (`ValidTable`); each slice's bytes at its address, which is nonzero even for an empty slice
  (`ValidInputSlice`). The tables need not be 8-byte aligned.
- output: `routine.outputBytes` allocated bytes at RCX, at a nonzero address (`ValidOutput`)
- stack (`Stack.Valid`): the `routine.minStackBytes` bytes below RSP and the 8-byte return slot at
  RSP allocated, with no underflow; RSP is 8 more than a multiple of 16
- low 4 GiB: the tables, every slice, the output and the stack region each end strictly below
  `userAddressLimit` (2^32)
- return address: the 8 bytes at RSP hold an address below 2^32 outside the program
- program: loaded at its link-time addresses, RIP at `routine.entryAddress`, the direction flag
  clear
- separation: the output and the stack region are pairwise disjoint, disjoint from the tables and
  the slices, and avoid the program and the page tables; the tables and the slices may overlap one
  another
-/
structure ValidCall (routine : Routine) (s : Machine.RamState) (inputs : Array Input) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  atEntryPoint : s.RIP = routine.entryAddress
  inputSlices : ValidInputSlices s inputs
  outputInMemory : ValidOutput s (outputRegion routine s)
  stackAvailable : Stack.Valid s routine.minStackBytes
  separation :
    MemorySeparation (readRegions s inputs)
      #v[outputRegion routine s, Stack.region s routine.minStackBytes]
  returnAddress : ValidReturnAddress s

/--
Validity conditions for a System V call to a `reset` routine with input slices `inputs`, reset
after the first `split` (all of them when `split` exceeds their count): the slices described
through RDI, RSI and RDX, the output buffer at RCX, and `split` in R8. Each call starts from a new
hasher. The stack region may hold message-derived data afterwards.
-/
structure ValidSplitCall (routine : Routine) (s : Machine.RamState) (inputs : Array Input)
    (split : Nat) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  atEntryPoint : s.RIP = routine.entryAddress
  splitArgumentMatchesSplit : (s.regValue .r8).toNat = split
  inputSlices : ValidInputSlices s inputs
  outputInMemory : ValidOutput s (outputRegion routine s)
  stackAvailable : Stack.Valid s routine.minStackBytes
  separation :
    MemorySeparation (readRegions s inputs)
      #v[outputRegion routine s, Stack.region s routine.minStackBytes]
  returnAddress : ValidReturnAddress s

/--
Validity conditions for a System V call to a two-output routine (`fixed_finalize_into_reset`,
`finalize_fixed_reset`, `digest_finalize_into_reset` or `digest_finalize_reset`) with input slices
`inputs`, finalized and reset after the first `split` (all of them when `split` exceeds their
count): the slices described through RDI, RSI and RDX, the first output buffer at RCX, `split` in
R8, and the second output buffer at R9. Each call starts from a new hasher. The stack region may
hold message-derived data afterwards.
-/
structure ValidTwoOutputCall (routine : Routine) (s : Machine.RamState) (inputs : Array Input)
    (split : Nat) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  atEntryPoint : s.RIP = routine.entryAddress
  splitArgumentMatchesSplit : (s.regValue .r8).toNat = split
  inputSlices : ValidInputSlices s inputs
  outputInMemory : ValidOutput s (outputRegion routine s)
  secondOutputInMemory : ValidOutput s (secondOutputRegion routine s)
  stackAvailable : Stack.Valid s routine.minStackBytes
  separation :
    MemorySeparation (readRegions s inputs)
      #v[outputRegion routine s, secondOutputRegion routine s,
        Stack.region s routine.minStackBytes]
  returnAddress : ValidReturnAddress s

/--
Reads `count` bytes from final memory at the start of `region`, in address order. Returns `.ok` on
success or `.error (.unmappedMemory address)` if a byte is missing.
-/
def readBytes (region : MemoryRegion) (count : Nat) (final : Machine.RamState) :
    Except Machine.Fault (Vector UInt8 count) :=
  Vector.ofFnM fun i : Fin count =>
    let address := BitVec.ofNat 64 (region.start + i.val)
    match final.external[address]? with
    | some byte => .ok byte
    | none => .error (.unmappedMemory address)

/--
Reads `routine`'s output from final memory at the initial output buffer in RCX; the first output
of the two-output forms
-/
def readOutput (routine : Routine) (initial final : Machine.RamState) :
    Except Machine.Fault (Vector UInt8 routine.outputBytes) :=
  readBytes (outputRegion routine initial) routine.outputBytes final

/-- Reads a `digest` routine's output from final memory at the initial output buffer in RDX -/
def readDigestOutput (routine : Routine) (initial final : Machine.RamState) :
    Except Machine.Fault (Vector UInt8 routine.outputBytes) :=
  readBytes (digestOutputRegion routine initial) routine.outputBytes final

/--
The System V callee-saved general-purpose registers other than RSP, namely RBX, RBP and R12–R15,
retain their entry values. RSP is fixed by the return boundary of `Prelude.UniqueExecution`; the
x87 control word and the MXCSR control bits, also callee-saved, are not covered.
-/
def CalleeSavedRegistersUnchanged (initial final : Machine.RamState) : Prop :=
  ∀ register ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
    final.regValue register = initial.regValue register

end Sha3.Spec.Program
