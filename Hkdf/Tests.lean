import Hkdf.Spec.RFC5869
import Hkdf.Spec.Program
import Standards.Tests.Utilities

/-!
# `hkdf` tests

Checks of `Hkdf.Spec.RFC5869`, the crate's operations built on the RFC 5869 definitions, against the
crate's own test data, run by `cd Hkdf && lake test`. The RFC 5869 text and the Wycheproof JSON
files are the vectors of the shared definitions, tested in `Standards.RFC.HKDF`; this suite tests
what the crate layer adds: the optional salt, `from_prk`'s PRK length rule, the output length limit,
the order of the two checks, the specifications of the combined entry points (`extract_expand`,
`new_expand`, `finalize_expand`), and `Hkdf.Spec.Program.concatenation`, which joins the slices of
the theorems that take slices.

| Source                    | Vectors | Checks                                                  |
| ------------------------- | ------: | ------------------------------------------------------- |
| `rfc5869_sha256.blb`      |       3 | PRK of `extract`, salt as the crate's test passes it    |
|                           |         | and as `Some`; OKM of `expandFromPrk`                   |
| `wycheproof_sha256.blb`   |     102 | OKM of `expandFromPrk` from `extract`'s PRK; the 22     |
|                           |         | empty salts also as no salt; then, with one vector's    |
|                           |         | PRK, the first rejected PRK and output lengths          |
| `tests/tests.rs`          |       7 | the length rules of four tests, each with a control,    |
|                           |         | from A.1, after a check of the PRK's size               |
| `expand_multi_info`       |       2 | an output of zero bytes, accepted and empty             |
| `tests/tests.rs`          |       8 | `concatenation` of the slices of two multi-part tests   |
| `rfc5869_sha256.blb`      |       3 | OKM of the combined entry points' specifications, IKM   |
|                           |         | split into slices several ways (5 checks per vector:    |
|                           |         | 15), and the first rejected output length with controls |
|                           |         | (4)                                                     |

The two `.blb` files are unmodified copies of `tests/data/` of `hkdf` 0.13.0, in the `blobby` 0.4
format: https://github.com/RustCrypto/KDFs/tree/hkdf-v0.13.0/hkdf/tests/data

The two theorems are at SHA-256, and these checks run `Hkdf.Spec.RFC5869` at SHA-256 only, on the
crate's data for `tests/rfc5869.rs` and `tests/wycheproof.rs`, so they check `Hkdf.Spec.RFC5869` and
`Standards.RFC.HKDF` and say nothing about compiled code. The combined entry points' specifications
run on RFC 5869's vectors at SHA-256.

No published vector gives `expandFromPrk` a PRK of other than `HashLen` bytes, so longer PRKs, and
those longer than the hash's block that HMAC hashes, rest on the crate and on `Standards.RFC.HMAC`'s
tests of long keys; Wycheproof's salts of 65 and 80 bytes are such keys for `extract` at SHA-256. No
published vector gives a `None` salt at SHA-256; the crate stores A.3's `(0 octets)` salt as empty,
and its `rfc5869` test passes every empty stored salt as `None`. An empty salt keys HMAC as
`HashLen` zeros do. No published vector has an output of zero bytes: its expected value, the empty
string, is the first 0 octets of RFC 5869 §2.3's T, and `expand_multi_info` returns `Ok` after a
loop over no chunks. This suite imports `Hkdf.Spec.Program` for `concatenation` only and runs no
extracted code.
-/

namespace Hkdf.Tests

open Standards.RFC Standards.Tests Hkdf.Spec.RFC5869
open Hkdf.Spec.Program (Input concatenation)

private def vectors : System.FilePath := "Hkdf/Tests/Vectors"

/-- Reads a `blobby` variable-length quantity: big-endian 7-bit groups, a continuation adds one -/
private def readVlq (data : ByteArray) (position : Nat) : Nat × Nat := Id.run do
  let mut position := position
  let mut byte := data.get! position
  let mut value := (byte &&& 0x7f).toNat
  position := position + 1
  for _ in [0:3] do
    if byte &&& 0x80 == 0 then break
    byte := data.get! position
    value := ((value + 1) <<< 7) + (byte &&& 0x7f).toNat
    position := position + 1
  return (value, position)

/--
The blobs of a `blobby` 0.4 file: a header of blob and dedup counts, the dedup table, then each
blob, inline or as a dedup reference. Fails unless the blobs end exactly at the end of the file.
-/
private def blobs (path : System.FilePath) : IO (Array ByteArray) := do
  let data ← IO.FS.readBinFile path
  let (count, position) := readVlq data 0
  let (dedupCount, position) := readVlq data position
  let mut position := position
  let mut dedup := #[]
  for _ in [0:dedupCount] do
    let (length, next) := readVlq data position
    dedup := dedup.push (data.extract next (next + length))
    position := next + length
  let mut result := #[]
  for _ in [0:count] do
    let (value, next) := readVlq data position
    if value % 2 == 1 then
      check s!"{path}: dedup index in range" (value / 2 < dedup.size)
      result := result.push dedup[value / 2]!
      position := next
    else
      result := result.push (data.extract next (next + value / 2))
      position := next + value / 2
  check s!"{path}: blobs end at the end of the file" (position == data.size)
  return result

private def expectOk {ε : Type} [Repr ε] (label : String) (actual : Except ε ByteArray)
    (expected : ByteArray) : IO Unit :=
  match actual with
  | .ok bytes => expect label bytes expected
  | .error error => throw (IO.userError s!"{label}: rejected with {repr error}")

private def expectError {ε : Type} [Repr ε] [DecidableEq ε] (label : String)
    (actual : Except ε ByteArray) (expected : ε) : IO Unit :=
  match actual with
  | .ok _ => throw (IO.userError s!"{label}: accepted")
  | .error error => check s!"{label}: rejected with {repr error}" (decide (error = expected))

/--
RFC 5869's test cases as the crate stores them, fields `ikm, salt, info, prk, okm`: A.1–A.3 at
SHA-256. The crate's `tests/rfc5869.rs` passes an empty stored salt as `None`. A.3 has a salt of
0 octets, which the crate stores as empty.
-/
private def rfc5869 (H : HKDF.Hash) (name : String) (count withoutSaltCount : Nat) : IO Unit := do
  let file := s!"rfc5869_{name}.blb"
  let fields ← blobs (vectors / file)
  check s!"{file} holds {count} vectors of 5 fields" (fields.size == 5 * count)
  let mut withoutSalt := 0
  for i in [0:count] do
    let field := fun j => fields[5 * i + j]!
    let (ikm, salt, info, prk, okm) := (field 0, field 1, field 2, field 3, field 4)
    let given := if salt.isEmpty then none else some salt
    if given.isNone then withoutSalt := withoutSalt + 1
    expect s!"{file} vector {i} extract" (extract H given ikm) prk
    expect s!"{file} vector {i} extract with Some salt" (extract H (some salt) ikm) prk
    expectOk s!"{file} vector {i} expandFromPrk" (expandFromPrk H prk info okm.size) okm
  check s!"{file} has {withoutSaltCount} vectors without a salt" (withoutSalt == withoutSaltCount)
  IO.println s!"hkdf {file}: {count} vectors passed, {withoutSalt} of them without a salt"

/--
Wycheproof's valid HKDF vectors at one hash as the crate stores them, fields `ikm, salt, info,
okm`. The crate's `tests/wycheproof.rs` passes each salt as `Some`. Then, with the first vector's
PRK and info: a PRK of `HashLen - 1` bytes is rejected, and an output of `255 * HashLen + 1` bytes
is rejected by `expandFromPrk`. Their controls are the first vector itself, accepted
with the same PRK, info and salt, and the vectors of exactly `255 * HashLen` bytes, accepted.
-/
private def wycheproof (H : HKDF.Hash) (name : String) (count emptySalts : Nat) : IO Unit := do
  let file := s!"wycheproof_{name}.blb"
  let fields ← blobs (vectors / file)
  check s!"{file} holds {count} vectors of 4 fields" (fields.size == 4 * count)
  let mut (withoutSalt, longest) := (0, 0)
  for i in [0:count] do
    let field := fun j => fields[4 * i + j]!
    let (ikm, salt, info, okm) := (field 0, field 1, field 2, field 3)
    expectOk s!"{file} vector {i} expandFromPrk"
      (expandFromPrk H (extract H (some salt) ikm) info okm.size) okm
    if salt.isEmpty then
      withoutSalt := withoutSalt + 1
      expectOk s!"{file} vector {i} expandFromPrk without a salt"
        (expandFromPrk H (extract H none ikm) info okm.size) okm
    if okm.size == 255 * H.hashLen then longest := longest + 1
  check s!"{file} has {emptySalts} vectors with an empty salt" (withoutSalt == emptySalts)
  check s!"{file} has 3 vectors of 255 * HashLen bytes" (longest == 3)
  let (ikm, salt, info, okm) := (fields[0]!, fields[1]!, fields[2]!, fields[3]!)
  let prk := extract H (some salt) ikm
  check s!"{file} vector 0 has a PRK of HashLen bytes" (prk.size == H.hashLen)
  expectError s!"{file} PRK of HashLen - 1 bytes"
    (expandFromPrk H (prk.extract 0 (H.hashLen - 1)) info okm.size) .invalidPrkLength
  expectError s!"{file} 255 * HashLen + 1 output bytes"
    (expandFromPrk H prk info (255 * H.hashLen + 1)) .invalidLength
  IO.println s!"hkdf {file}: {count} vectors passed, {withoutSalt} also without a salt; \
    2 length rejections"

/-- The size of an accepted result, or `none` for a rejection -/
private def acceptedSize {ε : Type} : Except ε ByteArray → Option Nat
  | .ok bytes => some bytes.size
  | .error _ => none

/--
One test case as the crate's tests pass it, fields `ikm, salt, info, okm`, with the PRK where the
source publishes one
-/
private structure TestCase where
  ikm : ByteArray
  salt : Option ByteArray
  info : ByteArray
  okm : ByteArray
  prk : Option ByteArray
  deriving Inhabited

/--
RFC 5869's test cases from the crate's `rfc5869_<name>.blb`, an empty stored salt as `None`, as the
crate's `tests/rfc5869.rs` passes it
-/
private def rfcVectors (name : String) (count : Nat) : IO (Array TestCase) := do
  let fields ← blobs (vectors / s!"rfc5869_{name}.blb")
  check s!"rfc5869_{name}.blb holds {count} vectors of 5 fields" (fields.size == 5 * count)
  return (Array.range count).map fun i =>
    let field := fun j => fields[5 * i + j]!
    { ikm := field 0, salt := if (field 1).isEmpty then none else some (field 1), info := field 2,
      okm := field 4, prk := some (field 3) }

/--
The length rules of the crate's `tests/tests.rs`, which it runs at SHA-256, here at the hash `H`,
with a PRK of `HashLen` bytes, its info and its OKM: a PRK of `HashLen - 1` bytes is rejected
(`test_prk_too_short`), with the PRK itself accepted as the control, `255 * HashLen` output bytes
are accepted (`test_max_length`), and `255 * HashLen + 1` and 90000 are rejected
(`test_max_length_exceeded`, `test_unsupported_length`). The accepted outputs of
`255 * HashLen` bytes are checked by Wycheproof's vectors of that size above; here only their length
is. `from_prk` runs before `expand_multi_info`'s check, so a short PRK with a long output reports
`InvalidPrkLength`. The PRK is RFC 5869 A.1's.
-/
private def lengthRules (H : HKDF.Hash) (label : String) (prk info okm : ByteArray) : IO Unit := do
  let limit := 255 * H.hashLen
  check s!"{label}: a PRK of HashLen bytes" (prk.size == H.hashLen)
  let short := prk.extract 0 (H.hashLen - 1)
  expectError s!"{label}: PRK of HashLen - 1 bytes" (expandFromPrk H short info okm.size)
    .invalidPrkLength
  expectOk s!"{label}: PRK of HashLen bytes, control" (expandFromPrk H prk info okm.size) okm
  expectError s!"{label}: PRK of HashLen - 1 bytes and {limit + 1} output bytes"
    (expandFromPrk H short info (limit + 1)) .invalidPrkLength
  expectError s!"{label}: {limit + 1} output bytes" (expandFromPrk H prk info (limit + 1))
    .invalidLength
  expectError s!"{label}: 90000 output bytes" (expandFromPrk H prk info 90000) .invalidLength
  check s!"{label}: {limit} output bytes, control"
    (acceptedSize (expandFromPrk H prk info limit) == some limit)
  IO.println s!"hkdf length rules at {label}: 6 checks passed, after the PRK size precondition"

/--
An output of zero bytes, which no published vector has: `expand_multi_info` accepts it and writes
nothing, so `expandFromPrk` returns the empty string, and a PRK of `HashLen - 1`
bytes is still rejected first. The inputs are those of `lengthRules`, whose checks are the controls.
-/
private def emptyOutput (H : HKDF.Hash) (label : String) (vector : TestCase) (prk : ByteArray) :
    IO Unit := do
  expectOk s!"{label}: expandFromPrk, 0 output bytes" (expandFromPrk H prk vector.info 0) .empty
  expectError s!"{label}: PRK of HashLen - 1 bytes and 0 output bytes"
    (expandFromPrk H (prk.extract 0 (H.hashLen - 1)) vector.info 0) .invalidPrkLength
  IO.println s!"hkdf empty output at {label}: 2 checks passed"

/--
The slices of the crate's `tests/tests.rs` `test_expand_multi_info` and `test_extract_streaming`,
which pass the five `COMPONENTS` (ASCII strings of 44, 42, 39, 37 and 34 bytes) to
`expand_multi_info` and to `input_ikm` regrouped five ways: the first `k` components joined into one
slice, then the other `5 - k` one by one, for `k` from 1 to 5. Each test asserts that every grouping
gives the result of the one slice `COMPONENTS.concat()`, written out below, so `concatenation` of
each grouping must equal it, since the `extract` theorem states its output over `concatenation`.
Then no slices give the empty string, and the components in reverse order, with an empty slice
before, between and after them, give the reversed string, so the order is kept and empty slices add
nothing. The slices' addresses play no part.
-/
private def concatenationOfSlices : IO Unit := do
  let components : Array ByteArray := #[
    "09090909090909090909090909090909090909090909".toUTF8,
    "8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a".toUTF8,
    "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0".toUTF8,
    "4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4".toUTF8,
    "1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d".toUTF8]
  let joined := "09090909090909090909090909090909090909090909\
    8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a\
    0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0\
    4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4\
    1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d".toUTF8
  check "COMPONENTS.concat() has 196 bytes" (joined.size == 196)
  let slices := fun (parts : Array ByteArray) => parts.zipIdx.map fun (bytes, i) =>
    ({ address := BitVec.ofNat 64 (0x10000 + 0x100 * i), bytes } : Input)
  for k in [1:6] do
    let head := (components.extract 0 k).foldl (· ++ ·) ByteArray.empty
    let parts := #[head] ++ components.extract k 5
    expect s!"concatenation of {6 - k} slices" (concatenation (slices parts)) joined
  expect "concatenation of no slices" (concatenation #[]) ByteArray.empty
  let reversed := "1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d\
    4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4\
    0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0\
    8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a\
    09090909090909090909090909090909090909090909".toUTF8
  let withEmpty := #[ByteArray.empty] ++ components.reverse.flatMap (#[·, ByteArray.empty])
  expect "concatenation of the components reversed, with empty slices"
    (concatenation (slices withEmpty)) reversed
  IO.println "hkdf concatenation: 8 checks passed"

/--
The specifications of the combined entry points on the published vectors at the hash `H`, as the
crate's tests pass them: `expandFromPrk` of `extract`'s PRK, the specification of `extract_expand`
and `new_expand`, gives the OKM, from a PRK of `HashLen` bytes, so `from_prk`'s rule never rejects
it; `extract` of `concatenation` of the IKM split into slices three ways (whole; halves; an empty
slice, the first byte, the rest and an empty slice), the specification of `finalize_expand`, gives
the same OKM: 5 checks per vector. RFC 5869 A.2's IKM bytes are distinct, so a reordering would
fail there. Then, with the first vector, an output of `255 * HashLen + 1` bytes is rejected by
the specifications of `extract_expand` and `finalize_expand`, with `255 * HashLen` bytes accepted as
each one's control; the accepted bytes at that length are checked by Wycheproof's vectors above,
and here only the length is.
-/
private def combinedEntryPoints (H : HKDF.Hash) (label : String) (cases : Array TestCase)
    (expected : Nat) : IO Unit := do
  let slices := fun (parts : Array ByteArray) => parts.zipIdx.map fun (bytes, i) =>
    ({ address := BitVec.ofNat 64 (0x10000 + 0x100 * i), bytes } : Input)
  let mut checks := 0
  for h : i in [0:cases.size] do
    let { ikm, salt, info, okm, .. } := cases[i]
    let half := ikm.size / 2
    check s!"{label} vector {i}: extract gives a PRK of HashLen bytes"
      ((extract H salt ikm).size == H.hashLen)
    expectOk s!"{label} vector {i}: extract_expand and new_expand"
      (expandFromPrk H (extract H salt ikm) info okm.size) okm
    checks := checks + 2
    let groupings : Array (Array ByteArray) := #[#[ikm],
      #[ikm.extract 0 half, ikm.extract half ikm.size],
      #[.empty, ikm.extract 0 1, ikm.extract 1 ikm.size, .empty]]
    for parts in groupings do
      expectOk s!"{label} vector {i}: finalize_expand, {parts.size} slices"
        (expandFromPrk H (extract H salt (concatenation (slices parts))) info okm.size) okm
      checks := checks + 1
  let limit := 255 * H.hashLen
  let { ikm, salt, info, .. } := cases[0]!
  let split := ikm.size / 2
  let prk := extract H salt ikm
  expectError s!"{label}: extract_expand, {limit + 1} output bytes"
    (expandFromPrk H prk info (limit + 1)) .invalidLength
  check s!"{label}: extract_expand, {limit} output bytes, control"
    (acceptedSize (expandFromPrk H prk info limit) == some limit)
  let parts := slices #[ikm.extract 0 split, ikm.extract split ikm.size]
  expectError s!"{label}: finalize_expand, {limit + 1} output bytes"
    (expandFromPrk H (extract H salt (concatenation parts)) info (limit + 1)) .invalidLength
  check s!"{label}: finalize_expand, {limit} output bytes, control"
    (acceptedSize (expandFromPrk H (extract H salt (concatenation parts)) info limit) == some limit)
  check s!"{label}: combined entry points, {expected} vector checks" (checks == expected)
  IO.println s!"hkdf combined entry points at {label}: {checks} vector checks and 4 length checks \
    passed"

/-- Runs every `hkdf` test, throwing on the first failure -/
def run : IO Unit := do
  rfc5869 .sha256 "sha256" 3 1
  wycheproof .sha256 "sha256" 102 22
  let rfcSha256 ← rfcVectors "sha256" 3
  let first := rfcSha256[0]!
  let prk := first.prk.getD (extract .sha256 first.salt first.ikm)
  lengthRules .sha256 "SHA-256" prk first.info first.okm
  emptyOutput .sha256 "SHA-256" first prk
  concatenationOfSlices
  combinedEntryPoints .sha256 "SHA-256" rfcSha256 15

end Hkdf.Tests
