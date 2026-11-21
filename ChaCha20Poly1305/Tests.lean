import ChaCha20Poly1305.Spec.AEAD
import ChaCha20Poly1305.Spec.Program.Routine

/-!
# `chacha20poly1305` tests

The crate's own test data at 0.11.0, run through the specification, by
`cd ChaCha20Poly1305 && lake test` (its own Lake package). The specification and the wrappers'
`Routine` records (`Spec/Program/Routine.lean`) are imported without the program image.

The vectors are the two ChaCha20Poly1305 files of the crate's `tests/data/`, from the
chacha20poly1305 0.11.0 package on crates.io
(https://docs.rs/crate/chacha20poly1305/0.11.0/source/tests/data/), kept unmodified in
`Tests/Vectors/` and read in aead 0.6.1's blobby format, five blobs per vector: key, nonce,
associated data, plaintext, and ciphertext followed by its tag. The crate derived them from
Project Wycheproof. Their expected values are the files':

* `wycheproof_chacha20poly1305_pass.blb` (SHA-256
  `87695fa84e7d146aad3a8b3290bf19e3cebf4e774ce3a8b56156f9418c28886b`): 233 vectors, which the
  crate's `new_pass_test!` encrypts with `Aead::encrypt` and decrypts with `Aead::decrypt` (aead
  0.6.1 `src/dev.rs`, lines 77-102). Each is checked by `encryptWithTag` against the file's
  ciphertext and tag, by `decryptWithTag` against its plaintext, and by `encryptWithoutTag`
  against the ciphertext alone, which `encrypt_in_place` leaves when its buffer has no room for the
  tag. Each decryption routine's `accepts` must accept it, so the call needs its output.
  Pinned: 38 have empty associated data and 53 associated data of a non-zero multiple of 16
  bytes; 2 an empty plaintext, 154 a plaintext of a non-zero multiple of 16 bytes, and 100 a
  plaintext over one 64-byte block.
* `wycheproof_chacha20poly1305_fail.blb` (SHA-256
  `2f0905a07a45c1d7955c0777617c98b701664c8f021f40d1ab60e7f0c5f8daaf`): 60 vectors, which the
  crate's `new_fail_test!` requires `Aead::decrypt` to reject. Each is checked to be rejected by
  `decryptWithTag`. Pinned: 20 have an empty
  plaintext, so a 16-byte input that is only a tag.

Rejections with their controls: each passing vector, accepted unchanged, is rejected with one bit
of its tag flipped, and, where it has a ciphertext, with one bit of its first ciphertext byte
flipped, by `decryptWithTag` (RFC 8439 §2.8: the message is authenticated only if the tags
match), and by each decryption routine's `accepts`. With the flipped tag, `decrypt` needs no
output, which its disassembly never touches on rejection, while `decrypt_in_place` still needs its
buffer, which holds its input.
Inputs shorter than
the tag: the two passing vectors with an empty plaintext are 16-byte inputs, accepted unchanged;
the same input without its last byte, 15 bytes, and the empty input are rejected, as aead 0.6.1's
`decrypt_in_place` returns its error when `checked_sub(16)` fails (`src/lib.rs`, line 299).

The vectors' plaintexts are at most 128 bytes, and the published vectors of the standard's own tests
(`Standards/RFC/ChaCha20Poly1305/AEAD/Tests.lean`, on the RFC 8439 definitions this crate's
specification calls unchanged) stop at 513 bytes (Wycheproof) and 265 (RFC 8439 A.5). No published
ChaCha20-Poly1305 vector in this repository is longer, though the theorems admit messages up to 4
GiB. For longer messages the tests check the specification against OpenSSL instead, an
implementation sharing no code with the specification or the crate:
`Tests/Generated/long_messages.txt`, written by `Tests/Generated/long_messages.py` (OpenSSL 3.0.13
through Python's cryptography 41.0.7), holds 4 cases of 514, 4,097, 65,601 and 1,048,639 bytes, with
associated data of 0, 13, 17 and 65,537 bytes. For each, `encryptWithTag` must give OpenSSL's tag
and the first and last 32 bytes of its ciphertext, and `decryptWithTag` must accept the result and
return the message. Between 1,048,639 bytes and 4 GiB there is no check against an outside
implementation: there the specification's agreement with RFC 8439 rests on its code, which treats
every 64-byte block alike, and its agreement with the crate on the proofs. No test reaches the
crate's length limit, which no theorem covers.

The routines (`routines`), on machine states whose argument registers and stack slots hold
distinct numbers:

* each `Routine` reads the message's length, and where it has them the capacity, the heap's
  address and length and the output's length, from the argument where the wrapper's signature in
  `program/src/lib.rs` puts it under System V (RDI, RSI, RDX, RCX, R8, R9, then the stack slots);
* its output size is RFC 8439 §2.8.2's: a 114-byte message gives 130 bytes, ciphertext and tag;
* the heaps of `encrypt` and `decrypt` are what `Aead::encrypt` and `Aead::decrypt` allocate
  (`Heap.bytes` in `Spec/Program/Routine.lean`): the message and 16 bytes, and the input's length,
  none for an empty input; the in-place routines have none;
* `hasRoom` holds for `encrypt_in_place` exactly when the capacity is at least the message's
  length plus 16, where the wrapper's `SliceBuffer::extend_from_slice` has room for the tag
  (checked at 114 bytes and at none, with one byte less as the control), and for every other
  routine, so that their `outputRegion` is the output's size.

Not tested: the registers holding the inputs' addresses (`inputs`) and the output's
(`outputPointer`), and the length arguments in `inputs`, the associated data's and the message's,
which repeats `messageLength` with nothing in the tests tying the two together. A wrong one would
make its routine's theorem false of the compiled code, so the proofs check them.

The rest of the call contract, `ValidCall` and the regions, is in `Spec/Program.lean`, which the
tests do not import, as it holds the program image; no test runs the extracted code, and the
proofs check it.
-/

namespace ChaCha20Poly1305.Tests

open ChaCha20Poly1305.Spec Standards.RFC.ChaCha20Poly1305 X86

/-- Throws `label` unless `condition` holds -/
def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"chacha20poly1305: {label}")

/--
Reads a blobby number at `position` and the position after it: seven bits per byte, a set high bit
continuing it, each continuation adding one before shifting, at most four bytes (blobby 0.4's
`read_vlq`)
-/
def readNumber (data : ByteArray) (position : Nat) : Except String (Nat × Nat) := do
  let mut value := 0
  let mut next := position
  for step in [0:4] do
    let some byte := data[next]? | throw "unexpected end of a number"
    next := next + 1
    let bits := (byte &&& 0x7f).toNat
    value := if step == 0 then bits else ((value + 1) <<< 7) + bits
    if byte &&& 0x80 == 0 then return (value, next)
  throw "a number longer than four bytes"

/--
The blobs of a blobby file (blobby 0.4's `parse_into_vec`): the blob and table counts, the table of
repeated blobs, then each blob as an odd number (twice the table index, plus one) or an even one
(twice its length) followed by its bytes; nothing may follow
-/
def readBlobs (data : ByteArray) : Except String (Array ByteArray) := do
  let (blobCount, next) ← readNumber data 0
  let (tableCount, next) ← readNumber data next
  let mut position := next
  let mut table := #[]
  for _ in [0:tableCount] do
    let (length, next) ← readNumber data position
    if next + length > data.size then throw "a table blob past the end"
    table := table.push (data.extract next (next + length))
    position := next + length
  let mut blobs := #[]
  for _ in [0:blobCount] do
    let (value, next) ← readNumber data position
    position := next
    if value % 2 == 1 then
      let some blob := table[value / 2]? | throw "a table index out of range"
      blobs := blobs.push blob
    else
      if position + value / 2 > data.size then throw "a blob past the end"
      blobs := blobs.push (data.extract position (position + value / 2))
      position := position + value / 2
  if position != data.size then throw "bytes after the last blob"
  return blobs

/-- One test vector of aead's `TestVector`: the ciphertext is followed by its 16-byte tag -/
structure TestVector where
  key : Vector UInt8 32
  nonce : Vector UInt8 12
  associatedData : ByteArray
  plaintext : ByteArray
  ciphertextWithTag : ByteArray

/-- `bytes` as a vector of `n` bytes, or an error naming its length -/
def toVector (bytes : ByteArray) (n : Nat) : Except String (Vector UInt8 n) :=
  if h : bytes.data.size = n then .ok ⟨bytes.data, h⟩
  else .error s!"expected {n} bytes, found {bytes.size}"

/-- The vectors of a blobby file, five blobs each -/
def readVectors (path : String) : IO (Array TestVector) := do
  let blobs ← IO.ofExcept (readBlobs (← IO.FS.readBinFile path))
  check s!"{path}: a whole number of five-blob vectors" (blobs.size % 5 == 0)
  (List.range (blobs.size / 5)).toArray.mapM fun i => IO.ofExcept do
    pure {
      key := ← toVector blobs[5 * i]! 32
      nonce := ← toVector blobs[5 * i + 1]! 12
      associatedData := blobs[5 * i + 2]!
      plaintext := blobs[5 * i + 3]!
      ciphertextWithTag := blobs[5 * i + 4]! }

/-- The input with bit 0 of byte `index` flipped -/
def flipBit (bytes : ByteArray) (index : Nat) : ByteArray := bytes.set! index (bytes[index]! ^^^ 1)

/-- Every check of the passing vectors, their pinned counts, and their rejections with controls -/
def passing : IO Unit := do
  let vectors ← readVectors "ChaCha20Poly1305/Tests/Vectors/wycheproof_chacha20poly1305_pass.blb"
  check s!"pass: expected 233 vectors, parsed {vectors.size}" (vectors.size == 233)
  for v in vectors, index in [0:vectors.size] do
    let label := s!"pass #{index}"
    let n := v.plaintext.size
    check s!"{label}: input is the plaintext and a tag" (v.ciphertextWithTag.size == n + 16)
    let ciphertext := v.ciphertextWithTag.extract 0 n
    check s!"{label}: encryptWithTag" <|
      AEAD.encryptWithTag v.associatedData v.key v.nonce v.plaintext == v.ciphertextWithTag
    check s!"{label}: decryptWithTag" <|
      AEAD.decryptWithTag v.associatedData v.key v.nonce v.ciphertextWithTag == some v.plaintext
    check s!"{label}: encryptWithoutTag, what encrypt_in_place leaves without room" <|
      AEAD.encryptWithoutTag v.associatedData v.key v.nonce v.plaintext == ciphertext
    let combined : List ByteArray := [v.key, v.nonce, v.associatedData, v.ciphertextWithTag]
    check s!"{label}: decrypt and decrypt_in_place accept it and need their output" <|
      Program.decrypt.needsOutput combined && Program.decryptInPlace.needsOutput combined
    let flippedTag := flipBit v.ciphertextWithTag (n + 15)
    check s!"{label}: a flipped tag bit is rejected" <|
      AEAD.decryptWithTag v.associatedData v.key v.nonce flippedTag == none
    let flipped : List ByteArray := [v.key, v.nonce, v.associatedData, flippedTag]
    check s!"{label}: a flipped tag bit: decrypt_in_place rejects it but needs its buffer" <|
      !Program.decryptInPlace.accepts flipped && Program.decryptInPlace.needsOutput flipped
    check s!"{label}: a flipped tag bit: decrypt needs no output" <|
      !Program.decrypt.needsOutput flipped
    if n > 0 then
      check s!"{label}: a flipped ciphertext bit is rejected" <|
        AEAD.decryptWithTag v.associatedData v.key v.nonce (flipBit v.ciphertextWithTag 0) == none
  let count (p : TestVector → Bool) := (vectors.filter p).size
  let blockMultiple (bytes : ByteArray) := bytes.size > 0 && bytes.size % 16 == 0
  let counts := (count (·.associatedData.size == 0), count (blockMultiple ·.associatedData),
    count (·.plaintext.size == 0), count (blockMultiple ·.plaintext), count (·.plaintext.size > 64))
  check s!"pass: pinned counts, found {counts}" (counts == (38, 53, 2, 154, 100))

/-- The failing vectors, each rejected by `decryptWithTag` -/
def failing : IO Unit := do
  let vectors ← readVectors "ChaCha20Poly1305/Tests/Vectors/wycheproof_chacha20poly1305_fail.blb"
  check s!"fail: expected 60 vectors, parsed {vectors.size}" (vectors.size == 60)
  for v in vectors, index in [0:vectors.size] do
    let label := s!"fail #{index}"
    check s!"{label}: decryptWithTag rejects" <|
      AEAD.decryptWithTag v.associatedData v.key v.nonce v.ciphertextWithTag == none
  let onlyTag := (vectors.filter (·.plaintext.size == 0)).size
  check s!"fail: expected 20 vectors with an empty plaintext, found {onlyTag}" (onlyTag == 20)

/--
`decryptWithTag` below 16 bytes: the passing vectors with an empty plaintext, 16 bytes, accepted
as the control; 15 of those bytes and none rejected, as aead's `checked_sub(16)` makes them
-/
def shortInputs : IO Unit := do
  let vectors ← readVectors "ChaCha20Poly1305/Tests/Vectors/wycheproof_chacha20poly1305_pass.blb"
  let tagOnly := vectors.filter (·.plaintext.size == 0)
  check s!"short: expected 2 tag-only vectors, found {tagOnly.size}" (tagOnly.size == 2)
  for v in tagOnly do
    let decrypt := AEAD.decryptWithTag v.associatedData v.key v.nonce
    check "short: the 16-byte tag-only input is accepted" <|
      decrypt v.ciphertextWithTag == some ByteArray.empty
    check "short: 15 bytes are rejected" (decrypt (v.ciphertextWithTag.extract 0 15) == none)
    check "short: no bytes are rejected" (decrypt ByteArray.empty == none)

/--
A machine state holding a call's arguments: RSP is `0x80008`, each register of `registers` holds
its number, and stack slot `i`, the 8 bytes at `RSP + 8 * (i + 1)`, holds the `i`-th of `slots` as
a little-endian word
-/
def argumentState (registers : List (Syntax.Reg × Nat)) (slots : List Nat) : Machine.RamState :=
  let rsp := 0x80008
  let state : Machine.RamState := default
  let registerFile := ((.rsp, rsp) :: registers).foldl
    (fun file (register, value) => file.setIfInBounds register.fin.val (BitVec.ofNat 64 value))
    state.GPR
  let memory := slots.zipIdx.foldl
    (fun memory (value, i) => (List.range 8).foldl
      (fun memory byte => memory.insert (BitVec.ofNat 64 (rsp + 8 * (i + 1) + byte))
        (UInt8.ofNat (value / 256 ^ byte)))
      memory)
    state.external
  { state with GPR := registerFile, external := memory }

/--
The routines' length arguments and sizes: the argument each reads the message's length, capacity,
heap address and length and output length from, by the wrapper signatures in `program/src/lib.rs`
under System V; the output sizes of RFC 8439 §2.8.2 (114 bytes of message, 130 with the tag); the
heap sizes `Aead::encrypt` and `Aead::decrypt` allocate; and `hasRoom`, which holds for
`encrypt_in_place` exactly when `SliceBuffer::extend_from_slice` has room for the tag, at least the
message's length plus 16, and for every other routine. Not the input and output pointer registers,
nor the length arguments in `inputs` (the module doc says why)
-/
def routines : IO Unit := do
  let state := argumentState [(.r8, 0x11), (.r9, 0x22)] [0x33, 0x44, 0x55, 0x66]
  let message (routine : Program.Routine) := Program.messageBytes routine state
  check "routines: message length in stack slot 1 (encrypt's `message_len`)" <|
    message Program.encrypt == 0x44
  check "routines: message length in stack slot 1 (decrypt's `ciphertext_len`)" <|
    message Program.decrypt == 0x44
  check "routines: message length in R9 (encrypt_in_place's `len`)" <|
    message Program.encryptInPlace == 0x22
  check "routines: message length in R9 (decrypt_in_place's `len`)" <|
    message Program.decryptInPlace == 0x22
  check "routines: encrypt_in_place's capacity in stack slot 0 (`capacity`); no other has one" <|
    Program.encryptInPlace.capacity.map (Program.argumentValue state) == some 0x33 &&
      [Program.encrypt, Program.decrypt, Program.decryptInPlace].all (·.capacity.isNone)
  check "routines: encrypt's and decrypt's output length in stack slot 3 (`output_len`)" <|
    [Program.encrypt, Program.decrypt].all fun routine =>
      routine.outputLength.map (Program.argumentValue state) == some 0x66
  check "routines: 114 bytes encrypt to 130, ciphertext and tag (RFC 8439 §2.8.2)" <|
    [Program.encrypt, Program.encryptInPlace].all (·.outputBytes 114 == 130)
  check "routines: 130 bytes, ciphertext and tag, decrypt to 114 (RFC 8439 §2.8.2)" <|
    [Program.decrypt, Program.decryptInPlace].all (·.outputBytes 130 == 114)
  check "routines: encrypt's heap, at R8 with its length in slot 2, takes the message and 16" <|
    (Program.encrypt.heap.map fun heap =>
      (heap.pointer == .r8, Program.argumentValue state heap.length, heap.bytes 114)) ==
      some (true, 0x55, 130)
  check "routines: decrypt's heap, at R8 with its length in slot 2, takes the input (0 if empty)" <|
    (Program.decrypt.heap.map fun heap => (heap.pointer == .r8,
      Program.argumentValue state heap.length, heap.bytes 130, heap.bytes 0)) ==
      some (true, 0x55, 130, 0)
  check "routines: no heap for the two in-place calls, which do not allocate" <|
    [Program.encryptInPlace, Program.decryptInPlace].all (·.heap.isNone)
  let inPlace (message capacity : Nat) :=
    Program.hasRoom Program.encryptInPlace (argumentState [(.r9, message)] [capacity])
  check "routines: encrypt_in_place, 114 bytes in 130 have room" (inPlace 114 130)
  check "routines: encrypt_in_place, 114 bytes in 129 have none" (!inPlace 114 129)
  check "routines: encrypt_in_place, no bytes in 16 have room" (inPlace 0 16)
  check "routines: encrypt_in_place, no bytes in 15 have none" (!inPlace 0 15)
  let other := argumentState [(.r9, 130)] [130, 130, 130, 130]
  check "routines: every other routine has room for its output" <|
    [Program.encrypt, Program.decrypt, Program.decryptInPlace].all (Program.hasRoom · other)

/-- The bytes of hexadecimal text, two digits per byte, or an error -/
def fromHex (text : String) : Except String ByteArray := do
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else .error s!"not a hexadecimal digit: {c}"
  let chars := text.toList.toArray
  if chars.size % 2 != 0 then throw s!"odd number of hexadecimal digits: {text}"
  let mut bytes := ByteArray.empty
  for i in [0:chars.size / 2] do
    let high ← digit chars[2 * i]!
    let low ← digit chars[2 * i + 1]!
    bytes := bytes.push (UInt8.ofNat (16 * high + low))
  return bytes

/-- `length` bytes, byte `i` being `(step * i + offset) mod 256`, as `long_messages.py` builds
them -/
def pattern (length step offset : Nat) : ByteArray :=
  ⟨Array.ofFn fun i : Fin length => UInt8.ofNat (step * i.val + offset)⟩

/--
The long messages of `Tests/Generated/long_messages.txt` against OpenSSL: `encryptWithTag` gives
OpenSSL's tag and the first and last 32 bytes of its ciphertext, and `decryptWithTag` accepts the
result and returns the message; the case count and the lengths are pinned
-/
def longMessages : IO Unit := do
  let text ← IO.FS.readFile "ChaCha20Poly1305/Tests/Generated/long_messages.txt"
  let lines := (text.splitOn "\n").filter (· ≠ "")
  check s!"long: expected 4 cases, found {lines.length}" (lines.length == 4)
  let mut lengths := #[]
  for line in lines do
    let [messageText, dataText, keyText, nonceText, headText, tailText, tagText] :=
      line.splitOn " " | throw (IO.userError s!"chacha20poly1305: long: bad line {line}")
    let some messageLength := messageText.toNat? | throw (IO.userError "long: bad length")
    let some dataLength := dataText.toNat? | throw (IO.userError "long: bad length")
    lengths := lengths.push (messageLength, dataLength)
    let key ← IO.ofExcept (fromHex keyText >>= (toVector · 32))
    let nonce ← IO.ofExcept (fromHex nonceText >>= (toVector · 12))
    let head ← IO.ofExcept (fromHex headText)
    let tail ← IO.ofExcept (fromHex tailText)
    let tag ← IO.ofExcept (fromHex tagText)
    let message := pattern messageLength 167 13
    let data := pattern dataLength 59 101
    let label := s!"long, {messageLength} bytes"
    let sealed := AEAD.encryptWithTag data key nonce message
    check s!"{label}: ciphertext and tag" (sealed.size == messageLength + 16)
    check s!"{label}: first 32 ciphertext bytes (OpenSSL)" (sealed.extract 0 32 == head)
    check s!"{label}: last 32 ciphertext bytes (OpenSSL)" <|
      sealed.extract (messageLength - 32) messageLength == tail
    check s!"{label}: tag (OpenSSL)" (sealed.extract messageLength (messageLength + 16) == tag)
    check s!"{label}: decryptWithTag" (AEAD.decryptWithTag data key nonce sealed == some message)
  check s!"long: pinned lengths, found {lengths}" <|
    lengths == #[(514, 0), (4097, 13), (65601, 17), (1048639, 65537)]

/-- Runs every `chacha20poly1305` test, throwing on the first failure -/
def run : IO Unit := do
  passing
  failing
  shortInputs
  longMessages
  routines
  IO.println <| "chacha20poly1305: 233 passing and 60 failing vectors, rejections, short " ++
    "inputs, 4 long messages against OpenSSL and the routines' length arguments, sizes and room"

end ChaCha20Poly1305.Tests
