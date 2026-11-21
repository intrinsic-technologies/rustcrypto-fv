import Base16ct.Spec
import Base16ct.Tests.CallWitness
import Standards.Tests.Utilities

/-!
# `base16ct` tests

Checks of the crate's specification `Base16ct.Spec.Base16`, run by `cd Base16ct && lake test`
(`Base16ct` is its own Lake package). The shared RFC 4648 definitions are tested against the RFC's
own vectors, including §10 `BASE16`, in `Standards/RFC/BaseEncodings/Tests.lean`, and those are
not repeated here. Nothing here runs the extracted machine code.

Sources, with the number of vectors and what each checks:

* `Tests/Vectors/base16ct-1.0.0-tests-lib.rs`, `HEX_TEST_VECTORS` (6): both encoders, and the
  three decoders through `decodeInto` with the crate's 5-byte buffer and with a buffer of
  exactly the decoded length, as the crate's `decode_vec` tests allocate; `mixed` decodes both
  the lowercase and the uppercase text with each buffer
* the same file, the odd-length tests (3): `12345` with a 3-byte buffer is `invalidLength` for
  each decoder
* the same file, `encode_and_decode_various_lengths` (64 lengths): `decodeInto` with a buffer of
  exactly the decoded length after each encoder, for `X` repeated 0 to 63 times; the crate's
  test decodes with `decode_vec`, which allocates that buffer
* the crate's docs example, `base16ct-1.0.0/src/lib.rs:29-32` (1): `AB CD 12 34` and its lower,
  upper and mixed-case text
* RFC 4648 Table 5 and §3.3 (all 65,536 two-character inputs): which characters each decoder
  accepts, and their values
* `decode_inner`, `base16ct-1.0.0/src/lib.rs:102-122`: each branch of `decodedLength` and
  `decodeInto`, with controls

Every expected value comes from the crate's test file, the crate's docs, or RFC 4648, as each
check's label says; the order of the length checks before the character check comes from the crate's
code. The expected values of the character table are written out from Table 5 and the case rule, not
computed by the specification. The vector file is the crate's `tests/lib.rs`, unmodified (SHA-256
`1b5ae439670c8c1ca3843922bd484dc642b660d91f401a29fa279d9e01fdab92`).

Boundaries without a published vector: no input to the encoders is longer than 63 bytes (the
round trips pass up to 126 characters to `decodeInto`). Every output buffer of an even-length
input is exactly its decoded length or shorter, except the crate's 5-byte and the docs' 16-byte
buffers. The odd-length rejections, which fail on the length before the buffer is used, take
buffers longer than half the input length rounded down: 3 bytes for the crate's `12345`, 4 for
the 7-character inputs (`abcd123`, `abcd12x` and their uppercase forms) and 1 for `1`. Longer
inputs and other capacities rest on the crate.

The encoders' buffer check, `2 * input.size ≤ outputCapacity`, has no test here: the encoder
specifications take no buffer, and the rule appears only in the encode theorems' `if`, where a
proof ties it to the compiled code. The crate's `lower_encode` and `upper_encode` tests use a
10-byte buffer, which every vector fits.

`Base16ct.Tests.CallWitness` holds no executable check: its theorems, checked when this library
is built, exhibit for every theorem a machine state that meets all of its statement's
hypotheses on a non-empty input, so no call predicate is unsatisfiable.
-/

namespace Base16ct.Tests

open Base16ct.Spec.Base16 Standards.Tests

private def vectorFile : String := "Base16ct/Tests/Vectors/base16ct-1.0.0-tests-lib.rs"

private def ascii (text : String) : ByteArray := text.toUTF8

/-- Bytes of the contents of a Rust byte-string literal, with its `\0` and `\xNN` escapes -/
private partial def unescape (chars : List Char) (bytes : ByteArray := .empty) : IO ByteArray :=
  match chars with
  | [] => pure bytes
  | '\\' :: '0' :: rest => unescape rest (bytes.push 0)
  | '\\' :: 'x' :: high :: low :: rest => do
    let value := 16 * (← hexDigit high) + (← hexDigit low)
    unescape rest (bytes.push (UInt8.ofNat value))
  | '\\' :: _ => throw (IO.userError "unsupported escape in a byte-string literal")
  | c :: rest => unescape rest (bytes ++ c.toString.toUTF8)

/-- The byte-string literal after `marker` in `line`, such as `b"2a2a2a"` after `lower_hex: ` -/
private def literalAfter (line marker : String) : IO ByteArray := do
  let tail ← after line (marker ++ "b\"")
  unescape ((tail.splitOn "\"").head!).toList

/-- `HEX_TEST_VECTORS` of the crate's test file, as `(raw, lower_hex, upper_hex)` -/
private def crateVectors (document : String) :
    IO (List (ByteArray × ByteArray × ByteArray)) := do
  let table := ((← after document "const HEX_TEST_VECTORS: &[HexVector] = &[").splitOn "];").head!
  let entries := (table.splitOn "HexVector {").drop 1
  let vectors ← entries.mapM fun entry => do
    let lines := entry.splitOn "\n"
    let field (name : String) : IO ByteArray := do
      match lines.find? (·.trimAscii.toString.startsWith s!"{name}: ") with
      | some line => literalAfter line s!"{name}: "
      | none => throw (IO.userError s!"HexVector without {name}")
    pure (← field "raw", ← field "lower_hex", ← field "upper_hex")
  check "crate tests/lib.rs: six HEX_TEST_VECTORS" (vectors.length == 6)
  pure vectors

/-- The inputs of the crate's `*_reject_odd_size_input` tests, `decode(b"…", &mut out)` -/
private def oddLengthInputs (document : String) : IO (List ByteArray) := do
  let calls := (document.splitOn "::decode(b\"").drop 1
  let inputs ← calls.mapM fun call => unescape ((call.splitOn "\"").head!).toList
  check "crate tests/lib.rs: three odd-length decode tests" (inputs.length == 3)
  check "crate tests/lib.rs: each with a 3-byte buffer"
    ((document.splitOn "let mut out = [0u8; 3];").length == 4)
  pure inputs

private def isOk (result : Except Error ByteArray) (expected : ByteArray) : Bool :=
  match result with
  | .ok output => output == expected
  | .error _ => false

private def isError (result : Except Error ByteArray) (expected : Error) : Bool :=
  match result with
  | .ok _ => false
  | .error error => error == expected

private def decoders : List (String × (ByteArray → Option ByteArray)) :=
  [("lower", lowerDecoder), ("upper", upperDecoder), ("mixed", mixedDecoder)]

/--
The crate's `HEX_TEST_VECTORS`, as its `lower_*`, `upper_*` and `mixed_decode` tests use them;
its `hex_display_*` tests also use them, but no theorem here covers `HexDisplay`
-/
private def checkCrateVectors (document : String) : IO Unit := do
  for (raw, lower, upper) in ← crateVectors document do
    let label := s!"crate vector {String.fromUTF8! upper}"
    check s!"{label}: lower encoding" (lowerEncoder raw == lower)
    check s!"{label}: upper encoding" (upperEncoder raw == upper)
    check s!"{label}: lower decode, 5-byte buffer" (isOk (decodeInto lowerDecoder lower 5) raw)
    check s!"{label}: upper decode, 5-byte buffer" (isOk (decodeInto upperDecoder upper 5) raw)
    check s!"{label}: mixed decode of the uppercase text, 5-byte buffer"
      (isOk (decodeInto mixedDecoder upper 5) raw)
    check s!"{label}: mixed decode of the lowercase text, 5-byte buffer"
      (isOk (decodeInto mixedDecoder lower 5) raw)
    check s!"{label}: lower decode, exact buffer"
      (isOk (decodeInto lowerDecoder lower (lower.size / 2)) raw)
    check s!"{label}: upper decode, exact buffer"
      (isOk (decodeInto upperDecoder upper (upper.size / 2)) raw)
    check s!"{label}: mixed decode of the lowercase text, exact buffer"
      (isOk (decodeInto mixedDecoder lower (lower.size / 2)) raw)
    check s!"{label}: mixed decode of the uppercase text, exact buffer"
      (isOk (decodeInto mixedDecoder upper (upper.size / 2)) raw)

/-- The crate's `*_reject_odd_size_input` tests: `12345` with a 3-byte buffer -/
private def checkOddLengthTests (document : String) : IO Unit := do
  for (input, (name, decoder)) in (← oddLengthInputs document).zip decoders do
    check s!"crate odd-length test, {name}: invalidLength"
      (isError (decodeInto decoder input 3) .invalidLength)

/--
The crate's `encode_and_decode_various_lengths`: `X` repeated 0 to 63 times, encoded and decoded
back; a round trip, so the expected value is the input itself. The crate's test decodes with
`decode_vec`; here `decodeInto` gets a buffer of exactly `i` bytes, the one `decode_vec` allocates
-/
private def checkRoundTrips : IO Unit := do
  for i in [:64] do
    let data := ascii (String.ofList (List.replicate i 'X'))
    check s!"crate round trip {i}: lower"
      (isOk (decodeInto lowerDecoder (lowerEncoder data) i) data)
    check s!"crate round trip {i}: upper"
      (isOk (decodeInto upperDecoder (upperEncoder data) i) data)
    check s!"crate round trip {i}: mixed after lower"
      (isOk (decodeInto mixedDecoder (lowerEncoder data) i) data)
    check s!"crate round trip {i}: mixed after upper"
      (isOk (decodeInto mixedDecoder (upperEncoder data) i) data)

/--
The crate's docs example (`src/lib.rs:29-32`): `abcd1234`, `ABCD1234` and `abCD1234` spell
`AB CD 12 34`; the docs decode into a 16-byte buffer
-/
private def checkDocsExample : IO Unit := do
  let raw := ByteArray.mk #[0xab, 0xcd, 0x12, 0x34]
  check "docs example: lower encoding" (lowerEncoder raw == ascii "abcd1234")
  check "docs example: upper encoding" (upperEncoder raw == ascii "ABCD1234")
  check "docs example: lower decode" (isOk (decodeInto lowerDecoder (ascii "abcd1234") 16) raw)
  check "docs example: upper decode" (isOk (decodeInto upperDecoder (ascii "ABCD1234") 16) raw)
  for text in ["abcd1234", "ABCD1234", "abCD1234"] do
    check s!"docs example: mixed decode of {text}"
      (isOk (decodeInto mixedDecoder (ascii text) 16) raw)

/--
Value of a character in each decoder's alphabet, written out from RFC 4648 Table 5 (`0`–`9`,
`A`–`F`), its lowercase form (§3.4), and both cases for `mixed`; `none` outside it (§3.3)
-/
private def expectedValue (decoder : String) (c : Nat) : Option Nat :=
  if 0x30 ≤ c ∧ c ≤ 0x39 then some (c - 0x30)
  else if 0x41 ≤ c ∧ c ≤ 0x46 ∧ decoder != "lower" then some (c - 0x41 + 10)
  else if 0x61 ≤ c ∧ c ≤ 0x66 ∧ decoder != "upper" then some (c - 0x61 + 10)
  else none

/--
Every pair of bytes as a two-character input, all 65,536, with the control `00`, which every
decoder accepts: the expected octet is `16 * high + low` when both characters are in the
decoder's alphabet, and a rejection otherwise
-/
private def checkCharacters : IO Unit := do
  for (name, decoder) in decoders do
    check s!"{name}: control `00` decodes to 00" (decoder (ascii "00") == some (ByteArray.mk #[0]))
    for high in [:256] do
      for low in [:256] do
        let result := decoder (ByteArray.mk #[UInt8.ofNat high, UInt8.ofNat low])
        let expected := match expectedValue name high, expectedValue name low with
          | some h, some l => some (ByteArray.mk #[UInt8.ofNat (16 * h + l)])
          | _, _ => none
        unless result == expected do
          throw (IO.userError s!"{name}: characters {high} and {low}: wrong result")

/--
Each branch of `decodedLength` and `decodeInto`, with a control for each rejection;
lengths come before characters, as in `decode_inner`
-/
private def checkBranches : IO Unit := do
  check "decodedLength 0 is 0" (decodedLength 0 == some 0)
  check "decodedLength 8 is 4" (decodedLength 8 == some 4)
  check "decodedLength 1 is none" (decodedLength 1 == none)
  check "decodedLength 5 is none" (decodedLength 5 == none)
  let raw := ByteArray.mk #[0xab, 0xcd, 0x12, 0x34]
  for (name, decoder) in decoders do
    let text := if name == "upper" then ascii "ABCD1234" else ascii "abcd1234"
    let bad := if name == "upper" then ascii "ABCD12x4" else ascii "abcd12x4"
    let odd := if name == "upper" then ascii "ABCD123" else ascii "abcd123"
    let oddBad := if name == "upper" then ascii "ABCD12x" else ascii "abcd12x"
    check s!"{name}: empty input, empty buffer" (isOk (decodeInto decoder .empty 0) .empty)
    check s!"{name}: exact buffer (control)" (isOk (decodeInto decoder text 4) raw)
    check s!"{name}: buffer one byte short" (isError (decodeInto decoder text 3) .invalidLength)
    check s!"{name}: odd length" (isError (decodeInto decoder odd 4) .invalidLength)
    check s!"{name}: one character" (isError (decodeInto decoder (ascii "1") 1) .invalidLength)
    check s!"{name}: bad character" (isError (decodeInto decoder bad 4) .invalidEncoding)
    check s!"{name}: bad character and odd length, length first"
      (isError (decodeInto decoder oddBad 4) .invalidLength)
    check s!"{name}: bad character and short buffer, length first"
      (isError (decodeInto decoder bad 3) .invalidLength)

def run : IO Unit := do
  let document ← IO.FS.readFile vectorFile
  checkCrateVectors document
  checkOddLengthTests document
  checkRoundTrips
  checkDocsExample
  checkCharacters
  checkBranches

end Base16ct.Tests
