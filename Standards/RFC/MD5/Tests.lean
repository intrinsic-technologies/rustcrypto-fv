import Standards.RFC.MD5
import Standards.Tests.Utilities

/-!
# RFC 1321 tests

The definitions against the unmodified RFC 1321 text, https://www.rfc-editor.org/rfc/rfc1321.txt,
with `messageDigest (bitsOfBytes input)` as the digest of a byte string.

| Source                  | Checks                                                                 |
| ----------------------- | ---------------------------------------------------------------------- |
| Appendix A.5            | The 7 digests of the test suite                                        |
| §3.3                    | The initial buffer                                                     |
| §3.4                    | The word index, rotation, and T index of each of the 64 operations, and the register order ABCD, DABC, CDAB, BCDA |
| §3.4, T[i]              | Each table entry against its definition, the integer part of 4294967296 times abs(sin(i)) |
| §3.4, block loop        | No words leave the buffer unchanged; processing two block sequences in turn equals processing their concatenation; the single padded block of "abc" gives its digest |

The register order is the one `processBlock` encodes in its rotation of (a, b, c, d), which is not
itself compared with the text.
-/

namespace Standards.RFC.MD5.Tests

open Standards.Tests Standards.RFC.MD5

private def hexDigit (n : Nat) : Char :=
  "0123456789abcdef".toList.getD n '?'

private def toHex (bytes : List UInt8) : String :=
  String.ofList (bytes.flatMap fun byte => [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)])

private def digestHex (input : ByteArray) : String :=
  toHex (messageDigest (bitsOfBytes input)).toList

/-- The text strictly between the first `start` and the next `stop` after it -/
private def between (text start stop : String) : String :=
  (((text.splitOn start).getD 1 "").splitOn stop).getD 0 ""

/--
The test suite of RFC 1321, Appendix A.5: lines `MD5 ("message") = digest`, some wrapped across
two lines, which are joined
-/
private def rfcTestSuite (text : String) : List (String × String) :=
  let suite := (text.splitOn "A.5 Test suite").getLast!
  (suite.splitOn "MD5 (\"").drop 1 |>.map fun entry =>
    let message := ((entry.splitOn "\") =").getD 0 "").replace "\n" ""
    let rest := (entry.splitOn "\") =").getD 1 ""
    let digest := String.ofList ((rest.toList.filter fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')).take 32)
    (message, digest)

/-- The operations `[abcd k s i]` printed in RFC 1321, §3.4, in order -/
private def rfcOperations (text : String) : List (String × Nat × Nat × Nat) :=
  let step4 := between text "3.4 Step 4." "3.5 Step 5."
  (step4.splitOn "[").drop 1 |>.filterMap fun entry =>
    match (((entry.splitOn "]").getD 0 "").splitOn " ").filter (· ≠ "") with
    | [registers, k, s, i] =>
      if registers.length == 4 && registers.toList.all fun c => "ABCD".toList.contains c then
        some (registers, k.toNat!, s.toNat!, i.toNat!)
      else none
    | _ => none

/-- The initial words printed in RFC 1321, §3.3, as bytes, low-order byte first -/
private def rfcInitialBytes (text : String) : ByteArray :=
  let step3 := between text "3.3 Step 3." "3.4 Step 4."
  let words := (step3.splitOn "word ").drop 1
  ⟨(words.flatMap fun word =>
    let hexBytes := ((((word.splitOn ":").getD 1 "").splitOn "\n").getD 0 "").splitOn " "
    hexBytes.filter (· ≠ "") |>.map fun byte =>
      (byte.toList.foldl (fun n (c : Char) => 16 * n + (if c.isDigit then c.toNat - '0'.toNat
        else c.toNat - 'a'.toNat + 10)) 0).toUInt8).toArray⟩

def run : IO Unit := do
  let rfc ← IO.FS.readFile "Standards/RFC/MD5/Vectors/rfc1321.txt"
  let suite := rfcTestSuite rfc
  check "RFC 1321 A.5 suite has 7 entries" (suite.length == 7)
  for (message, expected) in suite do
    check s!"RFC 1321 A.5 MD5 (\"{message}\")" (digestHex message.toUTF8 == expected)
  let initial := Buffer.initial
  check "initial buffer (§3.3)"
    (wordsOfBytes (rfcInitialBytes rfc) == #[initial.A, initial.B, initial.C, initial.D])
  let operations := rfcOperations rfc
  let transcribed := rounds.flatMap fun (_, operations) => operations.map fun (k, s) => (k.val, s)
  check "64 operations (§3.4)" (operations.length == 64)
  check "operation word indices and rotations (§3.4)"
    (operations.map (fun (_, k, s, _) => (k, s)) == transcribed)
  check "operations use T[1] to T[64] in order (§3.4)"
    (operations.map (fun (_, _, _, i) => i) == List.range' 1 64)
  check "operations update A, D, C, B in turn (§3.4)"
    (operations.zipIdx.all fun ((registers, _), j) => registers == ["ABCD", "DABC", "CDAB", "BCDA"][j % 4]!)
  for h : j in [0:64] do
    let i := j + 1
    let expected := (4294967296 * (Float.sin i.toFloat).abs).floor.toUInt64.toNat
    check s!"T[{i}] = integer part of 4294967296 * abs(sin({i}))" (T[j].toNat == expected)
  let words := wordsOfBytes (bitsOfBytes ("abc".toUTF8) |> appendPaddingBits |> appendLength 24 |> bytesOfBits)
  check "no words leave the buffer unchanged" (processBlocks initial #[] == initial)
  let blocks := wordsOfBytes (String.ofList (List.replicate 192 'x')).toUTF8
  check "processing blocks in turn equals processing their concatenation"
    (processBlocks (processBlocks initial (blocks.extract 0 16)) (blocks.extract 16 48) ==
      processBlocks initial blocks)
  check "one padded block gives the RFC 1321 digest of \"abc\""
    (toHex (processBlocks initial words).toBytes.toList == "900150983cd24fb0d6963f7d28e17f72")
  IO.println s!"RFC1321: {suite.length} test-suite digests, the constants, and the block loop passed"

end Standards.RFC.MD5.Tests
