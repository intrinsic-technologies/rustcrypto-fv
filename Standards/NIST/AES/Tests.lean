import Standards.NIST.AES
import Standards.Tests.Utilities

/-!
# FIPS 197 tests

Spot checks from FIPS 197-upd1 (the §4.2 and §5.1.1 worked examples, the first rows of Tables 4
and 6, and two key-schedule words of Appendix A.1), from the original FIPS 197, which FIPS 197-upd1
supersedes (November 26, 2001; https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197.pdf: the §4.2
example {57} • {83} = {c1}, replaced in FIPS 197-upd1 according to its Appendix D, item 12, and the
Appendix C.1–C.3 example vectors, removed according to its Appendix D, item 23, in favor of NIST's
"examples with intermediate values"), and the unmodified ECB known-answer response files of the
NIST CAVP AES Algorithm Validation Suite (AESAVS §6.2, `KAT_AES.zip`):
https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/block-ciphers
The multi-block message and Monte Carlo tests of AESAVS §§6.3–6.4 are not used.

Each response file has an `[ENCRYPT]` and a `[DECRYPT]` section; every vector of the first is
checked with CIPHER, and the second is not used.
-/

namespace Standards.NIST.AES.Tests

open Standards.Tests Standards.NIST.AES

-- FIPS 197 (2001) §4.2: {57} • {83} = {c1}; FIPS 197-upd1 §4.2, Eq. (4.7): {57} • {13} = {fe}
#guard mul 0x57 0x83 == 0xc1
#guard mul 0x57 0x13 == 0xfe
-- The inverse of {53} is {ca} (not stated in the document: {53} • {ca} = {01}, Eq. (4.10));
-- §5.1.1 and Table 4: SBOX({53}) = {ed}
#guard mul 0x53 0xca == 0x01
#guard inverse 0x53 == 0xca
#guard sbox 0x53 == 0xed
#guard inverse 0 == 0
-- Table 4, row 0
#guard (List.range 16).map (fun i => sbox i.toUInt8) ==
  [0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76]
-- Table 6, row 0
#guard (List.range 16).map (fun i => invSbox i.toUInt8) ==
  [0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb]
#guard (List.range 256).all fun i => invSbox (sbox i.toUInt8) == i.toUInt8
#guard (List.range 256).all fun i => sbox (invSbox i.toUInt8) == i.toUInt8

private def bytes (n : Nat) (f : Nat → Nat) : Vector UInt8 n := Vector.ofFn fun i => (f i).toUInt8

private def key128 : Vector UInt8 16 := bytes 16 fun i => [0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2,
  0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c][i]!

-- FIPS 197-upd1 Appendix A.1: w[4] = a0fafe17 and w[43] = b6630ca6
#guard (keyExpansion .aes128 key128)[4] == #v[0xa0, 0xfa, 0xfe, 0x17]
#guard (keyExpansion .aes128 key128)[43] == #v[0xb6, 0x63, 0x0c, 0xa6]

private def sequential (n : Nat) (step : Nat) : Vector UInt8 n := bytes n fun i => step * i

-- FIPS 197 (2001) Appendix C.1–C.3: key 00 01 02 …, plaintext 00 11 22 … ff
private def plaintext : Block := sequential 16 0x11
#guard cipher .aes128 (sequential 16 1) plaintext ==
  bytes 16 fun i => [0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30, 0xd8, 0xcd, 0xb7, 0x80,
    0x70, 0xb4, 0xc5, 0x5a][i]!
#guard cipher .aes192 (sequential 24 1) plaintext ==
  bytes 16 fun i => [0xdd, 0xa9, 0x7c, 0xa4, 0x86, 0x4c, 0xdf, 0xe0, 0x6e, 0xaf, 0x70, 0xa0,
    0xec, 0x0d, 0x71, 0x91][i]!
#guard cipher .aes256 (sequential 32 1) plaintext ==
  bytes 16 fun i => [0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf, 0xea, 0xfc, 0x49, 0x90,
    0x4b, 0x49, 0x60, 0x89][i]!

private def vectors : System.FilePath := "Standards/NIST/AES/Vectors"

private def toVector (n : Nat) (bytes : ByteArray) (label : String) : IO (Vector UInt8 n) := do
  if h : bytes.data.size = n then return ⟨bytes.data, h⟩
  throw (IO.userError s!"{label}: expected {n} bytes, got {bytes.size}")

/-- Checks every vector of one response file; returns the number checked -/
private def responseFile (v : Variant) (name : String) : IO Nat := do
  let path := vectors / name
  let mut decrypt := false
  let mut count := 0
  let mut key : Option ByteArray := none
  let mut first : Option ByteArray := none
  for raw in (← IO.FS.readFile path).splitOn "\n" do
    let line := raw.trimAscii.toString
    if line == "[ENCRYPT]" then decrypt := false
    else if line == "[DECRYPT]" then decrypt := true
    match line.splitOn " = " with
    | ["KEY", k] => key := some (← hex k)
    | [field, value] =>
      if !decrypt && (field == "PLAINTEXT" || field == "CIPHERTEXT") then
        match first with
        | none => first := some (← hex value)
        | some input =>
          let label := s!"{path}, vector {count}"
          let some k := key | throw (IO.userError s!"{label}: missing key")
          let k ← toVector v.keyBytes k label
          let input ← toVector 16 input label
          let output ← toVector 16 (← hex value) label
          check s!"{label}: mismatch" (cipher v k input == output)
          first := none
          count := count + 1
    | _ => pure ()
  check s!"{path}: no vectors" (count > 0)
  return count

/-- Runs the FIPS 197 tests, throwing on the first failure -/
def run : IO Unit := do
  let mut total := 0
  for (v, bits) in [(Variant.aes128, 128), (.aes192, 192), (.aes256, 256)] do
    for kind in ["GFSbox", "KeySbox", "VarKey", "VarTxt"] do
      total := total + (← responseFile v s!"ECB{kind}{bits}.rsp")
  IO.println s!"FIPS 197: {total} CAVP ECB vectors passed"

end Standards.NIST.AES.Tests
