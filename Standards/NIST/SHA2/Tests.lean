import Standards.NIST.SHA2
import Standards.Tests.Utilities

/-!
# FIPS 180-4 tests

The vectors are the unmodified bit- and byte-oriented SHA-224, SHA-256, SHA-384, SHA-512,
SHA-512/224, and SHA-512/256 response files of the NIST CAVP suites:
https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing

| Algorithm | Orientation | Short | Long | Monte Carlo checkpoints |
| --------- | ----------- | ----: | ---: | ----------------------: |
| SHA-224   | Bit         |   513 |  512 |                     100 |
| SHA-224   | Byte        |    65 |   64 |                     100 |
| SHA-256   | Bit         |   513 |  512 |                     100 |
| SHA-256   | Byte        |    65 |   64 |                     100 |
| SHA-384   | Bit         |  1025 | 1024 |                     100 |
| SHA-384   | Byte        |   129 |  128 |                     100 |
| SHA-512   | Bit         |  1025 | 1024 |                     100 |
| SHA-512   | Byte        |   129 |  128 |                     100 |
| SHA-512/224 | Bit       |  1025 | 1024 |                     100 |
| SHA-512/224 | Byte      |   129 |  128 |                     100 |
| SHA-512/256 | Bit       |  1025 | 1024 |                     100 |
| SHA-512/256 | Byte      |   129 |  128 |                     100 |

Each Monte Carlo suite performs 100,000 hashes following SHAVS §6.4. The byte-oriented message
vectors also check `SHA256.hashBytes`.
-/

namespace Standards.NIST.SHA2.Tests

open Standards.Tests Standards.NIST.SHA2

#guard bitsToWord (wordToBits (0xa103fe23 : BitVec 32)) == 0xa103fe23
#guard bitsToWord (wordToBits (0xa103fe2332ef301a : BitVec 64)) == 0xa103fe2332ef301a
#guard bitsToWord (wordToBits (0 : BitVec 0)) == 0
#guard ROTR 0 (0x80000001 : BitVec 32) == 0x80000001
#guard ROTR 31 (0x80000001 : BitVec 32) == 3
#guard ROTR 63 (0x8000000000000001 : BitVec 64) == 3
#guard ROTR 0 (0 : BitVec 0) == 0
#guard SHR 32 (0xffffffff : BitVec 32) == 0
#guard SHR 0 (0 : BitVec 0) == 0
#guard bytesToBits ⟨#[0x80, 0x01]⟩ ==
  #[true, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, true]

#guard SHA256.Ch 0xffff0000 0x12345678 0xabcdef01 == 0x1234ef01
#guard SHA256.Maj 0xffffffff 0 0x12345678 == 0x12345678
#guard SHA256.«Σ₀» 0 == 0 && SHA256.«Σ₁» 0 == 0 && SHA256.σ₀ 0 == 0 && SHA256.σ₁ 0 == 0
#guard SHA256.parse #[] == #[]
#guard SHA256.hashComputation #[] SHA256.«H⁽⁰⁾» == SHA256.«H⁽⁰⁾»
#guard (SHA256.pad #[]).size == 512
#guard (SHA256.parse (SHA256.pad (bytesToBits "abc".toUTF8)))[0]![0] == 0x61626380
#guard (SHA256.parse (SHA256.pad (bytesToBits "abc".toUTF8)))[0]![15] == 24

#guard SHA512.Ch 0xffffffff00000000 0x0123456789abcdef 0xfedcba9876543210 == 0x0123456776543210
#guard SHA512.Maj 0xffffffffffffffff 0 0x0123456789abcdef == 0x0123456789abcdef
#guard SHA512.«Σ₀» 0 == 0 && SHA512.«Σ₁» 0 == 0 && SHA512.σ₀ 0 == 0 && SHA512.σ₁ 0 == 0
#guard SHA512.σ₀ 1 == 0x8100000000000000 && SHA512.σ₁ 1 == 0x0000200000000008
#guard SHA512.parse #[] == #[]
#guard SHA512.hashComputation #[] SHA512.«H⁽⁰⁾» == SHA512.«H⁽⁰⁾»
#guard (SHA512.pad #[]).size == 1024
#guard (SHA512.pad (Array.replicate 896 false)).size == 2048
#guard (SHA512.parse (SHA512.pad (bytesToBits "abc".toUTF8)))[0]![0] == 0x6162638000000000
#guard (SHA512.parse (SHA512.pad (bytesToBits "abc".toUTF8)))[0]![15] == 24

/-- One hash function of FIPS 180-4, with what its tests need to know about it -/
structure Algorithm where
  /-- The standard's name, as in `SHA-256` -/
  name : String
  /-- The prefix of the vector file names, as in `SHA256` -/
  filePrefix : String
  byteCount : Nat
  hash : Array Bool → Digest byteCount
  /-- The function on octet strings, if any, checked against the byte-oriented vectors -/
  hashBytes : Option (ByteArray → ByteArray) := none
  pad : Array Bool → Array Bool
  blockBits : Nat
  lengthBits : Nat
  /-- Whether hashing the first half of the parsed blocks, then the rest, equals hashing them all -/
  continues : Array Bool → Bool
  /-- The number of short and long message vectors in the bit- and byte-oriented suites -/
  shortCount : Bool → Nat
  longCount : Bool → Nat

private def sha256 : Algorithm where
  name := "SHA-256"
  filePrefix := "SHA256"
  byteCount := 32
  hash := SHA256
  hashBytes := some SHA256.hashBytes
  pad := SHA256.pad
  blockBits := 512
  lengthBits := 64
  continues padded :=
    let M := SHA256.parse padded
    let split := M.size / 2
    SHA256.hashComputation (M.extract split M.size)
      (SHA256.hashComputation (M.extract 0 split) SHA256.«H⁽⁰⁾») ==
        SHA256.hashComputation M SHA256.«H⁽⁰⁾»
  shortCount byteOriented := if byteOriented then 65 else 513
  longCount byteOriented := if byteOriented then 64 else 512

private def sha224 : Algorithm where
  name := "SHA-224"
  filePrefix := "SHA224"
  byteCount := 28
  hash := SHA224
  pad := SHA256.pad
  blockBits := 512
  lengthBits := 64
  continues padded :=
    let M := SHA256.parse padded
    let split := M.size / 2
    SHA256.hashComputation (M.extract split M.size)
      (SHA256.hashComputation (M.extract 0 split) SHA224.«H⁽⁰⁾») ==
        SHA256.hashComputation M SHA224.«H⁽⁰⁾»
  shortCount byteOriented := if byteOriented then 65 else 513
  longCount byteOriented := if byteOriented then 64 else 512

private def sha384 : Algorithm where
  name := "SHA-384"
  filePrefix := "SHA384"
  byteCount := 48
  hash := SHA384
  pad := SHA512.pad
  blockBits := 1024
  lengthBits := 128
  continues padded :=
    let M := SHA512.parse padded
    let split := M.size / 2
    SHA512.hashComputation (M.extract split M.size)
      (SHA512.hashComputation (M.extract 0 split) SHA384.«H⁽⁰⁾») ==
        SHA512.hashComputation M SHA384.«H⁽⁰⁾»
  shortCount byteOriented := if byteOriented then 129 else 1025
  longCount byteOriented := if byteOriented then 128 else 1024

private def sha512 : Algorithm where
  name := "SHA-512"
  filePrefix := "SHA512"
  byteCount := 64
  hash := SHA512
  pad := SHA512.pad
  blockBits := 1024
  lengthBits := 128
  continues padded :=
    let M := SHA512.parse padded
    let split := M.size / 2
    SHA512.hashComputation (M.extract split M.size)
      (SHA512.hashComputation (M.extract 0 split) SHA512.«H⁽⁰⁾») ==
        SHA512.hashComputation M SHA512.«H⁽⁰⁾»
  shortCount byteOriented := if byteOriented then 129 else 1025
  longCount byteOriented := if byteOriented then 128 else 1024

private def sha512_224 : Algorithm where
  name := "SHA-512/224"
  filePrefix := "SHA512_224"
  byteCount := 28
  hash := SHA512_224
  pad := SHA512.pad
  blockBits := 1024
  lengthBits := 128
  continues padded :=
    let M := SHA512.parse padded
    let split := M.size / 2
    SHA512.hashComputation (M.extract split M.size)
      (SHA512.hashComputation (M.extract 0 split) SHA512_224.«H⁽⁰⁾») ==
        SHA512.hashComputation M SHA512_224.«H⁽⁰⁾»
  shortCount byteOriented := if byteOriented then 129 else 1025
  longCount byteOriented := if byteOriented then 128 else 1024

private def sha512_256 : Algorithm where
  name := "SHA-512/256"
  filePrefix := "SHA512_256"
  byteCount := 32
  hash := SHA512_256
  pad := SHA512.pad
  blockBits := 1024
  lengthBits := 128
  continues padded :=
    let M := SHA512.parse padded
    let split := M.size / 2
    SHA512.hashComputation (M.extract split M.size)
      (SHA512.hashComputation (M.extract 0 split) SHA512_256.«H⁽⁰⁾») ==
        SHA512.hashComputation M SHA512_256.«H⁽⁰⁾»
  shortCount byteOriented := if byteOriented then 129 else 1025
  longCount byteOriented := if byteOriented then 128 else 1024

def fields (path : System.FilePath) : IO (Array (String × String)) := do
  let mut result := #[]
  for raw in (← IO.FS.readFile path).splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" || line.startsWith "[L = " then continue
    match line.splitOn " = " with
    | [key, value] => result := result.push (key, value)
    | _ => throw (IO.userError s!"{path}: invalid line: {line}")
  return result

def field (data : Array (String × String)) (i : Nat) (key : String) : IO String := do
  let some (actual, value) := data[i]? | throw (IO.userError s!"Missing {key}")
  unless actual == key do throw (IO.userError s!"Expected {key}, got {actual}")
  return value

def number (value : String) : IO Nat := do
  let some n := value.toNat? | throw (IO.userError s!"Invalid number: {value}")
  return n

def checkDigest (algorithm : Algorithm) (actual : Digest algorithm.byteCount)
    (expected : String) (label : String) : IO Unit := do
  let expected ← hex expected
  unless actual.bytes.toArray == expected.data do
    throw (IO.userError s!"{label}: {algorithm.name} mismatch")

def messages (algorithm : Algorithm) (path : System.FilePath) (count : Nat)
    (byteOriented : Bool) : IO Unit := do
  let data ← fields path
  unless data.size == 3 * count do throw (IO.userError s!"{path}: incorrect vector count")
  for i in [:count] do
    let length ← number (← field data (3 * i) "Len")
    let message ← hex (← field data (3 * i + 1) "Msg")
    unless message.size == max 1 ((length + 7) / 8) &&
        (!byteOriented || length % 8 == 0) do
      throw (IO.userError s!"{path}: invalid message length")
    let bits := (bytesToBits message).extract 0 length
    let label := s!"{path}, vector {i}, Len = {length}"
    let expected ← field data (3 * i + 2) "MD"
    checkDigest algorithm (algorithm.hash bits) expected label
    if let (true, some hashBytes) := (byteOriented, algorithm.hashBytes) then
      unless hashBytes (message.extract 0 (length / 8)) == (← hex expected) do
        throw (IO.userError s!"{label}: {algorithm.name} hashBytes mismatch")
    let padded := algorithm.pad bits
    let lengthStart := padded.size - algorithm.lengthBits
    unless padded.size % algorithm.blockBits == 0 && padded.size > length &&
        padded.size - algorithm.blockBits ≤ length + algorithm.lengthBits &&
        padded.extract 0 length == bits && padded[length]! &&
        (padded.extract (length + 1) lengthStart).all (· == false) &&
        padded.extract lengthStart padded.size ==
          (wordToBits (BitVec.ofNat algorithm.lengthBits length)).toArray do
      throw (IO.userError s!"{label}: padding boundary")
    unless algorithm.continues padded do
      throw (IO.userError s!"{label}: block continuation")
  IO.println s!"{path}: {count} passed"

def monteCarlo (algorithm : Algorithm) (path : System.FilePath) : IO Unit := do
  let data ← fields path
  unless data.size == 201 do throw (IO.userError s!"{path}: incorrect checkpoint count")
  let seedBytes ← hex (← field data 0 "Seed")
  unless seedBytes.size == algorithm.byteCount do
    throw (IO.userError s!"{path}: invalid seed length")
  let mut seed := bytesToBits seedBytes
  for j in [:100] do
    let count ← number (← field data (1 + 2 * j) "COUNT")
    unless count == j do throw (IO.userError s!"{path}: incorrect COUNT")
    -- SHAVS §6.4: MD₀ = MD₁ = MD₂ = Seed, then MDᵢ = SHA(MDᵢ₋₃ || MDᵢ₋₂ || MDᵢ₋₁).
    let mut a := seed
    let mut b := seed
    let mut c := seed
    let mut digest : Digest algorithm.byteCount := ⟨Vector.replicate algorithm.byteCount 0⟩
    for _ in [:1000] do
      digest := algorithm.hash (a ++ b ++ c)
      a := b
      b := c
      c := bytesToBits ⟨digest.bytes.toArray⟩
    checkDigest algorithm digest (← field data (2 + 2 * j) "MD") s!"{path}, COUNT = {j}"
    seed := c
    if (j + 1) % 10 == 0 then IO.println s!"{path}: {j + 1}/100 checkpoints passed"

def run : IO Unit := do
  checkDigest sha224 (SHA224 (bytesToBits "abc".toUTF8))
    "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7" "abc"
  checkDigest sha256 (SHA256 (bytesToBits "abc".toUTF8))
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" "abc"
  checkDigest sha384 (SHA384 (bytesToBits "abc".toUTF8))
    ("cb00753f45a35e8bb5a03d699ac65007272c32ab0eded163" ++
      "1a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7") "abc"
  checkDigest sha512 (SHA512 (bytesToBits "abc".toUTF8))
    ("ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a" ++
      "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f") "abc"
  checkDigest sha512_224 (SHA512_224 (bytesToBits "abc".toUTF8))
    "4634270f707b6a54daae7530460842e20e37ed265ceee9a43e8924aa" "abc"
  checkDigest sha512_256 (SHA512_256 (bytesToBits "abc".toUTF8))
    "53048e2681941ef99b2e29b76b4c7dabe4c2d0c634fc6d46e0e2f13107e7af23" "abc"
  let algorithms := [sha224, sha256, sha384, sha512]
  let algorithms := algorithms ++ [sha512_224, sha512_256]
  let mut jobs := #[]
  let mut messageCount := 0
  for algorithm in algorithms do
    for (orientation, byteOriented) in [("Bit", false), ("Byte", true)] do
      let short := algorithm.shortCount byteOriented
      let long := algorithm.longCount byteOriented
      messageCount := messageCount + short + long
      let job ← IO.asTask do
        let dir := System.FilePath.mk "Standards/NIST/SHA2/Vectors" / orientation
        messages algorithm (dir / s!"{algorithm.filePrefix}ShortMsg.rsp") short byteOriented
        messages algorithm (dir / s!"{algorithm.filePrefix}LongMsg.rsp") long byteOriented
        monteCarlo algorithm (dir / s!"{algorithm.filePrefix}Monte.rsp")
      jobs := jobs.push job
  for job in jobs do
    IO.ofExcept job.get
  let checkpoints := 100 * jobs.size
  IO.println s!"Passed {messageCount} NIST message vectors and {checkpoints} Monte Carlo \
    checkpoints ({1000 * checkpoints} hashes), padding, continuation, and octet-string checks"

end Standards.NIST.SHA2.Tests
