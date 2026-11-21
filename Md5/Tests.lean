import Md5.Spec
import Standards.Tests.Utilities

/-!
# `md-5` tests

Executable checks of the specification, run by `cd Md5 && lake test` (`Md5` is its own Lake
package). The RFC 1321 definitions are tested against the RFC's text in
`Standards/RFC/MD5/Tests.lean`; here, `MD5.messageDigest (MD5.bitsOfBytes input)` is the digest of a
byte string, as in the statements.

Sources and checks:

* `Tests/Vectors/md5_kat.blb`: the 6 known-answer tests of `md-5` 0.11.0
  (`tests/data/md5_kat.blb`, unmodified, `blobby` 0.4 format, input and digest pairs), through the
  RFC 1321 definitions.
* `Tests/Generated/md5_lengths.txt`: 201 digests by Python's `hashlib`, from `generate.py`, of the
  first 0 to 200 bytes of the pattern `i % 251`: every padding case (a tail of 0 to 63 bytes, one
  or two final blocks) and up to three whole blocks, through the RFC 1321 definitions.
* `Tests/Generated/md5_long.txt`: 66 digests, from `generate_long.py`, of messages of at least 2^32
  bits: 2^23 or more whole blocks and a tail of n bytes. The padding encodes the length modulo 2^64,
  which has a nonzero high word on 54 lines; the other 12, counts 2^58 + 1 and 2^63, encode 512 + 8n
  and 8n. Each line gives the MD buffer the whole blocks leave and their number, low-order byte
  first; the test runs RFC 1321's §3.1 and §3.2 padding of the tail with the message's whole length
  in bits, the §3.4 block loop from that buffer, and the §3.5 output. 12 take every value from
  Python's `hashlib`, extending the hash of 2^23 - 1 and 2^23 zero blocks with their padding; 54
  take counts from 2^32 - 1 to 2^64 - 1, and for the 36 from 2^57 - 1 up, the length wraps at 2^64.
  Their digests come from the generator's own RFC 1321 code, which it checks against `hashlib`.
* `Tests/Generated/md5_bits.txt`: 1041 digests, from `generate_bits.py`, of the first 0 to 1040 bits
  of the same pattern, high-order bit first (RFC 1321, §2), through the RFC 1321 definitions
  directly: every bit length modulo 8, which no theorem uses, since every theorem hashes whole
  bytes, and every padding case of one and two blocks, including 447 and 959 bits, where §3.1
  appends a single 1 bit and no 0 bits. Python's `hashlib` takes whole bytes only, so these digests
  come from the generator's own RFC 1321 code, which it checks against `hashlib` on the 131
  whole-byte lengths; the other 910 rest on that code alone. Each length also checks
  `appendPaddingBits` against §3.1's definition: one 1 bit, then fewer than 512 0 bits, to 448
  modulo 512.
* `md-5` 0.11.0 `tests/mod.rs`, `md5_rand`: 16 MiB of the `digest` crate's xorshift test data,
  each 1024 bytes followed by the byte `42`, give the crate's expected digest `61aec26f…0977`,
  through RFC 1321's steps with the §3.4 block loop run over the message's whole blocks in pieces.
* The slices of the entry-point contracts: `Slices.message`, `Slices.firstMessage` and
  `Slices.secondMessage` on split, empty and out-of-range inputs. The reset theorems' example,
  parts `abc`, `message `, `digest` with first count 1, gives the digest of `message digest`, which
  differs from the digest of all three parts that a reset keeping the first message would give. A
  first count of 0 puts every slice in the second message.

The RFC 1321 definitions' `messageDigest` is not run on a message of 2^32 bits or more; its length
encoding at those lengths is checked only through `md5_long.txt`. The crate's `Md5` and `Md5Core`
states are not specified, so no test checks how the crate's hasher buffers bytes or counts blocks,
and the crate's `tests/data/md5_serialization.bin`, its record of that state, is not used. No test
runs the extracted code.
-/

namespace Md5.Tests

open Standards.Tests Standards.RFC Md5.Spec Md5.Spec.Program

private def vectors : System.FilePath := "Md5/Tests/Vectors"

private def generated : System.FilePath := "Md5/Tests/Generated"

private def digest (input : ByteArray) : Vector UInt8 16 :=
  MD5.messageDigest (MD5.bitsOfBytes input)

private def bytesOf (vector : Vector UInt8 n) : ByteArray := ⟨vector.toArray⟩

/-- A `blobby` variable-length quantity: big-endian 7-bit groups, each continuation adding one -/
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

/-- The blobs of a `blobby` 0.4 file: blob and dedup counts, the dedup table, then the blobs -/
private def blobs (data : ByteArray) : Array ByteArray := Id.run do
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
      result := result.push (dedup.getD (value / 2) .empty)
      position := next
    else
      result := result.push (data.extract next (next + value / 2))
      position := next + value / 2
  return result

/--
RFC 1321 from the MD buffer that a message's whole blocks leave: §3.1 and §3.2 padding of the
message's last bytes `tail`, with the whole message's length `messageBits` in bits, then the §3.4
block loop from `buffer`, and the §3.5 output
-/
private def finishFrom (buffer : MD5.Buffer) (messageBits : Nat) (tail : ByteArray) :
    Vector UInt8 16 :=
  let padded := MD5.appendLength messageBits (MD5.appendPaddingBits (MD5.bitsOfBytes tail))
  (MD5.processBlocks buffer (MD5.wordsOfBytes (MD5.bytesOfBits padded))).toBytes

/--
A line of `md5_long.txt`: the MD buffer words A to D from bytes 0 to 15 and the block count from
bytes 16 to 23, each low-order byte first, as `generate_long.py` writes them
-/
private def readBufferAndCount (bytes : ByteArray) : MD5.Buffer × Nat :=
  let word := fun (i : Nat) => (List.range 4).foldr
    (fun j (w : BitVec 32) => (w <<< 8) ||| BitVec.ofNat 32 (bytes.get! (4 * i + j)).toNat) 0
  let count := (List.range 8).foldr (fun j n => n * 256 + (bytes.get! (16 + j)).toNat) 0
  (⟨word 0, word 1, word 2, word 3⟩, count)

/-- The pattern of `generate.py`: byte `i` is `i % 251` -/
private def pattern (length : Nat) : ByteArray :=
  ⟨Array.ofFn fun i : Fin length => (i.val % 251).toUInt8⟩

/-- The `digest` crate's test xorshift generator, `src/dev/rng.rs`: the state x, y, z, w -/
private def nextWord (state : UInt32 × UInt32 × UInt32 × UInt32) :
    UInt32 × (UInt32 × UInt32 × UInt32 × UInt32) :=
  let (x, y, z, w) := state
  let t := x ^^^ (x <<< 11)
  let next := w ^^^ (w >>> 19) ^^^ (t ^^^ (t >>> 8))
  (next, (y, z, w, next))

/--
The digest of the `md5_rand` test's message, 16384 times 1024 random bytes then `42`: the §3.4
block loop over its whole blocks, 1024 blocks at a time, then `finishFrom` with the rest
-/
private def randDigest : Vector UInt8 16 := Id.run do
  let mut rng : UInt32 × UInt32 × UInt32 × UInt32 :=
    (0x07873B4A, 0xFAAB8FFE, 0x1745980F, 0xB0ADB4F3)
  let mut message := ByteArray.emptyWithCapacity (16384 * 1025)
  for _ in [0:16384] do
    for _ in [0:256] do
      let (word, next) := nextWord rng
      rng := next
      message := message.push word.toUInt8 |>.push (word >>> 8).toUInt8
        |>.push (word >>> 16).toUInt8 |>.push (word >>> 24).toUInt8
    message := message.push 42
  let wholeBytes := 64 * (message.size / 64)
  let mut buffer := MD5.Buffer.initial
  for start in [0:wholeBytes:65536] do
    buffer := MD5.processBlocks buffer
      (MD5.wordsOfBytes (message.extract start (min (start + 65536) wholeBytes)))
  return finishFrom buffer (8 * message.size) (message.extract wholeBytes message.size)

/-- Runs every `md-5` test, throwing on the first failure -/
def run : IO Unit := do
  -- The crate's known-answer tests
  let kat := blobs (← IO.FS.readBinFile (vectors / "md5_kat.blb"))
  check "md5_kat.blb has 6 input and digest pairs" (kat.size == 12)
  for i in [0:kat.size / 2] do
    let input := kat[2 * i]!
    let expected := kat[2 * i + 1]!
    check s!"md5_kat.blb vector {i}: RFC 1321 specification" (bytesOf (digest input) == expected)
  -- Generated lengths
  let lines := ((← IO.FS.readFile (generated / "md5_lengths.txt")).splitOn "\n").filter
    fun line => line ≠ "" && !line.startsWith "#"
  check "md5_lengths.txt has 201 digests" (lines.length == 201)
  for line in lines do
    match line.splitOn " " with
    | [length, expectedHex] =>
      let n := length.toNat!
      let input := pattern n
      let expected ← hex expectedHex
      check s!"{n} bytes: RFC 1321 specification" (bytesOf (digest input) == expected)
    | _ => check s!"md5_lengths.txt line: {line}" false
  -- Generated digests of messages of 2^23 and more whole blocks
  let long := ((← IO.FS.readFile (generated / "md5_long.txt")).splitOn "\n").filter
    fun line => line ≠ "" && !line.startsWith "#"
  check "md5_long.txt has 66 digests" (long.length == 66)
  for line in long do
    match line.splitOn " " with
    | [source, coreHex, length, expectedHex] =>
      let coreBytes ← hex coreHex
      let (buffer, count) := readBufferAndCount coreBytes
      let n := length.toNat!
      check s!"md5_long.txt {source} {coreHex} {length}: RFC 1321 padding and block loop"
        (coreBytes.size == 24 &&
          bytesOf (finishFrom buffer (8 * (64 * count + n)) (pattern n)) == (← hex expectedHex))
    | _ => check s!"md5_long.txt line: {line}" false
  -- Generated digests of bit strings, every bit length from 0 to 1040
  let bitLines := ((← IO.FS.readFile (generated / "md5_bits.txt")).splitOn "\n").filter
    fun line => line ≠ "" && !line.startsWith "#"
  check "md5_bits.txt has 1041 digests" (bitLines.length == 1041)
  let patternBits := MD5.bitsOfBytes (pattern 200)
  for line in bitLines do
    match line.splitOn " " with
    | [length, expectedHex] =>
      let n := length.toNat!
      let message := patternBits.extract 0 n
      let padded := MD5.appendPaddingBits message
      check s!"{n} bits: RFC 1321 §3.1 padding, one 1 bit, then 0 to 511 0 bits, to 448 mod 512"
        (message.size == n && n < padded.size && padded.size ≤ n + 512 &&
          padded.size % 512 == 448 && padded.extract 0 n == message && padded[n]! &&
          (padded.extract (n + 1) padded.size).all (· == false))
      check s!"{n} bits: RFC 1321 specification"
        (bytesOf (MD5.messageDigest message) == (← hex expectedHex))
    | _ => check s!"md5_bits.txt line: {line}" false
  -- The input slices
  let slices : Array Slices.Input :=
    #[⟨1, "message ".toUTF8⟩, ⟨2, ByteArray.empty⟩, ⟨3, "dig".toUTF8⟩, ⟨1, "est".toUTF8⟩]
  check "no slices form the empty message" (Slices.message #[]).isEmpty
  check "slices concatenate in order" ((Slices.message slices).data == "message digest".toUTF8.data)
  check "the digest of split slices is the RFC 1321 digest of \"message digest\""
    (bytesOf (digest (Slices.message slices)) == (← hex "f96b697d7cb7938d525a2f31aaf161d0"))
  check "a first count of 2 splits the slices into \"message \" and \"digest\""
    ((Slices.firstMessage slices 2).data == "message ".toUTF8.data &&
      (Slices.secondMessage slices 2).data == "digest".toUTF8.data)
  check "a first count of 0 puts every slice in the second message"
    ((Slices.firstMessage slices 0).isEmpty &&
      (Slices.secondMessage slices 0).data == "message digest".toUTF8.data)
  check "a first count above the number of slices puts every slice in the first message"
    ((Slices.firstMessage slices 9).data == "message digest".toUTF8.data &&
      (Slices.secondMessage slices 9).isEmpty)
  -- The reset theorems' specification: the second message alone, a non-empty first message dropped
  let resetSlices : Array Slices.Input :=
    #[⟨1, "abc".toUTF8⟩, ⟨2, "message ".toUTF8⟩, ⟨3, "digest".toUTF8⟩]
  check "reset example: first count 1 gives the digest of \"message digest\" alone"
    (bytesOf (digest (Slices.secondMessage resetSlices 1)) ==
      (← hex "f96b697d7cb7938d525a2f31aaf161d0"))
  check "reset example: a reset that kept \"abc\" would give the digest of \"abcmessage digest\""
    (bytesOf (digest (Slices.message resetSlices)) == (← hex "87ceb124f832ecab8eafb16e7d7448f4") &&
      digest (Slices.message resetSlices) != digest (Slices.secondMessage resetSlices 1))
  check "two-message example: first count 1 gives the digest of \"abc\" first"
    (bytesOf (digest (Slices.firstMessage resetSlices 1)) ==
      (← hex "900150983cd24fb0d6963f7d28e17f72"))
  -- The crate's md5_rand test
  check "md5_rand: 16 MiB of xorshift data give the crate's digest"
    (bytesOf randDigest == (← hex "61aec26f1b909578ef638ae02dac0977"))
  IO.println s!"md-5: {kat.size / 2} crate vectors, {lines.length} generated digests, \
    {bitLines.length} bit-string digests, {long.length} long-message digests, the slices and \
    md5_rand passed"

end Md5.Tests
