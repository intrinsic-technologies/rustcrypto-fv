/-!
# Bits, bytes, and words

The representations of RFC 1321, §2: a message is a sequence of bits, read as bytes with the
high-order bit of each byte first, and bytes are read as 32-bit words with the low-order byte
first.

Source: https://www.rfc-editor.org/rfc/rfc1321
-/

namespace Standards.RFC.MD5

/-- Each byte as eight bits, high-order bit first, the bit order of RFC 1321, §2 -/
def bitsOfBytes (bytes : ByteArray) : Array Bool :=
  bytes.data.flatMap fun byte => Array.ofFn fun i : Fin 8 => byte.toNat.testBit (7 - i.val)

/--
Each consecutive group of eight bits as a byte, high-order bit first (RFC 1321, §2). Trailing
bits that do not fill a byte are not read, which keeps the function total; the RFC does not say
this.
-/
def bytesOfBits (bits : Array Bool) : ByteArray :=
  ⟨Array.ofFn fun i : Fin (bits.size / 8) =>
    let group := bits.extract (8 * i.val) (8 * i.val + 8)
    group.foldl (fun byte bit => 2 * byte + if bit then 1 else 0) (0 : UInt8)⟩

/--
Each consecutive group of four bytes as a word, low-order byte first (RFC 1321, §2). Trailing
bytes that do not fill a word are not read, which keeps the function total; the RFC does not say
this.
-/
def wordsOfBytes (bytes : ByteArray) : Array (BitVec 32) :=
  Array.ofFn fun i : Fin (bytes.size / 4) =>
    let group := bytes.extract (4 * i.val) (4 * i.val + 4)
    group.data.foldr (fun byte word => (word <<< 8) ||| BitVec.ofNat 32 byte.toNat) (0 : BitVec 32)

/-- A word as four bytes, low-order byte first, the byte order of RFC 1321, §2 -/
def bytesOfWord (word : BitVec 32) : Vector UInt8 4 :=
  Vector.ofFn fun i => (word >>> (8 * i.val)).toNat.toUInt8

end Standards.RFC.MD5
