import Standards.RFC.MD5.Conversion

/-!
# Padding and length

Steps 1 and 2 of RFC 1321, §3.1 and §3.2: the message is extended to a multiple of 512 bits by
padding bits and the 64-bit length of the original message.

Source: https://www.rfc-editor.org/rfc/rfc1321
-/

namespace Standards.RFC.MD5

/--
Appends a single "1" bit, then "0" bits until the length in bits is congruent to 448 modulo 512;
always appends between 1 and 512 bits (RFC 1321, §3.1)
-/
def appendPaddingBits (message : Array Bool) : Array Bool :=
  let zeroCount := ((447 - (message.size : Int)) % 512).toNat
  message.push true ++ Array.replicate zeroCount false

/--
Appends the low-order 64 bits of the original message length `b`, as two words, low-order word
first, each in the bit order of §2 (RFC 1321, §3.2)
-/
def appendLength (b : Nat) (padded : Array Bool) : Array Bool :=
  let length := b % 2 ^ 64
  let lowWord : BitVec 32 := BitVec.ofNat 32 length
  let highWord : BitVec 32 := BitVec.ofNat 32 (length / 2 ^ 32)
  padded ++ bitsOfBytes ⟨(bytesOfWord lowWord ++ bytesOfWord highWord).toArray⟩

end Standards.RFC.MD5
