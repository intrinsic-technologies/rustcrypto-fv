import Standards.RFC.BaseEncodings.Alphabets

/-!
# Base encoding

Encoding of RFC 4648, §§3.1, 3.2, 3.5, 4, 5, 6, and 8, over any of the alphabets of
`Standards.RFC.BaseEncodings.Alphabets`. Input is octets; output is US-ASCII character codes.

Source: https://www.rfc-editor.org/rfc/rfc4648.html
-/

set_option autoImplicit false

namespace Standards.RFC.BaseEncodings

/--
Bit `position` of the bit stream formed by `values`, each `width` bits wide, most significant bit
first; bits past the end of the stream are zero

RFC 4648, §6: "When a bit stream is encoded via the base 32 encoding, the bit stream must be
presumed to be ordered with the most-significant-bit first. That is, the first bit in the stream
will be the high-order bit in the first 8bit byte, the eighth bit will be the low-order bit in
the first 8bit byte, and so on." §§4 and 8 do not state the order in words; §9 pictures it for
base 64, with bit 7 of the first octet as the first bit of the first index. The zero bits past the
end are those that §4 and §6 add "on the right" to complete the last group.
-/
def streamBit (width : Nat) (values : List Nat) (position : Nat) : Bool :=
  (values.getD (position / width) 0).testBit (width - 1 - position % width)

/--
Number whose `width` binary digits, most significant first, are `bit 0`, …, `bit (width - 1)`
-/
def ofBits (width : Nat) (bit : Nat → Bool) : Nat :=
  (List.range width).foldl (fun value j => 2 * value + (bit j).toNat) 0

/--
The first `count` groups of `toWidth` consecutive bits of the stream of `values`, each value
`fromWidth` bits wide, read from left to right. RFC 4648, §4: "Proceeding from left to right, a
24-bit input group is formed by concatenating 3 8-bit input groups. These 24 bits are then treated
as 4 concatenated 6-bit groups"; §6 says the same of 40-bit groups and 5-bit groups, and §8 of
8-bit inputs and 4-bit groups.
-/
def regroup (fromWidth toWidth : Nat) (values : List Nat) (count : Nat) : List Nat :=
  (List.range count).map fun i =>
    ofBits toWidth fun j => streamBit fromWidth values (toWidth * i + j)

/--
Number of encoding characters for `octets` input octets, before padding: `⌈8 · octets / bits⌉`,
the characters needed for the input bits plus the zero bits that complete the last group
(RFC 4648, §4: "bits with value zero are added (on the right) to form an integral number of 6-bit
groups"; §6 likewise for 5-bit groups)
-/
def Alphabet.encodedLength (alphabet : Alphabet) (octets : Nat) : Nat :=
  (8 * octets + alphabet.bits - 1) / alphabet.bits

/--
Number of pad characters after `characters` encoding characters: enough to complete the final
quantum (RFC 4648, §§4 and 6, final-quantum cases), so base 64 gets 0, 2, or 1 and base 32 gets
0, 6, 4, 3, or 1; base 16 gets none (§8)
-/
def Alphabet.padLength (alphabet : Alphabet) (characters : Nat) : Nat :=
  (alphabet.quantum - characters % alphabet.quantum) % alphabet.quantum

/--
Base encoding (RFC 4648, §§3.1, 3.2, 3.5, 4, 5, 6, and 8)

Parameters: an alphabet (Table 1, 2, 3, or 5, or lowercase base 16) and whether to pad
Input: octets `input`
Output: the encoded data, US-ASCII codes

1. Read `input` as a bit stream, most significant bit of each octet first
2. Add zero bits on the right to a whole number of `alphabet.bits`-bit groups (§§4, 6); these are
   the pad bits of §3.5, which "MUST be set to zero by conforming encoders"
3. Replace each group, from left to right, with the character at its value in the alphabet
4. If `padding` is `.padded`, append `=` until the length is a multiple of the quantum: 4
   characters for base 64 (§4), 8 for base 32 (§6), and 2 for base 16, which never needs any (§8)
5. Add no line feeds (§3.1: "Implementations MUST NOT add line feeds to base-encoded data unless
   the specification referring to this document explicitly directs base encoders to add line
   feeds after a specific number of characters")

The empty input gives the empty output (§10: `BASE64("") = ""`).
-/
def encode (alphabet : Alphabet) (padding : Padding) (input : ByteArray) : ByteArray :=
  let count := alphabet.encodedLength input.size
  let groups := regroup 8 alphabet.bits (input.data.toList.map (·.toNat)) count
  let characters := groups.map alphabet.character
  let pads := match padding with
    | .padded => alphabet.padLength count
    | .unpadded => 0
  ⟨(characters ++ List.replicate pads pad).toArray⟩

end Standards.RFC.BaseEncodings
