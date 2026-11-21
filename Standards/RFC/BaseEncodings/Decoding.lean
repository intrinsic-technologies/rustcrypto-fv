import Standards.RFC.BaseEncodings.Encoding

/-!
# Base decoding

Decoding of RFC 4648, §§3.1–3.5, 4, 5, 6, and 8, the inverse of `encode`. Two decoders:

* `decode` accepts exactly the output of `encode`: pad characters as `encode` writes them (§3.2),
  only alphabet characters (§3.3), and zero pad bits (§3.5)
* `decodeIgnoringCase` is `decode` with letters read in either case. This is not an RFC 4648
  decoder: it accepts characters outside the alphabet, which §3.3 allows only when a referring
  specification says so

Each returns `none` for data it rejects.

Source: https://www.rfc-editor.org/rfc/rfc4648.html
-/

set_option autoImplicit false

namespace Standards.RFC.BaseEncodings

/--
Encoding characters of `encoded`, without its pad characters, or `none` if the padding is wrong
(RFC 4648, §§3.2, 4, and 6)

* `.padded`: the characters before the first `=`, followed by exactly the `alphabet.padLength` pad
  characters that `encode` writes after them, and nothing else. Missing, excess, or interior `=`
  are rejected.
* `.unpadded`: all of `encoded`; a `=` in it is outside the alphabet and rejected later (§3.3).
-/
def removePadding (alphabet : Alphabet) (padding : Padding) (encoded : ByteArray) :
    Option (List UInt8) :=
  let characters := encoded.data.toList
  match padding with
  | .unpadded => some characters
  | .padded =>
    let data := characters.takeWhile (· != pad)
    if characters = data ++ List.replicate (alphabet.padLength data.length) pad then
      some data
    else
      none

/--
Values of the encoding characters of `encoded`, or `none` if it is not encoded data apart from its
pad bits (RFC 4648, §§3.1–3.3, 4, 6, and 8)

1. Remove the pad characters (`removePadding`)
2. Replace each character with its value in the alphabet; reject a character outside it,
   including line feeds and other white space (§3.3: "Implementations MUST reject the encoded data
   if it contains characters outside the base alphabet when interpreting base-encoded data, unless
   the specification referring to this document explicitly states otherwise.")
3. Reject a number of characters that `encode` never produces: `n` characters carry
   `⌊bits · n / 8⌋` octets, and `encode` writes `n` characters only if those octets need all `n`.
   For base 64 this rejects `n ≡ 1 (mod 4)`; for base 32, `n ≡ 1, 3, 6 (mod 8)`; for base 16, odd
   `n`.
-/
def characterValues (alphabet : Alphabet) (padding : Padding) (encoded : ByteArray) :
    Option (List Nat) := do
  let data ← removePadding alphabet padding encoded
  let values ← data.mapM alphabet.value?
  if alphabet.encodedLength (alphabet.bits * values.length / 8) = values.length then
    some values
  else
    none

/--
Octets of the bit stream of character `values`: its whole 8-bit groups from left to right. The
remaining bits, fewer than `alphabet.bits` for values from `characterValues`, are the pad bits of
RFC 4648, §3.5, and are dropped.
-/
def octetsOf (alphabet : Alphabet) (values : List Nat) : ByteArray :=
  ⟨((regroup alphabet.bits 8 values (alphabet.bits * values.length / 8)).map UInt8.ofNat).toArray⟩

/--
Whether every pad bit of character `values` is zero: every bit of their stream after the last
whole octet (RFC 4648, §3.5: "These pad bits MUST be set to zero by conforming encoders")
-/
def padBitsZero (alphabet : Alphabet) (values : List Nat) : Bool :=
  let used := 8 * (alphabet.bits * values.length / 8)
  (List.range (alphabet.bits * values.length - used)).all fun j =>
    !streamBit alphabet.bits values (used + j)

/--
Base decoding (RFC 4648, §§3.1–3.3, 3.5, 4, 5, 6, and 8)

Parameters: an alphabet and whether the data is padded
Input: encoded data `encoded`, US-ASCII codes
Output: the octets it encodes, or `none`

1. Remove the pad characters, translate each character to its value, and check the number of
   characters (`characterValues`); reject on failure
2. Reject non-zero pad bits (§3.5: "decoders MAY chose to reject an encoding if the pad bits have
   not been set to zero")
3. Return the octets of the bit stream of the values (`octetsOf`)

For an alphabet meeting the assumptions stated on `Alphabet`, which every named alphabet does,
`decode` is meant to accept exactly the outputs of `encode`; this is not proved.
-/
def decode (alphabet : Alphabet) (padding : Padding) (encoded : ByteArray) : Option ByteArray := do
  let values ← characterValues alphabet padding encoded
  if padBitsZero alphabet values then some (octetsOf alphabet values) else none

/--
`c` with its US-ASCII letter case swapped (RFC 20); other characters are unchanged
-/
def swapCase (c : UInt8) : UInt8 :=
  if 'A'.toUInt8 ≤ c ∧ c ≤ 'Z'.toUInt8 then c + 0x20
  else if 'a'.toUInt8 ≤ c ∧ c ≤ 'z'.toUInt8 then c - 0x20
  else c

/--
Case-insensitive base decoding, a departure from RFC 4648, §3.3, that only a referring
specification can permit

`decode` after replacing each letter outside the alphabet with the same letter in the other case.
Table 5 lists uppercase letters only, so over `base16Upper` this accepts lowercase letters, which
are outside the alphabet; §3.3: "Implementations MUST reject the encoded data if it contains
characters outside the base alphabet when interpreting base-encoded data, unless the specification
referring to this document explicitly states otherwise." Only a referring specification that states
otherwise permits this decoder.

Over `base16Upper` or `base16Lower` it accepts letters in either case, mixed within one input.
-/
def decodeIgnoringCase (alphabet : Alphabet) (padding : Padding) (encoded : ByteArray) :
    Option ByteArray :=
  let matchCase (c : UInt8) := if alphabet.characters.contains c then c else swapCase c
  decode alphabet padding ⟨(encoded.data.toList.map matchCase).toArray⟩

end Standards.RFC.BaseEncodings
