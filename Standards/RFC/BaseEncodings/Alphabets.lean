/-!
# Base encoding alphabets

The base 16 alphabet of RFC 4648, Table 5 (§8), with its lowercase form (§3.4), the pad character,
and the padding choice. Characters are US-ASCII codes (RFC 20), one octet each.

Source: https://www.rfc-editor.org/rfc/rfc4648.html
-/

set_option autoImplicit false

namespace Standards.RFC.BaseEncodings

/--
A base encoding alphabet (RFC 4648, §§4, 5, 6, and 8)

* `bits`: the number of bits each character represents: 6 for base 64 (§4: "enabling 6 bits to be
  represented per printable character"), 5 for base 32 (§6), and 4 for base 16 (§8)
* `characters`: the `2 ^ bits` characters in value order, as US-ASCII codes; the character at
  position `i` encodes the value `i`

The structure itself is unconstrained: any `bits` and any list of characters form an `Alphabet`.
These definitions assume `bits` from 1 to 8, exactly `2 ^ bits` characters, all distinct, none of
them `=`, and only the named alphabets below are claimed to meet these conditions.
-/
structure Alphabet where
  bits : Nat
  characters : List UInt8
  deriving DecidableEq, Repr

namespace Alphabet

/--
Number of characters in an encoding quantum: the fewest characters that hold a whole number of
octets, `lcm(8, bits) / bits`. RFC 4648 encodes "24-bit groups of input bits as output strings of
4 encoded characters" (§4), "40-bit groups of input bits as output strings of 8 encoded
characters" (§6), and "8-bit groups (octets) of input bits as output strings of 2 encoded
characters" (§8).
-/
def quantum (alphabet : Alphabet) : Nat :=
  Nat.lcm 8 alphabet.bits / alphabet.bits

/--
Character that encodes `value` (RFC 4648, §§4, 6, and 8): "Each 6-bit group is used as an index
into an array of 64 printable characters. The character referenced by the index is placed in the
output string." The encoder passes only values below `2 ^ bits`, so the default `0` is unused.
-/
def character (alphabet : Alphabet) (value : Nat) : UInt8 :=
  alphabet.characters.getD value 0

/--
Value a character encodes: its position in the alphabet, or `none` for a character outside it,
which a decoder rejects (RFC 4648, §3.3).
-/
def value? (alphabet : Alphabet) (character : UInt8) : Option Nat :=
  alphabet.characters.idxOf? character

/--
Table 5, "The Base 16 Alphabet" (RFC 4648, §8): `0`–`9`, `A`–`F`
-/
def base16Upper : Alphabet where
  bits := 4
  characters := "0123456789ABCDEF".toList.map Char.toUInt8

/--
Lowercase base 16 alphabet: Table 5 with `a`–`f` for `A`–`F`. RFC 4648 defines no lowercase table;
§3.4 lets the application choose the case: "For base 16 and base 32, this determines the use of
upper- or lowercase alphabets."
-/
def base16Lower : Alphabet where
  bits := 4
  characters := "0123456789abcdef".toList.map Char.toUInt8

end Alphabet

/--
The pad character `=` (RFC 4648, Tables 1, 2, and 3: "(pad) ="). It is outside every alphabet.
-/
def pad : UInt8 := '='.toUInt8

/--
Whether encoded data ends with pad characters (RFC 4648, §3.2)

§3.2: "Implementations MUST include appropriate pad characters at the end of encoded data unless
the specification referring to this document explicitly states otherwise." Base 16 never needs
pad characters (§8), so both choices give the same base 16 encoding.
-/
inductive Padding where
  /-- `=` characters complete the final quantum (§4 cases (2) and (3), §6 cases (2)–(5)) -/
  | padded
  /-- The pad characters are omitted, as a referring specification may direct (§3.2) -/
  | unpadded
  deriving DecidableEq, Repr

end Standards.RFC.BaseEncodings
