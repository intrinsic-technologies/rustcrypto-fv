import Std

/-!
# Bit strings and words

Big-endian representations from FIPS 180-4, §3.1. Array and vector indices start at
the left-most bit; word arithmetic uses Lean's fixed-width bit vectors.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
-/

namespace Standards.NIST.SHA2

/-- Interprets a bit string as a word, most significant bit first (FIPS 180-4, §3.1). -/
def bitsToWord {w : Nat} (M : Vector Bool w) : BitVec w :=
  (BitVec.ofBoolListBE M.toList).cast (by simp)

/-- Expands a word into bits, most significant bit first (FIPS 180-4, §3.1). -/
def wordToBits {w : Nat} (x : BitVec w) : Vector Bool w :=
  Vector.ofFn fun j => x.getMsbD j.val

/--
Expands bytes in address order into a bit string, reading each byte most significant bit first,
as the message "abc" is read in the example of FIPS 180-4, §5.1.1.
-/
def bytesToBits (input : ByteArray) : Array Bool :=
  input.data.flatMap fun x => (wordToBits x.toBitVec).toArray

end Standards.NIST.SHA2
