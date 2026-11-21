import Standards.NIST.SHA2.Representation

/-!
# Operations on words

The named word operations used by SHA-2 (FIPS 180-4, §§2.2.2 and 3.2).
Bitwise logic and addition modulo `2^w` use the operations on `BitVec w`. The standard defines
`SHR` and `ROTR` for `0 ≤ n < w`; these definitions are total, SHA-256 uses `n < 32` on 32-bit
words, and SHA-384 and SHA-512 use `n < 64` on 64-bit words.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
-/

namespace Standards.NIST.SHA2

/-- Shifts a word right, filling with zero bits (FIPS 180-4, §3.2, operation 3). -/
def SHR {w : Nat} (n : Nat) (x : BitVec w) : BitVec w :=
  x >>> n

/-- Rotates a word right by the given number of bits (FIPS 180-4, §3.2, operation 4). -/
def ROTR {w : Nat} (n : Nat) (x : BitVec w) : BitVec w :=
  x.rotateRight n

end Standards.NIST.SHA2
