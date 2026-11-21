import Standards.NIST.SHA2.Functions

/-!
# SHA-1 functions and constants

The left rotation of FIPS 180-4, §3.2, and the SHA-1 logical functions and constants of §4.1.1
and §4.2.1. `Ch` and `Maj` are the 32-bit functions FIPS 180-4 defines alike for SHA-1 (§4.1.1)
and SHA-256 (§4.1.2), taken from `Standards.NIST.SHA2`.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
-/

namespace Standards.NIST.SHA1

open Standards.NIST.SHA2

/-- Rotates a `w`-bit word left by `n < w` positions (FIPS 180-4, §3.2) -/
def ROTL {w : Nat} (n : Nat) (x : BitVec w) : BitVec w := (x <<< n) ||| (x >>> (w - n))

/-- Bitwise parity of three words (FIPS 180-4, §4.1.1) -/
def Parity (x y z : BitVec 32) : BitVec 32 := x ^^^ y ^^^ z

/-- The logical function used in step `t` (FIPS 180-4, §4.1.1) -/
def f (t : Fin 80) (x y z : BitVec 32) : BitVec 32 :=
  if t.val ≤ 19 then SHA256.Ch x y z
  else if t.val ≤ 39 then Parity x y z
  else if t.val ≤ 59 then SHA256.Maj x y z
  else Parity x y z

/-- The constant word used in step `t` (FIPS 180-4, §4.2.1) -/
def K (t : Fin 80) : BitVec 32 :=
  if t.val ≤ 19 then 0x5a827999
  else if t.val ≤ 39 then 0x6ed9eba1
  else if t.val ≤ 59 then 0x8f1bbcdc
  else 0xca62c1d6

end Standards.NIST.SHA1
