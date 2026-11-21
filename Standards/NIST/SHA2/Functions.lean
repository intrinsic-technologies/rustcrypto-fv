import Standards.NIST.SHA2.Operations

/-!
# SHA-2 functions

The six functions of each word size in FIPS 180-4, §§4.1.2 and 4.1.3. The `SHA256` namespace holds
the 32-bit functions with the standard's superscript {256}, and the `SHA512` namespace holds the
64-bit functions with the superscript {512}, which SHA-384 also uses. The upper- and lower-case
sigma subscripts match the standard.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
-/

namespace Standards.NIST.SHA2

namespace SHA256

/-- Chooses bits from the second or third word (FIPS 180-4, equation 4.2). -/
def Ch (x y z : BitVec 32) : BitVec 32 :=
  (x &&& y) ^^^ (~~~x &&& z)

/-- Takes the majority at each bit position (FIPS 180-4, equation 4.3). -/
def Maj (x y z : BitVec 32) : BitVec 32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Mixes the first working variable by rotation (FIPS 180-4, equation 4.4). -/
def «Σ₀» (x : BitVec 32) : BitVec 32 :=
  ROTR 2 x ^^^ ROTR 13 x ^^^ ROTR 22 x

/-- Mixes the fifth working variable by rotation (FIPS 180-4, equation 4.5). -/
def «Σ₁» (x : BitVec 32) : BitVec 32 :=
  ROTR 6 x ^^^ ROTR 11 x ^^^ ROTR 25 x

/-- Mixes an earlier schedule word by rotation and shift (FIPS 180-4, equation 4.6). -/
def σ₀ (x : BitVec 32) : BitVec 32 :=
  ROTR 7 x ^^^ ROTR 18 x ^^^ SHR 3 x

/-- Mixes a recent schedule word by rotation and shift (FIPS 180-4, equation 4.7). -/
def σ₁ (x : BitVec 32) : BitVec 32 :=
  ROTR 17 x ^^^ ROTR 19 x ^^^ SHR 10 x

end SHA256

namespace SHA512

/-- Chooses bits from the second or third word (FIPS 180-4, equation 4.8). -/
def Ch (x y z : BitVec 64) : BitVec 64 :=
  (x &&& y) ^^^ (~~~x &&& z)

/-- Takes the majority at each bit position (FIPS 180-4, equation 4.9). -/
def Maj (x y z : BitVec 64) : BitVec 64 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Mixes the first working variable by rotation (FIPS 180-4, equation 4.10). -/
def «Σ₀» (x : BitVec 64) : BitVec 64 :=
  ROTR 28 x ^^^ ROTR 34 x ^^^ ROTR 39 x

/-- Mixes the fifth working variable by rotation (FIPS 180-4, equation 4.11). -/
def «Σ₁» (x : BitVec 64) : BitVec 64 :=
  ROTR 14 x ^^^ ROTR 18 x ^^^ ROTR 41 x

/-- Mixes an earlier schedule word by rotation and shift (FIPS 180-4, equation 4.12). -/
def σ₀ (x : BitVec 64) : BitVec 64 :=
  ROTR 1 x ^^^ ROTR 8 x ^^^ SHR 7 x

/-- Mixes a recent schedule word by rotation and shift (FIPS 180-4, equation 4.13). -/
def σ₁ (x : BitVec 64) : BitVec 64 :=
  ROTR 19 x ^^^ ROTR 61 x ^^^ SHR 6 x

end SHA512

end Standards.NIST.SHA2
