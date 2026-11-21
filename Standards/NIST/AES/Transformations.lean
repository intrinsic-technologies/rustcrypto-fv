import Standards.NIST.AES.Field

/-!
# FIPS 197-upd1 §§3.4 and 5.1–5.3: the state and its transformations

A `Block` holds the 16 bytes of an input, output, or state in the order of FIPS 197-upd1 §3.4,
Eq. (3.6): byte `r + 4c` is the state byte s[r, c] in row `r` and column `c`.
FIPS 197 in the docstrings is FIPS 197-upd1.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf
-/

namespace Standards.NIST.AES

/-- A 16-byte input, output, or state; byte `r + 4c` is s[r, c] (FIPS 197 §3.4) -/
abbrev Block := Vector UInt8 16

/-- Left rotation of the bits of a byte by `n`, so bit `i` of the result is bit `i − n mod 8` -/
def rotateLeft (b : UInt8) (n : Nat) : UInt8 :=
  (b <<< (n % 8).toUInt8) ||| (b >>> ((8 - n % 8) % 8).toUInt8)

/--
The affine transformation of FIPS 197 §5.1.1, Eq. (5.3):
b′ᵢ = bᵢ ⊕ b₍ᵢ₊₄₎ ⊕ b₍ᵢ₊₅₎ ⊕ b₍ᵢ₊₆₎ ⊕ b₍ᵢ₊₇₎ ⊕ cᵢ with c = 63, indices modulo 8.
Bit `i + k` of `b` is bit `i` of `b` rotated left by `8 − k`.
-/
def affine (b : UInt8) : UInt8 :=
  b ^^^ rotateLeft b 4 ^^^ rotateLeft b 3 ^^^ rotateLeft b 2 ^^^ rotateLeft b 1 ^^^ 0x63

/--
The inverse of `affine`: b′ᵢ = b₍ᵢ₊₂₎ ⊕ b₍ᵢ₊₅₎ ⊕ b₍ᵢ₊₇₎ ⊕ dᵢ with d = 05. FIPS 197 §5.3.2
defines INVSBOX as the inverse of SBOX (Table 6) without stating this formula.
-/
def invAffine (b : UInt8) : UInt8 :=
  rotateLeft b 6 ^^^ rotateLeft b 3 ^^^ rotateLeft b 1 ^^^ 0x05

/--
SBOX, FIPS 197 §5.1.1: the multiplicative inverse (Eq. (5.2)) followed by the affine
transformation (Eq. (5.3)); computed from this definition, not transcribed from Table 4
-/
def sbox (b : UInt8) : UInt8 := affine (inverse b)

/--
INVSBOX, FIPS 197 §5.3.2, the inverse of SBOX: the inverse of the affine transformation followed
by the multiplicative inverse; computed, not transcribed from Table 6
-/
def invSbox (b : UInt8) : UInt8 := inverse (invAffine b)

/-- SUBBYTES, FIPS 197 §5.1.1: SBOX applied to every byte of the state -/
def subBytes (s : Block) : Block := s.map sbox

/-- INVSUBBYTES, FIPS 197 §5.3.2: INVSBOX applied to every byte of the state -/
def invSubBytes (s : Block) : Block := s.map invSbox

/-- SHIFTROWS, FIPS 197 §5.1.2, Eq. (5.5): s′[r, c] = s[r, (c + r) mod 4] -/
def shiftRows (s : Block) : Block :=
  Vector.ofFn fun i =>
    let r := i.val % 4
    let c := i.val / 4
    s[r + 4 * ((c + r) % 4)]'(by omega)

/-- INVSHIFTROWS, FIPS 197 §5.3.1, Eq. (5.12): s′[r, c] = s[r, (c − r) mod 4] -/
def invShiftRows (s : Block) : Block :=
  Vector.ofFn fun i =>
    let r := i.val % 4
    let c := i.val / 4
    s[r + 4 * ((c + 4 - r) % 4)]'(by omega)

/--
Multiplication of each column by the matrix whose first row is `[a₀, a₁, a₂, a₃]` and whose
later rows are its rotations to the right: s′[r, c] = a₀ • s[r, c] ⊕ a₁ • s[r + 1, c] ⊕
a₂ • s[r + 2, c] ⊕ a₃ • s[r + 3, c], row indices modulo 4. This is the matrix of FIPS 197 §4.3,
Eq. (4.9), but the arguments are its first row: the word [a₀, a₁, a₂, a₃] of §4.3 (its first
column) corresponds to `mixColumnsWith a₀ a₃ a₂ a₁`.
-/
def mixColumnsWith (a₀ a₁ a₂ a₃ : UInt8) (s : Block) : Block :=
  Vector.ofFn fun i =>
    let r := i.val % 4
    let c := i.val / 4
    mul a₀ (s[r + 4 * c]'(by omega)) ^^^ mul a₁ (s[(r + 1) % 4 + 4 * c]'(by omega)) ^^^
      mul a₂ (s[(r + 2) % 4 + 4 * c]'(by omega)) ^^^ mul a₃ (s[(r + 3) % 4 + 4 * c]'(by omega))

/--
MIXCOLUMNS, FIPS 197 §5.1.3, Eqs. (5.6)–(5.8): the first row 02, 03, 01, 01 of the matrix of
Eq. (5.7), from the word [{02}, {01}, {01}, {03}] of Eq. (5.6)
-/
def mixColumns (s : Block) : Block := mixColumnsWith 0x02 0x03 0x01 0x01 s

/--
INVMIXCOLUMNS, FIPS 197 §5.3.3, Eqs. (5.13)–(5.15): the first row 0e, 0b, 0d, 09 of the matrix of
Eq. (5.14), from the word [{0e}, {09}, {0d}, {0b}] of Eq. (5.13)
-/
def invMixColumns (s : Block) : Block := mixColumnsWith 0x0e 0x0b 0x0d 0x09 s

/--
ADDROUNDKEY, FIPS 197 §5.1.4, Eq. (5.9): column `c` of the state is XORed with the round-key
word `roundKey[c]`, so s′[r, c] = s[r, c] ⊕ roundKey[c][r]
-/
def addRoundKey (s : Block) (roundKey : Vector (Vector UInt8 4) 4) : Block :=
  Vector.ofFn fun i => s[i] ^^^ roundKey[i.val / 4][i.val % 4]

end Standards.NIST.AES
