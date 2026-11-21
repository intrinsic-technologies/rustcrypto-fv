import Standards.NIST.AES.Transformations

/-!
# FIPS 197-upd1 §§5 and 5.2: key lengths and KEYEXPANSION

A word is a `Vector UInt8 4`, the four bytes of a word (FIPS 197-upd1 §3.5). A key of the instance
`v` is a `Vector UInt8 v.keyBytes`, the 4·Nk bytes of the key (§3.3), word i being key[4*i..4*i+3]
(§5.2, Algorithm 2).
FIPS 197 in the docstrings is FIPS 197-upd1.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf
-/

namespace Standards.NIST.AES

/-- The three AES instances of FIPS 197 §5, Table 3 -/
inductive Variant where
  | aes128
  | aes192
  | aes256
  deriving DecidableEq, Repr

namespace Variant

/-- Nk, the number of 32-bit words of the key (FIPS 197 §5, Table 3) -/
def Nk : Variant → Nat
  | aes128 => 4
  | aes192 => 6
  | aes256 => 8

/-- Nr, the number of rounds (FIPS 197 §5, Table 3) -/
def Nr : Variant → Nat
  | aes128 => 10
  | aes192 => 12
  | aes256 => 14

/-- The key length in bytes, 4·Nk -/
def keyBytes (v : Variant) : Nat := 4 * v.Nk

end Variant

/-- ROTWORD, FIPS 197 §5.2, Eq. (5.10): [a₀, a₁, a₂, a₃] ↦ [a₁, a₂, a₃, a₀] -/
def rotWord (w : Vector UInt8 4) : Vector UInt8 4 := #v[w[1], w[2], w[3], w[0]]

/-- SUBWORD, FIPS 197 §5.2, Eq. (5.11): SBOX applied to each byte -/
def subWord (w : Vector UInt8 4) : Vector UInt8 4 := w.map sbox

/-- Bytewise XOR of words -/
def xorWord (a b : Vector UInt8 4) : Vector UInt8 4 := Vector.ofFn fun i => a[i] ^^^ b[i]

/-- Rcon[j] = [x^(j−1), 00, 00, 00], FIPS 197 §5.2, Table 5 -/
def rcon (j : Nat) : Vector UInt8 4 := #v[pow 0x02 (j - 1), 0, 0, 0]

/--
KEYEXPANSION, FIPS 197 §5.2, Algorithm 2: the 4·(Nr + 1) words of the key schedule. Words
0 to Nk − 1 are the key, w[i] = key[4i..4i+3] (lines 2–6); each later word is
w[i] = w[i − Nk] ⊕ temp, where temp is w[i − 1] transformed by
SUBWORD(ROTWORD(·)) ⊕ Rcon[i/Nk] when i mod Nk = 0, and by SUBWORD when Nk > 6 and
i mod Nk = 4 (lines 7–16).
-/
def keyExpansion (v : Variant) (key : Vector UInt8 v.keyBytes) :
    Vector (Vector UInt8 4) (4 * (v.Nr + 1)) :=
  let first : Array (Vector UInt8 4) := Array.ofFn fun i : Fin v.Nk =>
    Vector.ofFn fun j : Fin 4 => key[4 * i.val + j.val]'(by
      have := i.isLt; have := j.isLt; unfold Variant.keyBytes; omega)
  let all := (List.range (4 * (v.Nr + 1) - v.Nk)).foldl (fun w k =>
    let i := v.Nk + k
    let previous := w[i - 1]!
    let temp :=
      if i % v.Nk = 0 then xorWord (subWord (rotWord previous)) (rcon (i / v.Nk))
      else if v.Nk > 6 ∧ i % v.Nk = 4 then subWord previous
      else previous
    w.push (xorWord w[i - v.Nk]! temp)) first
  Vector.ofFn fun i => all[i]!

/-- The round key of round `round`: words w[4·round .. 4·round + 3] of the key schedule -/
def roundKey (v : Variant) (w : Vector (Vector UInt8 4) (4 * (v.Nr + 1)))
    (round : Fin (v.Nr + 1)) : Vector (Vector UInt8 4) 4 :=
  Vector.ofFn fun c => w[4 * round.val + c.val]'(by have := round.isLt; omega)

end Standards.NIST.AES
