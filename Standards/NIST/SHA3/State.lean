/-!
# Keccak state representations

Parameters and state representations from FIPS 202, §§3–3.1.3. The parameter `ℓ : Fin 7`, the
binary logarithm of the lane size, selects one of the seven permitted Keccak state sizes.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
-/

namespace Standards.NIST.SHA3

/-- Lane size in bits: `w = 2^ℓ` (FIPS 202, Table 1) -/
def w (ℓ : Fin 7) : Nat := 2 ^ (ℓ : Nat)

/-- State width in bits: `b = 25w`, ranging over 25, 50, 100, 200, 400, 800, and 1600 -/
def b (ℓ : Fin 7) : Nat := 25 * w ℓ

/-- The state array `A[x, y, z]`, with dimensions `5 × 5 × w` (FIPS 202, §3.1) -/
structure StateArray (ℓ : Fin 7) where
  bits : Vector (Vector (Vector Bool (w ℓ)) 5) 5

/-- Coordinate notation `a[x, y, z]` -/
scoped macro:max a:term noWs "[" x:term "," y:term "," z:term "]" : term =>
  `($a[(($x : Nat), ($y : Nat), ($z : Nat))])

namespace StateArray

variable {ℓ : Fin 7}

/-- Read a state bit with checked bounds `x < 5`, `y < 5`, and `z < w` -/
instance : GetElem (StateArray ℓ) (Nat × Nat × Nat) Bool
    (fun _ i => i.1 < 5 ∧ i.2.1 < 5 ∧ i.2.2 < w ℓ) where
  getElem a i h := ((a.bits[i.1]'h.1)[i.2.1]'h.2.1)[i.2.2]'h.2.2

/--
Convert a bit string to a state array using `A[x, y, z] = S[w(5y + x) + z]` (FIPS 202, §3.1.2)
-/
def ofString (s : Vector Bool (b ℓ)) : StateArray ℓ where
  bits := Vector.ofFn fun x => Vector.ofFn fun y => Vector.ofFn fun z =>
    s[(w ℓ) * (5 * (y : Nat) + (x : Nat)) + (z : Nat)]'(by
      have h := Nat.mul_le_mul_left (w ℓ)
        (show 5 * (y : Nat) + (x : Nat) + 1 ≤ 25 by omega)
      rw [Nat.mul_add, Nat.mul_one] at h
      unfold b
      rw [Nat.mul_comm 25]
      omega)

/--
Convert a state array to a bit string by concatenating lanes, then planes (FIPS 202, §3.1.3)
-/
def toString (a : StateArray ℓ) : Vector Bool (b ℓ) :=
  Vector.ofFn fun i =>
    have hw : 0 < w ℓ := Nat.pow_pos (by decide)
    have hi : (i : Nat) / w ℓ < 25 := (Nat.div_lt_iff_lt_mul hw).mpr i.isLt
    have hz : (i : Nat) % w ℓ < w ℓ := Nat.mod_lt _ hw
    a[((i : Nat) / w ℓ) % 5, ((i : Nat) / w ℓ) / 5, (i : Nat) % w ℓ]

end StateArray

end Standards.NIST.SHA3
