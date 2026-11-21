import K256.Proofs.Generate.Generator.Multiply.Split.WideProduct

namespace K256.Proofs.Generate.Generator.Multiply.Split.Rounding

open Standards.SECG.DomainParameters.Secp256k1

def upper (w : Vector (BitVec 64) 8) : Nat :=
  w[6].toNat + 2^64 * w[7].toNat

theorem upper_bound (w : Vector (BitVec 64) 8) : upper w < 2^128 := by
  have := w[6].isLt
  have := w[7].isLt
  simp only [upper, Nat.reducePow]
  omega

theorem upper_words (w : Vector (BitVec 64) 8) :
    #v[w[6], w[7], 0, 0] = scalarWords (upper w) := by
  have lo := w[6].isLt
  have hi := w[7].isLt
  apply Vector.ext
  intro i h
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl|rfl|rfl|rfl <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [upper, scalarWords, Vector.getElem_ofFn, BitVec.toNat_ofNat, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, Nat.reduceMul,
      Nat.reducePow, Nat.div_one, BitVec.reduceToNat] <;> omega

theorem shift_bit (w : Vector (BitVec 64) 8) : w[5] >>> 63 = 0 ∨ w[5] >>> 63 = 1 := by
  have := w[5].isLt
  have e : (w[5] >>> 63).toNat = w[5].toNat / 2^63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have : (w[5] >>> 63).toNat = 0 ∨ (w[5] >>> 63).toNat = 1 := by omega
  exact this.imp BitVec.eq_of_toNat_eq BitVec.eq_of_toNat_eq

theorem rounded_choice (w : Vector (BitVec 64) 8) :
    (if w[5] >>> 63 = 0 then upper w else (upper w + 1) % domain.n) = roundedHigh w := by
  have ub := upper_bound w
  have n : 2^128 < domain.n := by decide +kernel
  have eqn : (upper w + 1) % domain.n = upper w + 1 := Nat.mod_eq_of_lt (by omega)
  change _ = upper w + (w[5] >>> 63).toNat
  rcases shift_bit w with h|h <;> simp [h, eqn]

end K256.Proofs.Generate.Generator.Multiply.Split.Rounding
