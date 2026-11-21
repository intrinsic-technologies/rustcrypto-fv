import K256.Proofs.Common.Point.AddWords.Model
import K256.Proofs.Generate.Curve.Group.Field
import K256.Proofs.Sec1.Serialize.Normalize.Fold

namespace K256.Proofs.Common.Point.AddWords

open Field Generate.Curve.Group.CurveArithmetic Lean.Grind Fin.NatCast Fin.IntCast
open Sec1.Serialize.Normalize

private def limbBound (i : Fin 5) : Nat :=
  if i.val < 4 then 2^52 - 1 else 2^48 - 1

private theorem repr_bound {a : Limbs} {x : Fp} {m : Nat} (h : FieldRepr a x m)
    (i : Fin 5) : a[i].toNat ≤ (2*m) * limbBound i := by
  have hi := h.1 i
  by_cases hlt : i.val < 4 <;>
    simpa only [limbBound, hlt, ite_true, ite_false, getElem!_pos, i.isLt] using hi

private theorem repr_iff {a : Limbs} {x : Fp} {m : Nat} :
    FieldRepr a x m ↔
      (∀ i : Fin 5, a[i].toNat ≤ (2*m) * limbBound i) ∧ ((limbValue a : Nat) : Fp) = x := by
  constructor
  · intro h
    exact ⟨repr_bound h, Fin.ext h.2⟩
  · rintro ⟨b, h⟩
    refine ⟨fun i => ?_, congrArg Fin.val h⟩
    by_cases hlt : i.val < 4 <;>
      simpa only [limbBound, hlt, ite_true, ite_false, getElem!_pos, i.isLt] using b i

private theorem limbValue_eq (a : Limbs) :
    limbValue a = a[(0 : Fin 5)].toNat + a[(1 : Fin 5)].toNat * 2^52 +
      a[(2 : Fin 5)].toNat * 2^104 + a[(3 : Fin 5)].toNat * 2^156 +
      a[(4 : Fin 5)].toNat * 2^208 := by
  rw [SquareValue.limbValue_eq]
  rfl

private theorem limbBound_le (i : Fin 5) : limbBound i ≤ 2^52 - 1 := by
  unfold limbBound
  split <;> decide +kernel

private theorem mul_limb_lt {k : Nat} (h : k ≤ 4094) (i : Fin 5) :
    k * limbBound i < 2^64 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul h (limbBound_le i)) (by decide +kernel)

theorem sum_repr {a b : Limbs} {x y : Fp} {m n : Nat}
    (ha : FieldRepr a x m) (hb : FieldRepr b y n) (hm : m + n ≤ 2047) :
    FieldRepr (sum a b) (x + y) (m + n) := by
  have hbound (i : Fin 5) : a[i].toNat + b[i].toNat ≤ (2 * (m + n)) * limbBound i := by
    have h := Nat.add_le_add (repr_bound ha i) (repr_bound hb i)
    rwa [← Nat.add_mul, ← Nat.mul_add] at h
  have hlimb (i : Fin 5) : (sum a b)[i].toNat = a[i].toNat + b[i].toNat := by
    simp only [sum, Fin.getElem_fin, Vector.getElem_ofFn, BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (hbound i) (mul_limb_lt (by omega) i))
  apply repr_iff.mpr
  refine ⟨fun i => hlimb i ▸ hbound i, ?_⟩
  have hv : limbValue (sum a b) = limbValue a + limbValue b := by
    simp only [limbValue_eq, hlimb, Nat.add_mul]
    omega
  rw [hv, Semiring.natCast_add, (repr_iff.mp ha).2, (repr_iff.mp hb).2]

theorem scale_repr {a : Limbs} {x : Fp} {m : Nat} (n : Nat)
    (ha : FieldRepr a x m) (hm : m * n ≤ 2047) :
    FieldRepr (scale n a) ((n : Fp) * x) (m * n) := by
  have hbound (i : Fin 5) : a[i].toNat * n ≤ (2 * (m * n)) * limbBound i := by
    calc
      _ ≤ (2*m * limbBound i) * n := Nat.mul_le_mul_right n (repr_bound ha i)
      _ = _ := by ac_rfl
  have hlimb (i : Fin 5) : (scale n a)[i].toNat = a[i].toNat * n := by
    simp only [scale, Fin.getElem_fin, Vector.getElem_ofFn, BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mul_mod_mod]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (hbound i) (mul_limb_lt (by omega) i))
  apply repr_iff.mpr
  refine ⟨by intro i; rw [hlimb]; exact hbound i, ?_⟩
  have hv : limbValue (scale n a) = limbValue a * n := by
    simp only [limbValue_eq, hlimb, Nat.add_mul]
    ac_rfl
  rw [hv, Semiring.natCast_mul, (repr_iff.mp ha).2, CommSemiring.mul_comm]

theorem negate_repr {a : Limbs} {x : Fp} {m : Nat}
    (ha : FieldRepr a x m) (hm : m ≤ 2046) :
    FieldRepr (negate m a) (-x) (m + 1) := by
  have hupper (i : Fin 5) : modulusWords[i].toNat ≤ limbBound i := by
    obtain ⟨i, hi⟩ := i
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with
      rfl | rfl | rfl | rfl | rfl
    · exact (by decide +kernel : (0xffffefffffc2f : Nat) ≤ 2^52 - 1)
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · exact Nat.le_refl _
  have hlower (i : Fin 5) : 2*m*limbBound i ≤ modulusWords[i].toNat * (2*(m+1)) := by
    obtain ⟨i, hi⟩ := i
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with
      rfl | rfl | rfl | rfl | rfl
    · change 2*m*(2^52-1) ≤ 0xffffefffffc2f * (2*(m+1))
      omega
    · change 2*m*(2^52-1) ≤ (2^52-1) * (2*(m+1))
      omega
    · change 2*m*(2^52-1) ≤ (2^52-1) * (2*(m+1))
      omega
    · change 2*m*(2^52-1) ≤ (2^52-1) * (2*(m+1))
      omega
    · change 2*m*(2^48-1) ≤ (2^48-1) * (2*(m+1))
      omega
  have hProd (i : Fin 5) :
      ((modulusWords[i]) * BitVec.ofNat 64 (2*(m+1))).toNat =
        modulusWords[i].toNat * (2*(m+1)) := by
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mul_mod_mod, Nat.mod_eq_of_lt]
    rw [Nat.mul_comm]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (hupper i)) (mul_limb_lt (by omega) i)
  have hlimb (i : Fin 5) : (negate m a)[i].toNat =
      modulusWords[i].toNat * (2*(m+1)) - a[i].toNat := by
    simp only [negate, Fin.getElem_fin, Vector.getElem_ofFn]
    change (modulusWords[i] * BitVec.ofNat 64 (2*(m+1)) - a[i]).toNat = _
    have hle : a[i] ≤ modulusWords[i] * BitVec.ofNat 64 (2*(m+1)) := by
      rw [BitVec.le_def, hProd i]
      exact Nat.le_trans (repr_bound ha i) (hlower i)
    rw [BitVec.toNat_sub_of_le hle, hProd i]
    rfl
  apply repr_iff.mpr
  refine ⟨?_, ?_⟩
  · intro i
    rw [hlimb, Nat.mul_comm (modulusWords[i].toNat)]
    exact Nat.le_trans (Nat.sub_le ..) (Nat.mul_le_mul_left _ (hupper i))
  · have hlimb_sum (i : Fin 5) : (negate m a)[i].toNat + a[i].toNat =
        modulusWords[i].toNat * (2*(m+1)) := by
      rw [hlimb, Nat.sub_add_cancel (Nat.le_trans (repr_bound ha i) (hlower i))]
    have hmodulus : limbValue modulusWords = modulus := by decide +kernel
    have hv : limbValue (negate m a) + limbValue a = limbValue modulusWords * (2*(m+1)) := by
      simp only [limbValue_eq]
      calc
        _ = ((negate m a)[(0 : Fin 5)].toNat + a[(0 : Fin 5)].toNat) +
            ((negate m a)[(1 : Fin 5)].toNat + a[(1 : Fin 5)].toNat) * 2^52 +
            ((negate m a)[(2 : Fin 5)].toNat + a[(2 : Fin 5)].toNat) * 2^104 +
            ((negate m a)[(3 : Fin 5)].toNat + a[(3 : Fin 5)].toNat) * 2^156 +
            ((negate m a)[(4 : Fin 5)].toNat + a[(4 : Fin 5)].toNat) * 2^208 := by
              simp only [Nat.add_mul]
              ac_rfl
        _ = _ := by
          simp only [hlimb_sum, Nat.add_mul]
          ac_rfl
    have h := congrArg (fun n : Nat => (n : Fp)) (hmodulus ▸ hv)
    rw [Semiring.natCast_add, Semiring.natCast_mul, (repr_iff.mp ha).2] at h
    have hmod : (modulus : Fp) = 0 := Fin.ext (Nat.mod_self _)
    rw [hmod, Semiring.zero_mul] at h
    have h' := congrArg (fun v : Fp => v + -x) h
    simpa only [Semiring.add_assoc, AddCommGroup.add_neg_cancel, Semiring.add_zero,
      AddCommMonoid.zero_add] using h'

private theorem weakTop_bound (t a : Word) : (top t a).toNat ≤ 2 * 1 * (2^48 - 1) := by
  have hcarry : (t >>> 52).toNat < 2^12 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    exact t.isLt
  have hmask : (a &&& mask48).toNat < 2^48 := by
    simp only [BitVec.toNat_and, show mask48.toNat = 2^48 - 1 by decide +kernel,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  change ((t >>> 52) + (a &&& mask48)).toNat ≤ _
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (show (t >>> 52).toNat + (a &&& mask48).toNat < 2^64 by omega)]
  omega

private theorem weakLow_bound (t : Word) : (t &&& mask52).toNat ≤ 2 * 1 * (2^52 - 1) := by
  simp only [BitVec.toNat_and, show mask52.toNat = 2^52 - 1 by decide +kernel,
    Nat.and_two_pow_sub_one_eq_mod]
  have h : t.toNat % 2^52 < 2^52 := Nat.mod_lt _ (by decide)
  omega

theorem weak_repr {a : Limbs} {x : Fin modulus} {m : Nat}
    (ha : FieldRepr a x m) (hm : m ≤ 2047) : FieldRepr (weak a) x 1 := by
  let t0 := first a
  let t1 := carry t0 a[1]
  let t2 := carry t1 a[2]
  let t3 := carry t2 a[3]
  let t4 := top t3 a[4]
  have hval : limbValue (weak a) = foldedValue t0 t1 t2 t3 t4 := by
    rw [limbValue_eq]
    change (t0 &&& mask52).toNat + (t1 &&& mask52).toNat * 2^52 +
      (t2 &&& mask52).toNat * 2^104 + (t3 &&& mask52).toNat * 2^156 +
      t4.toNat * 2^208 = _
    simp only [BitVec.toNat_and, show mask52.toNat = 2^52 - 1 by decide +kernel,
      Nat.and_two_pow_sub_one_eq_mod, foldedValue]
    simp only [Nat.add_mul, Nat.mul_assoc]
    have h2 : 2^52 * 2^52 = 2^104 := by decide +kernel
    have h3 : 2^52 * (2^52 * 2^52) = 2^156 := by decide +kernel
    have h4 : 2^52 * (2^52 * (2^52 * 2^52)) = 2^208 := by decide +kernel
    simp only [h4, h3, h2]
    ac_rfl
  refine ⟨?_, by rw [hval]; exact (firstPass_correct a x m ha hm).2.2⟩
  intro i
  simp only [getElem!_pos, i.isLt]
  obtain ⟨i, hi⟩ := i
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with
    rfl | rfl | rfl | rfl | rfl
  · exact weakLow_bound t0
  · exact weakLow_bound t1
  · exact weakLow_bound t2
  · exact weakLow_bound t3
  · exact weakTop_bound t3 a[4]

end K256.Proofs.Common.Point.AddWords
