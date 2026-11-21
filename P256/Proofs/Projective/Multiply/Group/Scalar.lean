import P256.Spec.Points
import P256.Proofs.Projective.Multiply.Group.Base
import Init.Data.Range.Lemmas
import Init.Data.Nat.Bitwise.Lemmas

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Group

open Standards.SECG.ECC

theorem multiple_onCurve (domain : Curve.Domain) (laws : CurveAddLaws domain)
    (point : Curve.Point) (hp : Curve.onCurve domain point = true) (n : Nat) :
    Curve.onCurve domain (multiple domain point n) = true := by
  induction n with
  | zero => rfl
  | succ n ih => exact laws.closed _ _ ih hp

theorem multiple_add (domain : Curve.Domain) (laws : CurveAddLaws domain)
    (point : Curve.Point) (hp : Curve.onCurve domain point = true) (m n : Nat) :
    multiple domain point (m + n) =
      Curve.add domain (multiple domain point m) (multiple domain point n) := by
  induction n with
  | zero =>
    simp only [Nat.add_zero, multiple]
    cases multiple domain point m <;> rfl
  | succ n ih =>
    change Curve.add domain (multiple domain point (m + n)) point =
      Curve.add domain (multiple domain point m) (Curve.add domain (multiple domain point n) point)
    rw [ih]
    exact laws.assoc _ _ _ (multiple_onCurve domain laws point hp m)
      (multiple_onCurve domain laws point hp n) hp

theorem scalarMul_eq_multiple (domain : Curve.Domain) (laws : CurveAddLaws domain)
    (point : Curve.Point) (hp : Curve.onCurve domain point = true) (n : Nat) :
    Curve.scalarMul domain n point = multiple domain point n := by
  let step := fun (result : Curve.Point) (i : Nat) =>
    if n.testBit (n.log2 - i) then
      Curve.add domain (Curve.add domain result result) point
    else Curve.add domain result result
  have hprefix (k : Nat) (hk : k ≤ n.log2 + 1) :
      (List.range k).foldl step .infinity =
        multiple domain point (n / 2 ^ (n.log2 + 1 - k)) := by
    induction k with
    | zero =>
      simp only [List.range_zero, List.foldl_nil, Nat.sub_zero,
        Nat.div_eq_of_lt Nat.lt_log2_self, multiple]
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (by omega)]
      have he : n.log2 + 1 - k = (n.log2 - k) + 1 := by omega
      have he' : n.log2 + 1 - (k + 1) = n.log2 - k := by omega
      have hd : n / 2 ^ (n.log2 - k) =
          n / 2 ^ (n.log2 + 1 - k) + n / 2 ^ (n.log2 + 1 - k) +
            (n.testBit (n.log2 - k)).toNat := by
        rw [he, Nat.toNat_testBit, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
        have h := Nat.div_add_mod (n / 2 ^ (n.log2 - k)) 2
        omega
      rw [he', hd]
      dsimp only [step]
      cases hbit : n.testBit (n.log2 - k)
      · simp only [Bool.false_eq_true, ite_false, Bool.toNat_false, Nat.add_zero]
        exact (multiple_add domain laws point hp _ _).symm
      · simp only [ite_true, Bool.toNat_true, multiple]
        rw [multiple_add domain laws point hp]
  unfold Curve.scalarMul
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Id.run,
    ← apply_ite, List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  change (List.range (n.log2 + 1)).foldl step .infinity = _
  rw [hprefix _ (Nat.le_refl _), Nat.sub_self, Nat.pow_zero, Nat.div_one]

end P256.Proofs.Projective.Multiply.Group
