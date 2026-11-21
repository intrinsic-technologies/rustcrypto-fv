import P256.Proofs.Projective.Multiply.Lookup.Correct
import P256.Proofs.Projective.Multiply.Radix.Correct
import P256.Proofs.Projective.Multiply.Loop.Value

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.ScalarMul

open P256.Spec.Operations (domain)
open Algebra
open Standards.SECG.ECC Group ProjectiveLookup ProjectiveLoop ProjectiveRadix

theorem double4_correct (laws : CurveAddLaws domain)
    (base : Curve.Point) (hb : Curve.onCurve domain base = true)
    (point : Projective) (hp : point.valid) (n : Nat)
    (heq : point.toAffine = multiple domain base n) :
    (double4 point).valid ∧
      (double4 point).toAffine = multiple domain base (16 * n) := by
  have hv₁ := Projective.double_valid point hp
  have hv₂ := Projective.double_valid point.double hv₁
  have hv₃ := Projective.double_valid point.double.double hv₂
  have hv₄ := Projective.double_valid point.double.double.double hv₃
  have he₁ := double_multiple_toAffine laws base hb point hp n heq
  have he₂ := double_multiple_toAffine laws base hb point.double hv₁ (2 * n) he₁
  have he₃ := double_multiple_toAffine laws base hb point.double.double hv₂ (2 * (2 * n)) he₂
  have he₄ := double_multiple_toAffine laws base hb point.double.double.double hv₃
    (2 * (2 * (2 * n))) he₃
  refine ⟨hv₄, ?_⟩
  simpa only [double4, ← Nat.mul_assoc] using he₄

theorem accumulator_correct (laws : CurveAddLaws domain)
    (point : Projective) (hp : point.valid) (d : Nat) (hd : d < 2 ^ 256)
    (k : Nat) (hk : k ≤ 64) :
    (accumulator (Projective.table point) (digitByte d) k).valid ∧
      (accumulator (Projective.table point) (digitByte d) k).toAffine =
        multiple domain point.toAffine (radixPrefix d (64 - k)) := by
  induction k with
  | zero =>
    apply add_signedLookup_correct laws point Projective.identity hp Projective.identity_valid
      0 (radixPrefix d 64) rfl (digitByte d 64)
    · rw [digitByte_toInt]
      exact digitInt_bounds d 64
    · simpa only [Int.natCast_zero, Int.zero_add, digitByte_toInt] using radixPrefix_initial d hd
  | succ k ih =>
    have hprev := ih (by omega)
    have hdouble := double4_correct laws point.toAffine (Projective.toAffine_onCurve point hp)
      (accumulator (Projective.table point) (digitByte d) k) hprev.1
      (radixPrefix d (64 - k)) hprev.2
    apply add_signedLookup_correct laws point
      (double4 (accumulator (Projective.table point) (digitByte d) k)) hp hdouble.1
      (16 * radixPrefix d (64 - k)) (radixPrefix d (64 - (k + 1))) hdouble.2
      (digitByte d (63 - k))
    · rw [digitByte_toInt]
      exact digitInt_bounds d (63 - k)
    · rw [digitByte_toInt]
      have hstep := radixPrefix_step d (63 - k) (by omega)
      have he₁ : 63 - k + 1 = 64 - k := by omega
      have he₂ : 64 - (k + 1) = 63 - k := by omega
      simpa only [he₁, he₂] using hstep

end P256.Proofs.Projective.Multiply.ScalarMul
