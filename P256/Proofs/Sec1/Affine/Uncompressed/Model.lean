import P256.Proofs.Sec1.Affine.Uncompressed.Interface

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed

open P256.Spec Standards.SECG.ECC

theorem canonical_lt (x : Nat) : canonical x < Operations.domain.p := by
  unfold canonical
  split
  · assumption
  · decide +kernel

theorem canonical_eq {x : Nat} (h : x < Operations.domain.p) : canonical x = x := by
  simp only [canonical, h, ite_true]

theorem valid_bounds {bytes : ByteArray} (h : valid bytes = true) :
    xCoordinate bytes < Operations.domain.p ∧ yCoordinate bytes < Operations.domain.p := by
  simp only [valid, Curve.onCurve, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem valid_eq (bytes : ByteArray) :
    valid bytes = (decide (xCoordinate bytes < Operations.domain.p) &&
      decide (yCoordinate bytes < Operations.domain.p) &&
      (canonical (yCoordinate bytes) * canonical (yCoordinate bytes) % Operations.domain.p ==
        (canonical (xCoordinate bytes) * canonical (xCoordinate bytes) *
          canonical (xCoordinate bytes) + Operations.domain.a * canonical (xCoordinate bytes) +
          Operations.domain.b) % Operations.domain.p)) := by
  by_cases hx : xCoordinate bytes < Operations.domain.p
  · by_cases hy : yCoordinate bytes < Operations.domain.p
    · simp [valid, Curve.onCurve, canonical, hx, hy]
    · simp [valid, Curve.onCurve, hy]
  · simp [valid, Curve.onCurve, hx]

theorem decodePoint_eq {bytes : ByteArray} (size : bytes.size = 65)
    (tag : bytes.data[0]? = some 4) :
    P256.Spec.Points.decodePoint bytes =
      if valid bytes then some (.affine (xCoordinate bytes) (yCoordinate bytes)) else none := by
  have nonidentity : (bytes == (⟨#[0]⟩ : ByteArray)) = false := by
    change (bytes.data == #[0]) = false
    apply Bool.eq_false_iff.mpr
    intro h
    have he : bytes = ⟨#[0]⟩ := ByteArray.ext (eq_of_beq h)
    rw [he] at size
    contradiction
  simp only [P256.Spec.Points.decodePoint, size, Nat.reduceEqDiff, false_and, ite_false,
    Standards.SECG.ECC.Points.decodePoint, nonidentity, Bool.false_eq_true,
    Sec1.field_octets, Nat.reduceMul, Nat.reduceAdd, beq_self_eq_true, tag,
    Option.getD_some, Bool.and_self, ite_true]
  rfl

end P256.Proofs.Sec1.Affine.Uncompressed
