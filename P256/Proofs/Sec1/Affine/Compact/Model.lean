import P256.Proofs.Sec1.Affine.Model

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact

open P256.Spec Standards.SECG.ECC

theorem decodePoint_eq_decompact {bytes : ByteArray}
    (size : bytes.size = 33) (tag : bytes.data[0]? = some 5) :
    P256.Spec.Points.decodePoint bytes = Points.decompact (Points.element bytes 1) := by
  unfold P256.Spec.Points.decodePoint
  split
  · rfl
  · rename_i rejected
    exact (rejected ⟨size, tag⟩).elim

theorem compactY_eq_min (y : Nat) :
    Points.compactY y = min y (Points.negElement y) := by
  unfold Points.compactY
  split
  · exact (Nat.min_eq_right (by omega)).symm
  · exact (Nat.min_eq_left (by omega)).symm

theorem decompact_none {x : Nat} (decoded : Points.decompress x false = none) :
    Points.decompact x = none := by
  simp [Points.decompact, decoded]

theorem decompact_some {x a y : Nat}
    (decoded : Points.decompress x false = some (.affine a y)) :
    Points.decompact x = some (.affine a
      (if Points.negElement y < y then Points.negElement y else y)) := by
  simp [Points.decompact, decoded, Points.compactY]

theorem decompress_coordinates {x a y : Nat}
    (decoded : Points.decompress x false = some (.affine a y)) :
    a < Operations.domain.p ∧ y < Operations.domain.p := by
  have on := decompress_some_onCurve decoded
  simp only [Curve.onCurve, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at on
  exact on.1

end P256.Proofs.Sec1.Affine.Compact
