import K256.Spec.Secp256k1

namespace K256.Proofs.Ecdh.Curve

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

private theorem decodePoint_onCurve (input : ByteArray) (p : Curve.Point)
    (h : Points.decodePoint domain K256.Spec.Secp256k1.sqrtMod input = some p) :
    Curve.onCurve domain p = true := by
  simp only [Points.decodePoint, Option.pure_def, Option.bind_eq_bind] at h
  split at h
  · cases h
    rfl
  · split at h
    · split at h
      · cases h
        assumption
      · cases h
    · split at h
      · split at h
        · cases h
        · obtain ⟨root, _, h⟩ := Option.bind_eq_some_iff.mp h
          split at h <;> split at h <;> rename_i ok <;> cases h <;>
            simp only [Bool.and_eq_true, beq_iff_eq] at ok <;>
            simp only [Curve.onCurve, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] <;>
            exact ⟨⟨by omega, Nat.mod_lt _ (by decide +kernel)⟩, ok.1⟩
      · cases h

theorem groupPoint_onCurve (input : ByteArray) (p : Curve.Point)
    (h : K256.Spec.Secp256k1.groupPoint input = some p) : Curve.onCurve domain p = true := by
  unfold K256.Spec.Secp256k1.groupPoint at h
  split at h
  · cases h
    rfl
  · split at h
    · simp only [K256.Spec.Secp256k1.decodePublicKey, Points.decodePublicKey,
        Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨q, hd, h⟩ := h
      have hq := decodePoint_onCurve _ q hd
      cases q with
      | infinity => cases h
      | affine x y =>
        change (if _ then some _ else none) = some p at h
        split at h
        · cases h
          exact hq
        · cases h
    · cases h

end K256.Proofs.Ecdh.Curve
