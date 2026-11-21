import K256.Proofs.Sec1.Serialize.Normalize.Fold
import K256.Proofs.Sec1.Serialize.Normalize.Flag
import K256.Proofs.Sec1.Serialize.Normalize.Select

namespace K256.Proofs.Sec1.Serialize.Normalize

open K256.Proofs.Common.Field

theorem normalize_correct (a : Limbs) (x : Fin modulus) (m : Nat)
    (h : FieldRepr a x m) (hm : m ≤ 2047) :
    Widths (normalize a) ∧ limbValue (normalize a) = x.val := by
  obtain ⟨ht, hv, hx⟩ := firstPass_correct a x m h hm
  unfold normalize
  dsimp only
  rw [flagOf_eq _ _ _ _ _ ht]
  exact (normOf_correct _ _ _ _ _ hv).imp_right (·.trans hx)

end K256.Proofs.Sec1.Serialize.Normalize
