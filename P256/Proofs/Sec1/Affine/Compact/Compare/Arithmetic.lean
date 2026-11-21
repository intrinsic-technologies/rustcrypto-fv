import P256.Proofs.Field.Subtract.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Compare

open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Field.Subtract

theorem borrow_eq (a b : Limbs) :
    (subRaw a b).2 = if a.toNat<b.toNat then 1 else 0 := by
  have h := subRaw_toNat a b
  have bound := limbs_toNat_lt (subRaw a b).1
  rcases eq_zero_or_one h.1 with eq | eq
  · rw [eq] at h ⊢
    have order : ¬ a.toNat<b.toNat := by
      have h := h.2
      change (subRaw a b).1.toNat+b.toNat=a.toNat+2^256*0 at h
      omega
    rw [ite_eq_right order]
  · rw [eq] at h ⊢
    have order : a.toNat<b.toNat := by
      have h := h.2
      change (subRaw a b).1.toNat+b.toNat=a.toNat+2^256*1 at h
      omega
    rw [ite_eq_left order]

end P256.Proofs.Sec1.Affine.Compact.Compare
