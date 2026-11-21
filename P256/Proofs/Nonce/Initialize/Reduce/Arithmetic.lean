import P256.Proofs.Field.Subtract.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Reduce

open P256.Proofs.SecretKeyFromBytes.Scalar

def borrowWord (a b r : BitVec 64) : BitVec 64 :=
  ((~~~a &&& b) ||| ((~~~a ||| b) &&& r)) >>> 63

def subtractOrder (a : Limbs) : Limbs × BitVec 64 :=
  let r0 := a.l0 - 0xf3b9cac2fc632551
  let b0 := borrowWord a.l0 0xf3b9cac2fc632551 r0
  let r1 := (-b0).sshiftRight 63 + (a.l1 - 0xbce6faada7179e84)
  let b1 := borrowWord a.l1 0xbce6faada7179e84 r1
  let r2 := (-b1).sshiftRight 63 + (a.l2 - 0xffffffffffffffff)
  let b2 := borrowWord a.l2 0xffffffffffffffff r2
  let r3 := (-b2).sshiftRight 63 + (a.l3 - 0xffffffff00000000)
  let b3 := borrowWord a.l3 0xffffffff00000000 r3
  (⟨r0, r1, r2, r3⟩, b3)

theorem borrowWord_eq (a b r : BitVec 64) : borrowWord a b r = Field.Subtract.borrow a b r := by
  simp only [borrowWord, Field.Subtract.borrow, BitVec.and_comm, BitVec.or_comm]

theorem subtractOrder_eq (a : Limbs) : subtractOrder a =
    Field.Subtract.subRaw a ⟨0xf3b9cac2fc632551, 0xbce6faada7179e84,
      0xffffffffffffffff, 0xffffffff00000000⟩ := by
  simp only [subtractOrder, borrowWord_eq, Field.Subtract.subRaw, Field.Subtract.subWord]

theorem subtractOrder_toNat (a : Limbs) :
    (subtractOrder a).2.toNat ≤ 1 ∧
      (subtractOrder a).1.toNat + P256.Spec.Operations.domain.n =
        a.toNat + 2^256 * (subtractOrder a).2.toNat := by
  rw [subtractOrder_eq]
  exact Field.Subtract.subRaw_toNat a _

theorem subtractOrder_choice (a : Limbs) :
    (((subtractOrder a).2.setWidth 8 &&& 1).setWidth 64) =
      if decide ((subtractOrder a).2 ≠ 0) then 1 else 0 := by
  rcases eq_zero_or_one (subtractOrder_toNat a).1 with h | h <;> rw [h] <;> decide +kernel

theorem selected_toNat (a : Limbs) :
    (if decide ((subtractOrder a).2 ≠ 0) then a.toNat else (subtractOrder a).1.toNat) =
      a.toNat % P256.Spec.Operations.domain.n := by
  have h := subtractOrder_toNat a
  have ha := limbs_toNat_lt a
  have hr := limbs_toNat_lt (subtractOrder a).1
  have sum := h.2
  rcases eq_zero_or_one h.1 with hb | hb
  · rw [hb] at sum ⊢
    change (subtractOrder a).1.toNat = a.toNat % P256.Spec.Operations.domain.n
    change _ + P256.Spec.Operations.domain.n = a.toNat + 2^256 * 0 at sum
    simp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at sum ⊢
    omega
  · rw [hb] at sum ⊢
    change a.toNat = a.toNat % P256.Spec.Operations.domain.n
    change _ + P256.Spec.Operations.domain.n = a.toNat + 2^256 * 1 at sum
    simp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at sum ⊢
    omega

end P256.Proofs.Nonce.Initialize.Reduce
