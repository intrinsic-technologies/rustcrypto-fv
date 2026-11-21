import P256.Proofs.Nonce.Initialize.Reduce.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Compare.Borrow

open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Nonce.Initialize.Reduce

theorem borrowWord_form (a b r : BitVec 64) :
    (((~~~a ||| b) &&& r) ||| (b &&& ~~~a)) >>> 63 = borrowWord a b r := by
  rw [borrowWord]
  congr 1
  ac_rfl

def borrowChain (a : Limbs) : BitVec 64 :=
  let q0 := borrowWord a.l0 0xf3b9cac2fc632551 (a.l0 - 0xf3b9cac2fc632551)
  let q1 := borrowWord a.l1 0xbce6faada7179e84 ((-q0).sshiftRight 63 + a.l1 - 0xbce6faada7179e84)
  let q2 := borrowWord a.l2 0xffffffffffffffff ((-q1).sshiftRight 63 + a.l2 - 0xffffffffffffffff)
  borrowWord a.l3 0xffffffff00000000 ((-q2).sshiftRight 63 + a.l3 - 0xffffffff00000000)

theorem borrowChain_eq (a : Limbs) :
    borrowChain a = if a.toNat < P256.Spec.Operations.domain.n then 1 else 0 := by
  have same : borrowChain a = (subtractOrder a).2 := by
    simp only [borrowChain, subtractOrder, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rw [same]
  have h := subtractOrder_toNat a
  have hr := limbs_toNat_lt (subtractOrder a).1
  have ha := limbs_toNat_lt a
  rcases eq_zero_or_one h.1 with hb | hb
  · have h := h.2
    rw [hb] at h ⊢
    change _ + P256.Spec.Operations.domain.n = a.toNat + 2^256 * 0 at h
    rw [ite_eq_right (by omega)]
  · have h := h.2
    rw [hb] at h ⊢
    change _ + P256.Spec.Operations.domain.n = a.toNat + 2^256 * 1 at h
    rw [ite_eq_left (by omega)]

end P256.Proofs.Nonce.Fill.Tail.Compare.Borrow
