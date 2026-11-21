import P256.Proofs.Scalar.Multiply.Arithmetic.Support
import P256.Proofs.SecretKeyFromBytes.Compare

set_option autoImplicit false

open P256.Proofs.Scalar.Multiply.Arithmetic.Support (Limbs)
open P256.Proofs.SecretKeyFromBytes.Scalar (orderBorrow orderBorrow_eq)

namespace P256.Proofs.Scalar.Multiply.Arithmetic.Reduction



def subtractOrder (a : Limbs) : Limbs :=
  let r0 := 0x0c46353d039cdaaf + a.l0
  let b0 := (~~~a.l0 ||| r0) >>> 63
  let r1 := 0x4319055258e8617c + a.l1 + (-b0).sshiftRight 63
  let b1 := (~~~a.l1 ||| r1) >>> 63
  let r2 := ((b1 - 1) >>> 63) + a.l2
  let b2 := (~~~a.l2 ||| r2) >>> 63
  let r3 := 0x100000000 + a.l3 + (-b2).sshiftRight 63
  ⟨r0, r1, r2, r3⟩

theorem subtractOrder_toNat (a : Limbs) :
    (subtractOrder a).toNat + P256.Spec.Operations.domain.n =
      a.toNat + 2^256 * (orderBorrow a).toNat := by
  let r0 := 0x0c46353d039cdaaf + a.l0
  let b0 := (~~~a.l0 ||| r0) >>> 63
  let r1 := 0x4319055258e8617c + a.l1 + (-b0).sshiftRight 63
  let b1 := (~~~a.l1 ||| r1) >>> 63
  let r2 := ((b1 - 1) >>> 63) + a.l2
  let b2 := (~~~a.l2 ||| r2) >>> 63
  let r3 := 0x100000000 + a.l3 + (-b2).sshiftRight 63
  have h0nat : r0.toNat = (2^64 + a.l0.toNat - 0xf3b9cac2fc632551 - 0) % 2^64 := by
    rw [BitVec.toNat_add]
    change (0x0c46353d039cdaaf + a.l0.toNat) % 2^64 = _
    exact congrArg (fun x : Nat => x % 2^64) (by omega)
  have h0 := P256.Proofs.SecretKeyFromBytes.Scalar.subtractWord_borrow_or a.l0 r0 0xf3b9cac2fc632551 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) h0nat
  change b0.toNat ≤ 1 ∧ _ at h0
  have h1nat := P256.Proofs.SecretKeyFromBytes.Scalar.subtractWord_toNat a.l1 b0 0xbce6faada7179e84
    (by decide +kernel) (P256.Proofs.SecretKeyFromBytes.Scalar.eq_zero_or_one h0.1)
  have hr1 : r1 = a.l1 + (-b0).sshiftRight 63 +
      BitVec.ofNat 64 (2^64 - 0xbce6faada7179e84) := by
    change 0x4319055258e8617c + a.l1 + (-b0).sshiftRight 63 =
      a.l1 + (-b0).sshiftRight 63 + 0x4319055258e8617c
    ac_rfl
  rw [← hr1] at h1nat
  have h1 := P256.Proofs.SecretKeyFromBytes.Scalar.subtractWord_borrow_or a.l1 r1 0xbce6faada7179e84 b0.toNat
    (by decide +kernel) (by decide +kernel) h0.1 h1nat
  change b1.toNat ≤ 1 ∧ _ at h1
  have hr2 : r2 = a.l2 + (-b1).sshiftRight 63 +
      BitVec.ofNat 64 (2^64 - 0xffffffffffffffff) := by
    rcases P256.Proofs.SecretKeyFromBytes.Scalar.eq_zero_or_one h1.1 with hb1 | hb1
    · change ((b1 - 1) >>> 63) + a.l2 = a.l2 + (-b1).sshiftRight 63 + 1
      rw [hb1]
      change 1#64 + a.l2 = a.l2 + 0#64 + 1#64
      rw [BitVec.add_zero, BitVec.add_comm]
    · change ((b1 - 1) >>> 63) + a.l2 = a.l2 + (-b1).sshiftRight 63 + 1
      rw [hb1]
      change 0#64 + a.l2 = a.l2 + (-1#64) + 1#64
      rw [BitVec.zero_add, BitVec.add_assoc,
        show (-1#64) + 1#64 = 0#64 by decide +kernel, BitVec.add_zero]
  have h2nat := P256.Proofs.SecretKeyFromBytes.Scalar.subtractWord_toNat a.l2 b1 0xffffffffffffffff
    (by decide +kernel) (P256.Proofs.SecretKeyFromBytes.Scalar.eq_zero_or_one h1.1)
  rw [← hr2] at h2nat
  have h2 := P256.Proofs.SecretKeyFromBytes.Scalar.subtractWord_borrow_or a.l2 r2 0xffffffffffffffff b1.toNat
    (by decide +kernel) (by decide +kernel) h1.1 h2nat
  change b2.toNat ≤ 1 ∧ _ at h2
  have h3nat := P256.Proofs.SecretKeyFromBytes.Scalar.subtractWord_toNat a.l3 b2 0xffffffff00000000
    (by decide +kernel) (P256.Proofs.SecretKeyFromBytes.Scalar.eq_zero_or_one h2.1)
  have hr3 : r3 = a.l3 + (-b2).sshiftRight 63 +
      BitVec.ofNat 64 (2^64 - 0xffffffff00000000) := by
    change 0x100000000 + a.l3 + (-b2).sshiftRight 63 =
      a.l3 + (-b2).sshiftRight 63 + 0x100000000
    ac_rfl
  rw [← hr3] at h3nat
  have h3 := P256.Proofs.SecretKeyFromBytes.Scalar.subtractWord_borrow_or a.l3 r3 0xffffffff00000000 b2.toNat
    (by decide +kernel) (by decide +kernel) h2.1 h3nat
  change (orderBorrow a).toNat ≤ 1 ∧ _ at h3
  have hsum : (P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.mk r0 r1 r2 r3).toNat +
      P256.Spec.Operations.domain.n = a.toNat + 2^256 * (orderBorrow a).toNat := by
    simp only [P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.toNat, P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain]
    change r0.toNat + 2^64 * (r1.toNat + 2^64 * (r2.toNat + 2^64 * r3.toNat)) + _ =
      a.l0.toNat + 2^64 * (a.l1.toNat + 2^64 * (a.l2.toNat + 2^64 * a.l3.toNat)) +
        2^256 * ((~~~a.l3 ||| r3) >>> 63).toNat
    dsimp only [b0, b1, b2] at h0 h1 h2 h3
    omega
  exact hsum

end P256.Proofs.Scalar.Multiply.Arithmetic.Reduction
