import P256.Proofs.Field.Montgomery.Reduction.CorrectionArithmetic
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Field.Add

open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Field.Montgomery.Reduction

def addRaw (a b : Limbs) : Limbs × Bool :=
  let c0 := carry a.l0 b.l0 false
  let c1 := carry a.l1 b.l1 c0
  let c2 := carry a.l2 b.l2 c1
  (⟨adc a.l0 b.l0 false, adc a.l1 b.l1 c0,
    adc a.l2 b.l2 c1, adc a.l3 b.l3 c2⟩, carry a.l3 b.l3 c2)

def add (a b : Limbs) : Limbs :=
  reduceSum (addRaw a b).1 (addRaw a b).2

theorem addRaw_toNat (a b : Limbs) :
    (addRaw a b).1.toNat + 2^256 * (addRaw a b).2.toNat = a.toNat + b.toNat := by
  have h0 := adc_carry a.l0 b.l0 false
  have h1 := adc_carry a.l1 b.l1 (carry a.l0 b.l0 false)
  have h2 := adc_carry a.l2 b.l2 (carry a.l1 b.l1 (carry a.l0 b.l0 false))
  have h3 := adc_carry a.l3 b.l3
    (carry a.l2 b.l2 (carry a.l1 b.l1 (carry a.l0 b.l0 false)))
  simp only [Bool.toNat_false, Nat.add_zero] at h0
  simp only [addRaw, Limbs.toNat]
  omega

theorem addRaw_comm (a b : Limbs) : addRaw a b = addRaw b a := by
  have carry_comm (a b : BitVec 64) (c : Bool) : carry a b c = carry b a c := by
    simp only [carry, Nat.add_comm a.toNat b.toNat]
  have adc_comm (a b : BitVec 64) (c : Bool) : adc a b c = adc b a c := by
    simp only [adc, BitVec.add_comm a b]
  simp only [addRaw, carry_comm a.l0 b.l0, carry_comm a.l1 b.l1,
    carry_comm a.l2 b.l2, carry_comm a.l3 b.l3, adc_comm a.l0 b.l0,
    adc_comm a.l1 b.l1, adc_comm a.l2 b.l2, adc_comm a.l3 b.l3]

theorem add_toNat (a b : Limbs)
    (ha : a.toNat < P256.Spec.Operations.domain.p)
    (hb : b.toNat < P256.Spec.Operations.domain.p) :
    (add a b).toNat = (a.toNat + b.toNat) % P256.Spec.Operations.domain.p := by
  have hsum := addRaw_toNat a b
  unfold add
  rw [reduceSum_toNat _ _ (by rw [hsum]; omega), hsum]

theorem add_montgomery (a b : Limbs) (x y : Nat)
    (ha : a.toNat = x * 2^256 % P256.Spec.Operations.domain.p)
    (hb : b.toNat = y * 2^256 % P256.Spec.Operations.domain.p) :
    (add a b).toNat = ((x + y) % P256.Spec.Operations.domain.p) * 2^256 %
      P256.Spec.Operations.domain.p := by
  rw [add_toNat a b (ha ▸ Nat.mod_lt _ Montgomery.p_pos)
    (hb ▸ Nat.mod_lt _ Montgomery.p_pos), ha, hb, ← Nat.add_mod,
    ← Nat.add_mul, Nat.mod_mul_mod]

end P256.Proofs.Field.Add
