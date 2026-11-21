import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearCombination.WideValue
import P256.Proofs.Common.Instructions.Carry.Arithmetic
import P256.Proofs.Field.Subtract.Arithmetic

set_option autoImplicit false
open P256.Proofs.Field.Schoolbook (packFive)
open P256.Proofs.Field.Montgomery (wordBase)
open P256.Proofs.Field.Subtract (borrow subRaw subRaw_toNat subWord subWord_borrow)
open P256.Proofs.Common.Instructions.Carry (sbbSpec sbbSpec_toNat_add_borrow subSpec_toNat_add_borrow)

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
open X86Proofs

def negateWide (a : Vector (BitVec 64) 5) : Vector (BitVec 64) 5 :=
  let v0 := subSpec 0 a[0]
  let v1 := sbbSpec 0 a[1] (BitVec.ofBool v0.2.CF)
  let v2 := sbbSpec 0 a[2] (BitVec.ofBool v1.2.CF)
  let v3 := sbbSpec 0 a[3] (BitVec.ofBool v2.2.CF)
  let carry : BitVec 8 := if !v3.2.CF then 1 else 0
  #v[-a[0],v1.1,v2.1,v3.1,~~~a[4] + carry.setWidth 64]

def subtractWide (a b : Vector (BitVec 64) 5) : Vector (BitVec 64) 5 × BitVec 64 :=
  let r := subRaw ⟨a[0],a[1],a[2],a[3]⟩ ⟨b[0],b[1],b[2],b[3]⟩
  let r4 := subWord a[4] b[4] r.2
  (#v[r.1.l0,r.1.l1,r.1.l2,r.1.l3,r4],borrow a[4] b[4] r4)

theorem wideValue_eq (a : Vector (BitVec 64) 5) :
    wideValue a = a[0].toNat + 2^64*a[1].toNat + 2^128*a[2].toNat +
      2^192*a[3].toNat + 2^256*a[4].toNat := by
  simp [wideValue,packFive,wordBase]

theorem wideValue_lt (a : Vector (BitVec 64) 5) : wideValue a < 2^320 := by
  rw [wideValue_eq]
  have h0 := a[0].isLt
  have h1 := a[1].isLt
  have h2 := a[2].isLt
  have h3 := a[3].isLt
  have h4 := a[4].isLt
  omega

theorem subtractWide_value (a b : Vector (BitVec 64) 5) :
    (subtractWide a b).2.toNat ≤ 1 ∧
    wideValue (subtractWide a b).1 + wideValue b =
      wideValue a + 2^320 * (subtractWide a b).2.toNat := by
  have h := subRaw_toNat ⟨a[0],a[1],a[2],a[3]⟩ ⟨b[0],b[1],b[2],b[3]⟩
  have h4 := subWord_borrow a[4] b[4] _ (P256.Proofs.SecretKeyFromBytes.Scalar.eq_zero_or_one h.1)
  refine ⟨h4.1, ?_⟩
  simp only [subtractWide,wideValue_eq,Vector.getElem_mk,List.getElem_toArray,
    List.getElem_cons_succ,List.getElem_cons_zero]
  simp only [P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.toNat] at h
  omega

set_option maxHeartbeats 800000 in
theorem negateWide_value (a : Vector (BitVec 64) 5) :
    wideValue (negateWide a) + wideValue a = if wideValue a = 0 then 0 else 2^320 := by
  let v0 := subSpec (0 : BitVec 64) a[0]
  let v1 := sbbSpec (0 : BitVec 64) a[1] (BitVec.ofBool v0.2.CF)
  let v2 := sbbSpec (0 : BitVec 64) a[2] (BitVec.ofBool v1.2.CF)
  let v3 := sbbSpec (0 : BitVec 64) a[3] (BitVec.ofBool v2.2.CF)
  have h0 := subSpec_toNat_add_borrow (0 : BitVec 64) a[0]
  have h1 := sbbSpec_toNat_add_borrow (0 : BitVec 64) a[1] (BitVec.ofBool v0.2.CF)
  have h2 := sbbSpec_toNat_add_borrow (0 : BitVec 64) a[2] (BitVec.ofBool v1.2.CF)
  have h3 := sbbSpec_toNat_add_borrow (0 : BitVec 64) a[3] (BitVec.ofBool v2.2.CF)
  change (-a[0]).toNat + a[0].toNat = 0 + 2^64*v0.2.CF.toNat at h0
  change v1.1.toNat + a[1].toNat + (BitVec.ofBool v0.2.CF).toNat = 0 + 2^64*v1.2.CF.toNat at h1
  change v2.1.toNat + a[2].toNat + (BitVec.ofBool v1.2.CF).toNat = 0 + 2^64*v2.2.CF.toNat at h2
  change v3.1.toNat + a[3].toNat + (BitVec.ofBool v2.2.CF).toNat = 0 + 2^64*v3.2.CF.toNat at h3
  simp only [BitVec.toNat_ofBool, Nat.zero_add] at h0 h1 h2 h3
  have ha := wideValue_lt a
  have hn := wideValue_lt (negateWide a)
  have ht := a[4].isLt
  have hexpand : wideValue (negateWide a) = (-a[0]).toNat + 2^64*v1.1.toNat +
      2^128*v2.1.toNat + 2^192*v3.1.toNat +
      2^256*((~~~a[4] + ((if !v3.2.CF then 1 else 0) : BitVec 8).setWidth 64).toNat) := by
    simp only [negateWide,wideValue_eq,Vector.getElem_mk,List.getElem_toArray,
      List.getElem_cons_succ,List.getElem_cons_zero]
    rfl
  rw [hexpand] at hn
  rw [hexpand,wideValue_eq]
  rw [wideValue_eq] at ha
  simp only [BitVec.toNat_add,BitVec.toNat_not,BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
  cases hc : v3.2.CF <;> simp only [hc,Bool.not_false,Bool.not_true,
    Bool.toNat_false,Bool.toNat_true,Bool.false_eq_true,ite_false,ite_true,
    show (0 : BitVec 8).toNat = 0 from rfl,show (1 : BitVec 8).toNat = 1 from rfl] at * <;>
    split <;> omega
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
