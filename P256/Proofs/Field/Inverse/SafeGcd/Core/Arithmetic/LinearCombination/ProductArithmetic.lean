import P256.Proofs.Field.Schoolbook.LowerSums.Arithmetic
set_option autoImplicit false
open P256.Proofs.Field.Schoolbook (firstRow firstRow_lt packFive packFive_firstRow)
open P256.Proofs.Field.Montgomery (wordBase)
open P256.Proofs.Common.Instructions (mulHigh64)
open P256.Proofs.Common.Instructions.Carry (adcSpec adcSpec_toNat)

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
open X86Proofs

private theorem mulHigh64_comm (a b : BitVec 64) : mulHigh64 a b = mulHigh64 b a := by
  simp only [mulHigh64, Nat.mul_comm]

private theorem addSpec_comm (a b : BitVec 64) : addSpec a b = addSpec b a := by
  simp only [addSpec, BitVec.add_comm, Nat.add_comm, Int.add_comm]

theorem product_limbs (u a0 a1 a2 a3 : BitVec 64) :
    let v1 := addSpec (u*a1) (mulHigh64 u a0)
    let v2 := adcSpec (u*a2) (mulHigh64 u a1) (BitVec.ofBool v1.2.CF)
    let v3 := adcSpec (u*a3) (mulHigh64 u a2) (BitVec.ofBool v2.2.CF)
    let v4 := adcSpec (mulHigh64 u a3) 0 (BitVec.ofBool v3.2.CF)
    packFive #v[(u*a0).toNat,v1.1.toNat,v2.1.toNat,v3.1.toNat,v4.1.toNat] =
      u.toNat * (a0.toNat + wordBase*a1.toNat + wordBase^2*a2.toNat + wordBase^3*a3.toNat) := by
  dsimp only
  have hrow := P256.Proofs.Field.Schoolbook.lowerSums_firstRow u a0 a1 a2 a3
  simp only [BitVec.mul_comm a0 u, BitVec.mul_comm a1 u, BitVec.mul_comm a2 u,
    BitVec.mul_comm a3 u, mulHigh64_comm a0 u, mulHigh64_comm a1 u,
    mulHigh64_comm a2 u, mulHigh64_comm a3 u,
    addSpec_comm (mulHigh64 u a0) (u*a1)] at hrow
  have hp (a : BitVec 64) : a.toNat*u.toNat ≤ (wordBase-1)*(wordBase-1) := by
    have ha := a.isLt
    have hu := u.isLt
    exact Nat.mul_le_mul (by dsimp only [wordBase]; omega) (by dsimp only [wordBase]; omega)
  have hbound := firstRow_lt _ _ _ _ (hp a0) (hp a1) (hp a2) (hp a3) 4 (by decide)
  rw [hrow] at hbound
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero] at hbound
  have hv4 := adcSpec_toNat (mulHigh64 u a3) 0
    (BitVec.ofBool (adcSpec (u*a3) (mulHigh64 u a2)
      (BitVec.ofBool (adcSpec (u*a2) (mulHigh64 u a1)
        (BitVec.ofBool (addSpec (u*a1) (mulHigh64 u a0)).2.CF)).2.CF)).2.CF)
  simp only [BitVec.toNat_ofBool, show (0 : BitVec 64).toNat=0 from rfl, Nat.add_zero] at hv4
  rw [Nat.mod_eq_of_lt hbound] at hv4
  calc
    _ = packFive (firstRow (a0.toNat*u.toNat) (a1.toNat*u.toNat)
        (a2.toNat*u.toNat) (a3.toNat*u.toNat)) := by
      rw [hrow, hv4]
    _ = _ := by
      rw [packFive_firstRow, Nat.mul_comm u.toNat]
      simp only [Nat.add_mul, Nat.mul_assoc]
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
