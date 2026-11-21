import P256.Proofs.Field.Schoolbook.Carry
import P256.Proofs.Common.Instructions.Carry.Arithmetic
import P256.Proofs.Common.Instructions.Mul.Spec

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64)
open P256.Proofs.Common.Instructions.Carry (adcSpec adcSpec_toNat_add_carry addSpec_toNat_add_carry)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Field.Montgomery (wordBase)

open X86Proofs

theorem addWord_eq_iff (a b c low high : Nat) :
    addWord a b c = (low, high) ↔
      low < wordBase ∧ low + wordBase*high = a+b+c := by
  simp only [addWord, Prod.mk.injEq]
  dsimp [wordBase]
  omega

theorem addSpec_addWord (a b : BitVec 64) :
    ((addSpec a b).1.toNat, (addSpec a b).2.CF.toNat) = addWord a.toNat b.toNat 0 := by
  apply Eq.symm
  apply (addWord_eq_iff _ _ _ _ _).mpr
  exact ⟨(addSpec a b).1.isLt, by simpa only [Nat.add_zero] using addSpec_toNat_add_carry a b⟩

theorem adcSpec_addWord (a b : BitVec 64) (carry : BitVec 1) :
    ((adcSpec a b carry).1.toNat, (adcSpec a b carry).2.CF.toNat) =
      addWord a.toNat b.toNat carry.toNat := by
  apply Eq.symm
  apply (addWord_eq_iff _ _ _ _ _).mpr
  exact ⟨(adcSpec a b carry).1.isLt, adcSpec_toNat_add_carry a b carry⟩

theorem mulHigh64_toNat (a b : BitVec 64) :
    (mulHigh64 a b).toNat = a.toNat*b.toNat / wordBase := by
  change (a.toNat*b.toNat / wordBase) % wordBase = _
  apply Nat.mod_eq_of_lt
  have h := mulWord_high_lt a.isLt b.isLt
  omega

theorem mul64_toNat (a b : BitVec 64) :
    ((a*b).toNat, (mulHigh64 a b).toNat) =
      (a.toNat*b.toNat % wordBase, a.toNat*b.toNat / wordBase) := by
  rw [mulHigh64_toNat]
  rfl

theorem addSpec_addProduct (lo hi c d : BitVec 64) :
    let l1 := addSpec lo c
    let h1 := adcSpec hi 0 (BitVec.ofBool l1.2.CF)
    let l2 := addSpec l1.1 d
    let h2 := adcSpec h1.1 0 (BitVec.ofBool l2.2.CF)
    (l2.1.toNat, h2.1.toNat) =
      addProduct (lo.toNat + wordBase*hi.toNat) c.toNat d.toNat := by
  have hlo : (lo.toNat + wordBase*hi.toNat) % wordBase = lo.toNat := by
    have h := lo.isLt
    dsimp only [wordBase]
    omega
  have hhi : (lo.toNat + wordBase*hi.toNat) / wordBase = hi.toNat := by
    have h := lo.isLt
    dsimp only [wordBase]
    omega
  have h1 := adcSpec_addWord hi 0 (BitVec.ofBool (addSpec lo c).2.CF)
  simp only [BitVec.toNat_ofBool, show (0 : BitVec 64).toNat = 0 from rfl] at h1
  have h2 := adcSpec_addWord (adcSpec hi 0 (BitVec.ofBool (addSpec lo c).2.CF)).1 0
    (BitVec.ofBool (addSpec (addSpec lo c).1 d).2.CF)
  simp only [BitVec.toNat_ofBool, show (0 : BitVec 64).toNat = 0 from rfl] at h2
  simp only [addProduct, hlo, hhi, ← addSpec_addWord lo c, ← h1,
    ← addSpec_addWord (addSpec lo c).1 d, ← h2]

theorem adcSpec_addProduct (lo hi c d : BitVec 64) (carry : BitVec 1) :
    let l1 := adcSpec lo c carry
    let h1 := adcSpec hi 0 (BitVec.ofBool l1.2.CF)
    let l2 := addSpec l1.1 d
    let h2 := adcSpec h1.1 0 (BitVec.ofBool l2.2.CF)
    (l2.1.toNat, h2.1.toNat) =
      addProduct (lo.toNat + wordBase*hi.toNat) (c.toNat + carry.toNat) d.toNat := by
  have hlo : (lo.toNat + wordBase*hi.toNat) % wordBase = lo.toNat := by
    have h := lo.isLt
    dsimp only [wordBase]
    omega
  have hhi : (lo.toNat + wordBase*hi.toNat) / wordBase = hi.toNat := by
    have h := lo.isLt
    dsimp only [wordBase]
    omega
  have hl := adcSpec_addWord lo c carry
  have he : addWord lo.toNat (c.toNat + carry.toNat) 0 =
      addWord lo.toNat c.toNat carry.toNat := by simp [addWord, Nat.add_assoc]
  have h1 := adcSpec_addWord hi 0 (BitVec.ofBool (adcSpec lo c carry).2.CF)
  simp only [BitVec.toNat_ofBool, show (0 : BitVec 64).toNat = 0 from rfl] at h1
  have h2 := adcSpec_addWord (adcSpec hi 0 (BitVec.ofBool (adcSpec lo c carry).2.CF)).1 0
    (BitVec.ofBool (addSpec (adcSpec lo c carry).1 d).2.CF)
  simp only [BitVec.toNat_ofBool, show (0 : BitVec 64).toNat = 0 from rfl] at h2
  simp only [addProduct, hlo, hhi, he, ← hl, ← h1,
    ← addSpec_addWord (adcSpec lo c carry).1 d, ← h2]

end P256.Proofs.Field.Schoolbook
