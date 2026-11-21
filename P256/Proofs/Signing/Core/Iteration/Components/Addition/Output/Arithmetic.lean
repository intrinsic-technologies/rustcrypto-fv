import P256.Proofs.SecretKeyFromBytes.Arithmetic
import P256.Proofs.Signing.Core.Iteration.Components.Addition.State

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem selected_sum_mod [Bindings] {s t : RamState} {a b : Nat}
    (state : DifferenceState s t a b)
    (leftCanonical : a < P256.Spec.Operations.domain.n)
    (rightCanonical : b < P256.Spec.Operations.domain.n) :
    ∃ keep : Bool,
      ((if t.regValue .r12 = 0 then 1 else 0) &&& (t.regValue .r13).setWidth 8) =
        (if keep then (1 : BitVec 8) else 0) ∧
      (if keep then (sumLimbs t).toNat else (differenceLimbs t).toNat) =
        (a+b) % P256.Spec.Operations.domain.n := by
  obtain ⟨borrow,hborrow,borrowReg,difference⟩ := state.difference
  have sum := state.sum
  have sumBound := P256.Proofs.SecretKeyFromBytes.Scalar.limbs_toNat_lt (sumLimbs t)
  have differenceBound := P256.Proofs.SecretKeyFromBytes.Scalar.limbs_toNat_lt (differenceLimbs t)
  have orderBound : P256.Spec.Operations.domain.n < 2^256 := by decide +kernel
  have borrowCases : borrow = 0 ∨ borrow = 1 := by
    have h : borrow.toNat = 0 ∨ borrow.toNat = 1 := by omega
    rcases h with h | h
    · left
      exact BitVec.eq_of_toNat_eq h
    · right
      exact BitVec.eq_of_toNat_eq h
  have carryCases : t.regValue .r12 = 0 ∨ t.regValue .r12 = 1 := by
    have h : (t.regValue .r12).toNat = 0 ∨ (t.regValue .r12).toNat = 1 := by omega
    rcases h with h | h
    · left
      exact BitVec.eq_of_toNat_eq h
    · right
      exact BitVec.eq_of_toNat_eq h
  rcases carryCases with carry | carry <;> rcases borrowCases with rfl | rfl
  · refine ⟨false, ?_, ?_⟩
    · rw [borrowReg,carry]
      decide +kernel
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [carry] at sum
      change (sumLimbs t).toNat = a+b at sum
      change (differenceLimbs t).toNat + P256.Spec.Operations.domain.n = (sumLimbs t).toNat at difference
      have lower : P256.Spec.Operations.domain.n ≤ a+b := by omega
      have upper : a+b < P256.Spec.Operations.domain.n*2 := by omega
      rw [Nat.mod_eq_sub_mod lower, Nat.mod_eq_of_lt (by omega)]
      omega
  · refine ⟨true, ?_, ?_⟩
    · rw [borrowReg,carry]
      decide +kernel
    · simp only [↓reduceIte]
      rw [carry] at sum
      change (sumLimbs t).toNat = a+b at sum
      change (differenceLimbs t).toNat + P256.Spec.Operations.domain.n = (sumLimbs t).toNat + 2^256 at difference
      have small : a+b < P256.Spec.Operations.domain.n := by omega
      rw [Nat.mod_eq_of_lt small]
      exact sum
  · rw [carry] at sum
    change (sumLimbs t).toNat + 2^256 = a+b at sum
    change (differenceLimbs t).toNat + P256.Spec.Operations.domain.n = (sumLimbs t).toNat at difference
    omega
  · refine ⟨false, ?_, ?_⟩
    · rw [borrowReg,carry]
      decide +kernel
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [carry] at sum
      change (sumLimbs t).toNat + 2^256 = a+b at sum
      change (differenceLimbs t).toNat + P256.Spec.Operations.domain.n = (sumLimbs t).toNat + 2^256 at difference
      have lower : P256.Spec.Operations.domain.n ≤ a+b := by omega
      have upper : a+b < P256.Spec.Operations.domain.n*2 := by omega
      rw [Nat.mod_eq_sub_mod lower, Nat.mod_eq_of_lt (by omega)]
      omega

end P256.Proofs.Signing.Core.Iteration.Components.Addition
