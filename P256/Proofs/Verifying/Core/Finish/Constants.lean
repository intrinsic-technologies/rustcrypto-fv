import P256.Proofs.Verifying.Core.Finish.Memory
import P256.Proofs.PublicPoint.Normalize.Finish.Constants

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field
open PublicPoint.Normalize.Finish (constant_inProgram constant_readable constant_zero)

theorem constant_disjoint [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10d570 72 24 9992) :
    0x2024f0 + 72 ≤ (stackPtr s - 600).toNat ∨
      (stackPtr s - 600).toNat + 72 ≤ 0x2024f0 := by
  have hs := stack_bounds pre.stack
  have hn : (stackPtr s - 600).toNat = (stackPtr s).toNat - 600 :=
    stack_sub_toNat pre.stack (by decide)
  by_cases hbefore : 0x2024f0 + 72 ≤ (stackPtr s - 600).toNat
  · exact .inl hbefore
  right
  apply Nat.le_of_not_lt
  intro hafter
  let a := max 0x2024f0 (stackPtr s - 600).toNat
  have ha : a < 2^64 := by dsimp only [a]; have := (stackPtr s - 600).isLt; omega
  have he : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
  have him : InProgram (BitVec.ofNat 64 a) := by
    have h := constant_inProgram (i := a - 0x2024f0) (by dsimp only [a]; omega)
    have hadd : 0x2024f0 + BitVec.ofNat 64 (a - 0x2024f0) = BitVec.ofNat 64 a := by
      rw [show (0x2024f0 : BitVec 64) = BitVec.ofNat 64 0x2024f0 from rfl,
        ← BitVec.ofNat_add, Nat.add_sub_of_le]
      exact Nat.le_max_left _ _
    rwa [hadd] at h
  apply pre.avoids (Stack.region s 9992) (by simp) (BitVec.ofNat 64 a) _ (.inl him)
  change (Stack.region s 9992).start ≤ _ ∧ _ <
    (Stack.region s 9992).start + (Stack.region s 9992).size
  rw [he, stack_region_end]
  change 9992 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 at hs
  change (stackPtr s).toNat - 9992 ≤ a ∧ a < (stackPtr s).toNat + 8
  dsimp only [a]
  omega


end P256.Proofs.Verifying.Core.Finish
