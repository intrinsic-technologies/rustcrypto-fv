import P256.Proofs.Ecdh.Normalize.Finish.Prepare.Memory
import P256.Proofs.PublicPoint.Normalize.Finish.Constants

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Finish

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field

theorem constant_disjoint [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x100000 32 32 3464) :
    0x2024f0 + 72 ≤ (stackPtr s - 1808).toNat ∨
      (stackPtr s - 1808).toNat + 72 ≤ 0x2024f0 := by
  have hs := stack_bounds pre.stack
  have hn : (stackPtr s - 1808).toNat = (stackPtr s).toNat - 1808 :=
    stack_sub_toNat pre.stack (by decide)
  by_cases hbefore : 0x2024f0 + 72 ≤ (stackPtr s - 1808).toNat
  · exact .inl hbefore
  right
  apply Nat.le_of_not_lt
  intro hafter
  let a := max 0x2024f0 (stackPtr s - 1808).toNat
  have ha : a < 2^64 := by dsimp only [a]; have := (stackPtr s - 1808).isLt; omega
  have he : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
  have him : InProgram (BitVec.ofNat 64 a) := by
    have h := PublicPoint.Normalize.Finish.constant_inProgram (i := a - 0x2024f0) (by dsimp only [a]; omega)
    have hadd : 0x2024f0 + BitVec.ofNat 64 (a - 0x2024f0) = BitVec.ofNat 64 a := by
      rw [show (0x2024f0 : BitVec 64) = BitVec.ofNat 64 0x2024f0 from rfl,
        ← BitVec.ofNat_add, Nat.add_sub_of_le]
      exact Nat.le_max_left _ _
    rwa [hadd] at h
  apply pre.avoids (Stack.region s 3464) (by simp) (BitVec.ofNat 64 a) _ (.inl him)
  change (Stack.region s 3464).start ≤ _ ∧ _ <
    (Stack.region s 3464).start + (Stack.region s 3464).size
  rw [he, stack_region_end]
  change 3464 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 at hs
  change (stackPtr s).toNat - 3464 ≤ a ∧ a < (stackPtr s).toNat + 8
  dsimp only [a]
  omega

end P256.Proofs.Ecdh.Normalize.Finish
