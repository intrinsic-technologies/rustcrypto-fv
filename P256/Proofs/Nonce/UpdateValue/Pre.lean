import P256.Proofs.Nonce.UpdateValue.Interface
import P256.Proofs.Program.ScalarFrame.Prologue

set_option autoImplicit false

namespace P256.Proofs.Nonce

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem DrbgCalleePre.callee [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {reserve : Nat} {state : State}
    (pre : DrbgCalleePre s boundary entry reserve state) :
    CalleePre s boundary entry 0 64 reserve .rdi := by
  refine ⟨pre.bindingsSupported, pre.machine, pre.directionFlag, pre.loaded, pre.rip,
    ?_, ?_, pre.stateBounded, pre.stateAllocated, pre.stack, ?_, pre.avoids,
    pre.outerBoundary, pre.returnInProgram⟩
  · change (s.regValue .rdi).toNat + 0 < 2^32
    have h := pre.stateBounded
    change (s.regValue .rdi).toNat + 64 < 2^32 at h
    omega
  · intro a ha
    have h : (s.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (s.regValue .rdi).toNat + 0 := ha
    omega
  · intro i j hij
    have pairs : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases pairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro a ha _
      change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + 0 at ha
      omega
    · intro a ha _
      change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + 0 at ha
      omega
    · exact pre.separation

end P256.Proofs.Nonce
