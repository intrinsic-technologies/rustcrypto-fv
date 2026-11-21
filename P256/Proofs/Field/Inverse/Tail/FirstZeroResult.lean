import P256.Proofs.Field.Inverse.Tail.Support
import P256.Proofs.Field.Inverse.Tail.FirstZero
import P256.Proofs.Field.Inverse.Tail.ZeroState

set_option autoImplicit false

open P256.Proofs.Program (CalleePre)

namespace P256.Proofs.Field.Inverse.FirstZero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem zero_stage_with_zero [Bindings] {s t : RamState} {boundary : ReturnBoundary} {beta : Nat}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x114154) (input : Nat256At t (stackPtr s - 56) beta) :
    ∃ n u, Advances boundary n t u ∧ FrameState s u ∧ u.RIP = 0x11417e ∧
      Nat256At u (stackPtr s - 56) beta ∧
      Nat256At u (stackPtr s - 168) 0 ∧
      AgreesExcept (zeroComponents t 144) t u := by
  obtain ⟨n,u,run,ready,_,effect⟩ := select_zero boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported) (select_zero_code state.loaded)
    (selectZeroPre_of_frame pre state rip)
  have agrees : AgreesExcept (zeroComponents t 144) t u := by
    simpa [zeroComponents, selectZeroEffect, Effect.components, stackPtr, gprIndex] using effect.agrees
  have state1 := zero_frame pre state ready (by decide : 144<152) agrees
  have addr : stackPtr t + 112#64 = stackPtr s - 56 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have output := zero_candidate (source := 112) (by decide) agrees (by rw [addr]; exact input)
  rw [addr] at output
  have zero : Nat256At u (stackPtr s - 168) 0 := by
    apply nat256At_zero_limbs
    · intro i hi
      exact effect.agrees.grow _ (state.allocated _
        ((P256.Proofs.Program.stack_sub_readable pre.stack
          (offset := 168) (len := 32) (by decide) (by decide)).mem i hi))
    · have words := effect.writes.2
      change memLoad u.external (stackPtr t + 0) 64 = 0 ∧
        memLoad u.external (stackPtr t + 8) 64 = 0 ∧
        memLoad u.external (stackPtr t + 16) 64 = 0 ∧
        memLoad u.external (stackPtr t + 24) 64 = 0 at words
      rw [state.rsp] at words
      exact words
  exact ⟨n,u,run,state1,effect.rip,output,zero,agrees⟩

end P256.Proofs.Field.Inverse.FirstZero
