import P256.Proofs.Field.Inverse.Tail.FirstCopy
import P256.Proofs.Field.Inverse.Tail.CopyState

set_option autoImplicit false

open P256.Proofs.Program (CalleePre)

namespace P256.Proofs.Field.Inverse.FirstCopy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem copy_stage [Bindings] {s t : RamState} {boundary : ReturnBoundary} {beta : Nat}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x11411e) (input : Nat256At t (stackPtr s - 168) beta) :
    ∃ n u, Advances boundary n t u ∧ FrameState s u ∧ u.RIP = 0x11414b ∧
      Nat256At u (stackPtr s - 56) beta ∧
      AgreesExcept (copyComponents t 112) t u := by
  have cp := candidateCopyPre_of_frame pre state rip
  obtain ⟨n,u,run,ready,_,effect⟩ := candidate_copy boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported) (candidate_copy_code state.loaded) cp
  have agrees : AgreesExcept (copyComponents t 112) t u := by
    simpa [copyComponents, candidateCopyEffect, Effect.components, stackPtr, gprIndex] using effect.agrees
  have state1 := copy_frame pre state ready (by decide : 112+32≤152) agrees
  have input' : Nat256At t (stackPtr t + 0#64) beta := by
    simpa only [state.rsp, BitVec.add_zero] using input
  have output := candidateCopyEffect_value cp effect input'
  have addr : stackPtr t + 112 = stackPtr s - 56 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  rw [addr] at output
  exact ⟨n,u,run,state1,effect.rip,output,agrees⟩

end P256.Proofs.Field.Inverse.FirstCopy
