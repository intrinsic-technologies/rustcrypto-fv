import P256.Proofs.Nonce.Fill.Generate.Interface
import P256.Proofs.Nonce.Fill.CallResult
import P256.Proofs.Nonce.UpdateValue

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Generate

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem value [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : State}
    (pre : Pre initial boundary orderAddress original)
    (input : Ready initial s orderAddress state) :
    ∃ fuel t, Advances boundary fuel s t ∧ HasValue initial t orderAddress state := by
  obtain ⟨called, callRun, ready, effect⟩ := ScalarFrame.call_step pre.toCalleePre
    (frameOffset := 232) (by decide) (by decide)
    (readyToStep input.machine input.bindingsSupported)
    input.loaded input.allocated input.rsp 0x73c2 0x3539
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0xa900 (by decide)) input.rip
  change (callEffect (fun _ => 0x10a900) 0x1073c7 s).Holds s called at effect
  have calleePre : UpdateValuePre called boundary state :=
    call_drbg_pre pre input.toFrame (by decide) ready effect input.rdi
      (inProgram_of_textOffset 0x73c7 (by decide)) input.generator
  obtain ⟨t, result⟩ := UpdateValue.correct calleePre
  have memory := call_result_memory pre input.toFrame (by decide) effect input.rdi
    result.toCalleeResult
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨1 + fuel, t, callRun.trans run,
    input.toFrame.after_drbg_call pre (by decide) effect input.rdi result.toCalleeResult,
    input.toSlots.of_call_frame pre memory, ?_, ?_, ?_⟩
  · exact ⟨
      (result.calleeSaved .r12 (by simp)).trans
        ((effect.agrees.read (n := 64) (r := 12) (by simp)).trans input.r12),
      (result.calleeSaved .rbx (by simp)).trans
        ((effect.agrees.read (n := 64) (r := 3) (by simp)).trans input.rbx),
      (result.calleeSaved .rbp (by simp)).trans
        ((effect.agrees.read (n := 64) (r := 5) (by simp)).trans input.rbp),
      (result.calleeSaved .r14 (by simp)).trans
        ((effect.agrees.read (n := 64) (r := 14) (by simp)).trans input.r14),
      (result.calleeSaved .r15 (by simp)).trans
        ((effect.agrees.read (n := 64) (r := 15) (by simp)).trans input.r15)⟩
  · exact result.rip.trans (callEffect_stack effect).1
  · apply generator_after_call pre memory input.generator
    have pointer : called.regValue .rdi = initial.regValue .rdi + 8 :=
      (effect.agrees.read (n := 64) (r := 7) (by simp)).trans input.rdi
    simpa only [pointer] using result.stateBytes

end P256.Proofs.Nonce.Fill.Generate
