import P256.Proofs.Nonce.Fill.Update.Arguments
import P256.Proofs.Nonce.Fill.CallResult
import P256.Proofs.Nonce.Fill.Mathematics
import P256.Proofs.Nonce.Update.Interface

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Update

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s called t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {original state : State}

theorem call (pre : Pre initial boundary orderAddress original)
    (input : Ready initial s orderAddress state) :
    ∃ called, Advances boundary 1 s called ∧
      (callEffect (fun _ => 0x109f30) 0x1073eb s).Holds s called ∧
      UpdateEmptyPre called boundary (updateValue state) := by
  obtain ⟨called, run, ready, effect⟩ := ScalarFrame.call_step pre.toCalleePre
    (frameOffset := 232) (by decide) (by decide)
    (readyToStep input.machine input.bindingsSupported) input.loaded input.allocated input.rsp
    0x73e6 0x2b45 (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x9f30 (by decide)) input.rip
  change (callEffect (fun _ => 0x109f30) 0x1073eb s).Holds s called at effect
  refine ⟨called, run, effect,
    call_drbg_pre pre input.toFrame (by decide) ready effect input.rdi
      (inProgram_of_textOffset 0x73eb (by decide)) input.generator,
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans input.count⟩

theorem returned (pre : Pre initial boundary orderAddress original)
    (input : Ready initial s orderAddress state)
    (effect : (callEffect (fun _ => 0x109f30) 0x1073eb s).Holds s called)
    (result : DrbgCalleeResult called t boundary 1856
      (updateState false ByteArray.empty (updateValue state))) :
    Updated initial t orderAddress state := by
  have memory := call_result_memory pre input.toFrame (by decide) effect input.rdi
    result.toCalleeResult
  refine ⟨input.toFrame.after_drbg_call pre (by decide) effect input.rdi result.toCalleeResult,
    input.toSlots.of_call_frame pre memory,
    result.rip.trans (callEffect_stack effect).1, ?_, ?_⟩
  · apply generator_after_call pre memory input.generator
    rw [nextState_eq]
    have output : called.regValue .rdi = initial.regValue .rdi + 8 :=
      (effect.agrees.read (n := 64) (r := 7) (by simp)).trans input.rdi
    simpa only [output] using result.stateBytes
  · exact frame_hasBytes memory (fun _ member => call_output_apart pre member)
      pre.inputBounded input.output

end P256.Proofs.Nonce.Fill.Update
