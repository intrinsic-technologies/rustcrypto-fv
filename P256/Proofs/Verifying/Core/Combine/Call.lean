import P256.Proofs.Verifying.Core.Combine.Constants
import P256.Proofs.Verifying.Combination.Input
import P256.Proofs.Program.FieldCall.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Combine

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame FieldCall
open SecretKeyFromBytes.Scalar (Nat256At)
open Projective.Multiply.Machine.Basepoint (basePoint)

def callLayout : StackCallLayout 9992 256 96 8808 :=
  ⟨1184,1048,1176,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} {u v r : Nat} (pre : Core.Pre s boundary)
    (state : Ready s t point u v r) (valid : point.valid)
    (combination : Combination.Correct) :
    ∃ fuel z result, Advances boundary fuel t z ∧ Frame s z ∧ z.RIP = 0x10de41 ∧
      ProjectiveAt z (frameBase s) result ∧ result.valid ∧
      result.toAffine = Points.add (Points.mul u Operations.domain.G) (Points.mul v point.toAffine) ∧
      Nat256At z (frameBase s+704#64) r ∧ memLoad z.external (frameBase s+384) 64 = s.regValue .rdi ∧
      MemoryWriteFrame t z #v[Stack.region s 9992] := by
  obtain ⟨a,runA,readyA,effect⟩ := scalar_call pre.toCalleePre (by decide) (by decide)
    state.toFrameState 0xde3c 0xffff86bf (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x6500 (by decide)) state.rip
  have frameA := state.toFrameState.after_call pre.toCalleePre (by decide) (by decide) readyA effect
  have inputAddress : frameBase s+128#64 = stackPtr s-1048#64 := by
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have ai : a.regValue .rsi = stackPtr s-1048#64 :=
    ((effect.agrees.read (n := 64) (r := 6) (by simp)).trans state.source).trans inputAddress
  have ao : a.regValue .rdi = stackPtr s-1176#64 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans state.destination
  have ret : (returnBoundary a).rip = 0x10de41 := (callEffect_stack effect).1
  have cp : Combination.Pre a boundary :=
    CalleePre.of_stack pre.toCalleePre callLayout frameA.bindingsSupported frameA.machine
      frameA.directionFlag frameA.loaded frameA.allocated effect.rip frameA.rsp ai ao
      (by rw [ret]; exact inProgram_of_textOffset 0xde41 (by decide))
  have input : Combination.InputAt a (a.regValue .rsi) basePoint point u v := by
    rw [ai,← inputAddress]
    have initial : Combination.InputAt t (frameBase s+128#64) basePoint point u v := state.input
    apply initial.of_bytes_eq
    intro i hi
    rw [inputAddress]
    exact scalar_call_byte (frameOffset := 1176) (offset := 1048) (by decide) state.toFrameState effect
      (by decide) (by decide) hi
  obtain ⟨z,result,out,value,correct⟩ := combination a boundary basePoint point u v cp input
    generator_valid valid
  obtain ⟨fuel,runZ⟩ := out.execution
  have memory := stack_result_work_frame (frameOffset := 1176) pre.toCalleePre frameA out ao
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨1+fuel,z,result,runA.trans runZ,
    after_result (frameOffset := 1176) pre.toCalleePre frameA out (by decide) memory,
    out.rip.trans ret,?_,correct.1,?_,?_,?_,?_⟩
  · rwa [ao] at value
  · simpa only [generator_toAffine] using correct.2
  · have addr : frameBase s+704#64 = stackPtr s-472#64 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    have saved : Nat256At t (frameBase s+704#64) r := state.savedR
    rw [addr] at saved ⊢
    refine ⟨saved.1,fun i hi => ?_⟩
    exact (stack_result_byte (frameOffset := 1176) pre.toCalleePre frameA out ao
      (by decide) (by decide) (by decide) (by decide) (.inl (by decide)) hi).trans
      ((scalar_call_byte (frameOffset := 1176) (by decide) state.toFrameState effect
        (by decide) (by decide) hi).trans (saved.2 i hi))
  · have pm := memoryWriteFrame_trans (prefix_call pre state.toFrameState effect)
      (prefix_result pre frameA out (offset := 0)
        (by simpa [frameBase] using ao) (by decide) (by decide))
    exact (prefix_load pre pm (offset := 384) (n := 64) (by decide) (by decide)).trans state.output
  · exact work_memory_stack pre (memoryWriteFrame_trans
      (field_call_work_frame pre.toCalleePre state.toFrameState (by decide) (by decide) effect) memory)

end P256.Proofs.Verifying.Core.Combine
