import P256.Proofs.Ecdh.Normalize.Invert.SelectFacts
import P256.Proofs.PublicPoint.Normalize.Invert.SelectCall
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct

set_option autoImplicit false
namespace P256.Proofs.Ecdh.Normalize
open P256.Spec P256.Spec.Program P256.Spec.Operations Standards.SECG.ECC Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Program.FieldCall

def selectSite : BinaryCallSite 3464 2056 0x114380 128 where
  codeOffset := 0x392
  disp := 0x13fe9
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨2064,2040,176,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 1976
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

theorem select_inverse [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : Inverted s t boundary point) : ∃ u, Selected s u boundary point := by
  obtain ⟨n,v,run,ready,_,effect⟩ := select_setup_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x355 selectSetupBytes
      (by decide) (by decide +kernel)) (select_setup_pre pre state)
  have frame := select_setup_frame pre state.toFrameState ready effect
  have sp : stackPtr v = stackPtr t := effect.agrees.read (n := 64) (r := 4)
    (by simp [selectSetupEffect,Effect.components])
  have values := effect.writes
  simp only [selectSetupEffect,Write.AllHold] at values
  have zero := select_setup_zero pre frame sp effect
  have original : ProjectiveAt v (stackPtr s-1904) point := by
    apply state.projective.of_bytes_eq
    have hb := select_setup_bytes (offset := 152) (len := 96) effect
      (by
        intro k hk
        have hk' : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
        rcases hk' with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide) (by decide)
    rw [scalar_stack_address (frameOffset := 2056) (offset := 152) state.rsp (by decide) (by decide)] at hb
    exact hb
  have inverse : Field.MontgomeryAt v (stackPtr s-1976) (Curve.inverse domain.p point.z) := by
    apply state.inverse.of_bytes_eq
    have hb := select_setup_bytes (offset := 80) (len := 32) effect
      (by
        intro k hk
        have hk' : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
        rcases hk' with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide) (by decide)
    rw [scalar_stack_address (frameOffset := 2056) (offset := 80) state.rsp (by decide) (by decide)] at hb
    exact hb
  have flag := select_setup_choice effect (show t.external[stackPtr t+112]? =
      some (if point.z=0 then 0 else 1) by
    exact (congrArg (fun a => t.external[a]?)
      (show stackPtr t+112 = stackPtr s-1944 from
        scalar_stack_address (frameOffset := 2056) (offset := 112) state.rsp (by decide) (by decide))).trans state.choice)
  have choice : (v.regValue .rcx).setWidth 8 = if decide (point.z ≠ 0) then 1 else 0 := by
    by_cases hz : point.z = 0 <;> simpa [hz] using flag.2
  have savedFlag : (v.regValue .rbp).setWidth 8 = if point.z=0 then 0 else 1 := by
    by_cases hz : point.z = 0 <;> simpa [hz] using flag.1
  have input : v.regValue .rsi = stackPtr s - 2040 := by
    exact values.2.2.2.2.2.2.1.trans (scalar_stack_address (frameOffset := 2056) (offset := 16) state.rsp (by decide) (by decide))
  have right : v.regValue .rdx = stackPtr s-1976 := values.2.2.2.2.2.2.2.2.1.trans state.r15
  have output : v.regValue .rdi = stackPtr s-176 :=
    values.2.2.2.2.2.2.2.1.trans (scalar_stack_address (frameOffset := 2056) state.rsp (by decide) (by decide))
  obtain ⟨m,u,called,finished,rip,value,saved,bytes,_⟩ := PublicPoint.Normalize.select_binary_call
    (op := fun x y => if decide (point.z ≠ 0) then y else x)
    pre frame selectSite
    (fun w hp hc hx hy => Projective.Multiply.Machine.Lookup.Select.field_select_low8_correct hp hx hy
      ((congrArg (BitVec.setWidth 8) hc).trans choice))
    effect.rip input right output (show Field.MontgomeryAt v (stackPtr s - 2040) 0 from (scalar_stack_address (frameOffset := 2056) (offset := 16) state.rsp (by decide) (by decide)) ▸ zero) inverse
  refine ⟨u,finished,?_,rip,?_,?_,?_,?_,?_⟩
  · obtain ⟨fuel,previous⟩ := state.execution
    exact ⟨fuel+n+m,(previous.trans run).trans called⟩
  · exact (saved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp [selectSetupEffect,Effect.components])).trans state.output)
  · apply original.of_bytes_eq
    intro i hi
    exact bytes 1904 96 (by decide) (by decide) (Or.inr (by decide)) i hi
  · have he : (if decide (point.z ≠ 0) then Curve.inverse domain.p point.z else 0) =
        Curve.inverse domain.p point.z := by
      by_cases hz : point.z=0
      · simp [hz,Projective.Algebra.inverse_zero]
      · simp [hz]
    exact he ▸ value
  · exact (congrArg (BitVec.setWidth 8) (saved .rbp (by simp))).trans savedFlag
  · exact (saved .r14 (by simp)).trans
      (values.2.2.2.2.2.1.trans (scalar_stack_address (frameOffset := 2056) state.rsp (by decide) (by decide)))

end P256.Proofs.Ecdh.Normalize
