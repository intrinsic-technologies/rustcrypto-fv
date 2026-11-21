import P256.Proofs.Sec1.Affine.Uncompressed.Output.State
import P256.Proofs.Sec1.Affine.Uncompressed.Output.SelectSetup
import P256.Proofs.PublicPoint.Normalize.Invert.SelectCall
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec P256.Spec.Program P256.Spec.Operations Standards.SECG.ECC Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Program.FieldCall

def firstSite : BinaryCallSite 3360 760 0x114380 128 where
  codeOffset := 0x10ca4
  disp := 0x36d7
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨768,592,664,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 744
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def secondSite : BinaryCallSite 3360 760 0x114380 128 where
  codeOffset := 0x10cbe
  disp := 0x36bd
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨768,560,632,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 712
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

theorem select_x [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes)
    (state : Prepared s t bytes) : ∃ fuel u, Advances boundary fuel t u ∧ XSelected s u bytes := by
  obtain ⟨n,v,run,ready,_,effect⟩ := select_first_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10c95 selectFirstBytes
      (by decide) (by decide +kernel)) state.rip
  have memory := effect.agrees.external (by simp [selectFirstEffect, Effect.components, Component.Covers])
  have frame := state.toFrameState.after_registers ready effect.agrees
    (by simp [selectFirstEffect, Effect.components, Component.Covers])
    (by simp [selectFirstEffect, Effect.components])
  have values := effect.writes
  simp only [selectFirstEffect, Write.AllHold] at values
  have flag := select_flag state.choice values.2.2.2
  have choice : (v.regValue .rcx).setWidth 8 = if valid bytes then 1 else 0 := flag
  obtain ⟨m,u,called,finished,rip,value,saved,bytes',_⟩ := PublicPoint.Normalize.select_binary_call
    (op := fun x y => if valid bytes then y else x)
    pre.toCalleePre frame firstSite
    (fun w hp hc hx hy => Projective.Multiply.Machine.Lookup.Select.field_select_low8_correct hp hx hy
      ((congrArg (BitVec.setWidth 8) hc).trans choice))
    effect.rip (values.2.2.1.trans state.rax)
    (values.2.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
    (values.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
    (state.zeroX.of_bytes_eq (by intro i hi; rw [memory]; rfl))
    (state.x.of_bytes_eq (by intro i hi; rw [memory]; rfl))
  refine ⟨n+m,u,run.trans called,finished,rip,?_,value,?_,?_,?_,?_,?_⟩
  · exact (saved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp [selectFirstEffect, Effect.components])).trans state.output)
  · apply state.y.of_bytes_eq
    intro i hi
    exact (bytes' 712 32 (by decide) (by decide) (Or.inr (by decide)) i hi).trans
      (by rw [memory]; rfl)
  · apply state.zeroY.of_bytes_eq
    intro i hi
    exact (bytes' 560 32 (by decide) (by decide) (Or.inl (by decide)) i hi).trans
      (by rw [memory]; rfl)
  · exact (saved .r14 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 14) (by simp [selectFirstEffect, Effect.components])).trans state.r14)
  · exact (congrArg (BitVec.setWidth 8) ((saved .rbp (by simp)).trans
      (effect.agrees.read (n := 64) (r := 5) (by simp [selectFirstEffect, Effect.components])))).trans state.choice
  · exact (congrArg (BitVec.setWidth 8) ((saved .r15 (by simp)).trans
      (effect.agrees.read (n := 64) (r := 15) (by simp [selectFirstEffect, Effect.components])))).trans state.infinity

theorem select_y [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes)
    (state : XSelected s t bytes) :
    ∃ fuel u, Advances boundary fuel t u ∧ Selected s u bytes := by
  obtain ⟨n,v,run,ready,_,effect⟩ := select_second_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10ca9 selectSecondBytes
      (by decide) (by decide +kernel)) state.rip
  have memory := effect.agrees.external (by simp [selectSecondEffect, Effect.components, Component.Covers])
  have frame := state.toFrameState.after_registers ready effect.agrees
    (by simp [selectSecondEffect, Effect.components, Component.Covers])
    (by simp [selectSecondEffect, Effect.components])
  have values := effect.writes
  simp only [selectSecondEffect, Write.AllHold] at values
  have flag := select_flag state.choice values.2.2.2
  have choice : (v.regValue .rcx).setWidth 8 = if valid bytes then 1 else 0 := flag
  obtain ⟨m,u,called,finished,rip,value,saved,bytes',_⟩ := PublicPoint.Normalize.select_binary_call
    (op := fun x y => if valid bytes then y else x)
    pre.toCalleePre frame secondSite
    (fun w hp hc hx hy => Projective.Multiply.Machine.Lookup.Select.field_select_low8_correct hp hx hy
      ((congrArg (BitVec.setWidth 8) hc).trans choice))
    effect.rip
    (values.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
    (values.2.2.1.trans state.r14)
    (values.2.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
    (state.zeroY.of_bytes_eq (by intro i hi; rw [memory]; rfl))
    (state.y.of_bytes_eq (by intro i hi; rw [memory]; rfl))
  refine ⟨n+m,u,run.trans called,finished,rip,?_,?_,value,?_,?_⟩
  · exact (saved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp [selectSecondEffect, Effect.components])).trans state.output)
  · apply state.x.of_bytes_eq
    intro i hi
    exact (bytes' 664 32 (by decide) (by decide) (Or.inr (by decide)) i hi).trans
      (by rw [memory]; rfl)
  · exact (congrArg (BitVec.setWidth 8) ((saved .rbp (by simp)).trans
      (effect.agrees.read (n := 64) (r := 5) (by simp [selectSecondEffect, Effect.components])))).trans state.choice
  · exact (congrArg (BitVec.setWidth 8) ((saved .r15 (by simp)).trans
      (effect.agrees.read (n := 64) (r := 15) (by simp [selectSecondEffect, Effect.components])))).trans state.infinity

end P256.Proofs.Sec1.Affine.Uncompressed.Output
