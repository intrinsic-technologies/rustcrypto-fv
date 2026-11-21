import P256.Proofs.Sec1.Affine.Compact.Finish.State
import P256.Proofs.Sec1.Affine.Compact.Finish.Memory
import P256.Proofs.Sec1.Affine.Compact.Normalize.Arguments
import P256.Proofs.Sec1.Affine.Compressed.Finish.SelectCall
import P256.Proofs.Sec1.Representation
import P256.Proofs.Common.Field.SquareRoot.Exponent.ReadDigit.State
import P256.Proofs.Common.Memory.LoadByte

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC
open ScalarFrame FieldCall Compressed.Finish Normalize

def firstSite : BinaryCallSite 3360 760 0x114380 128 where
  codeOffset := 0x10589
  disp := 0x3df2
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
  codeOffset := 0x105a5
  disp := 0x3dd6
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
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : Ready s t point) : ∃ fuel u, Advances boundary fuel t u ∧ XSelected s u point := by
  obtain ⟨n,v,run,ready,_,effect⟩ := finalX_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x1057f finalXBytes
      (by decide) (by decide +kernel))
    state.rip
  have memory := effect.agrees.external (by simp [finalXEffect, Effect.components, Component.Covers])
  have frame := state.toFrameState.after_registers ready effect.agrees
    (by simp [finalXEffect, Effect.components, Component.Covers])
    (by simp [finalXEffect, Effect.components])
  have values := effect.writes
  simp only [finalXEffect, Write.AllHold] at values
  have flag : (v.regValue .rcx).setWidth 8 = if point.isSome then 1 else 0 := by
    have h : v.regValue .rcx = ((t.regValue .rbp).setWidth 32).setWidth 64 := values.2.2
    rw [h,BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
    exact state.choice
  obtain ⟨m,u,called,finished,rip,value,saved,kept,_⟩ := select_bytes_call
    pre.toCalleePre frame firstSite
    flag
    effect.rip (values.2.1.trans state.rax)
    ((effect.agrees.read (n := 64) (r := 2) (by simp [finalXEffect, Effect.components])).trans state.rdx)
    (values.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
  have source : ∀ i < 73, u.external[stackPtr s - 744 + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - 744 + BitVec.ofNat 64 i]? := by
    intro i hi
    exact (kept 744 73 (by decide) (by decide) (Or.inr (by decide)) i hi).trans
      (by rw [memory]; rfl)
  refine ⟨n+m,u,run.trans called,finished,rip,?_,state.decoded.of_bytes_eq source,?_,?_,?_⟩
  · exact (saved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp [finalXEffect, Effect.components])).trans state.output)
  · exact (congrArg (BitVec.setWidth 8) ((saved .rbp (by simp)).trans
      (effect.agrees.read (n := 64) (r := 5) (by simp [finalXEffect,Effect.components])))).trans state.choice
  · apply Eq.trans (load_preserve (kept 748 1 (by decide) (by decide) (Or.inr (by decide))))
      (by rw [memory]; exact state.mask)
  · intro valid i hi
    have selected := value i hi
    simp only [valid, ite_true, firstSite, BitVec.ofNat_eq_ofNat, memory] at selected
    exact selected.trans (source i (by omega)).symm

theorem select_y [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : XSelected s t point) : ∃ fuel u, Advances boundary fuel t u ∧ Selected s u point := by
  obtain ⟨n,v,run,ready,_,effect⟩ := finalY_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x1058e finalYBytes
      (by decide) (by decide +kernel)) state.rip
  have memory := effect.agrees.external (by simp [finalYEffect, Effect.components, Component.Covers])
  have frame := state.toFrameState.after_registers ready effect.agrees
    (by simp [finalYEffect, Effect.components, Component.Covers])
    (by simp [finalYEffect, Effect.components])
  have values := effect.writes
  simp only [finalYEffect, Write.AllHold] at values
  have flag : (v.regValue .rcx).setWidth 8 = if point.isSome then 1 else 0 := by
    change ((Operand.reg 1 : Operand 64).read v).setWidth 8 = _
    rw [values.2.2.2, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
    exact state.choice
  obtain ⟨m,u,called,finished,rip,value,saved,kept,_⟩ := select_bytes_call
    pre.toCalleePre frame secondSite flag effect.rip
    (values.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
    (values.2.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
    (values.2.2.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
  have source : ∀ i < 73, u.external[stackPtr s - 744 + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - 744 + BitVec.ofNat 64 i]? := by
    intro i hi
    exact (kept 744 73 (by decide) (by decide) (Or.inr (by decide)) i hi).trans
      (by rw [memory]; rfl)
  refine ⟨n+m,u,run.trans called,finished,rip,?_,state.decoded.of_bytes_eq source,?_,?_,?_⟩
  · exact (saved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp [finalYEffect, Effect.components])).trans state.output)
  · exact (congrArg (BitVec.setWidth 8) ((saved .rbp (by simp)).trans
      (effect.agrees.read (n := 64) (r := 5) (by simp [finalYEffect,Effect.components])))).trans state.choice
  · apply Eq.trans (load_preserve (kept 748 1 (by decide) (by decide) (Or.inr (by decide))))
      (by rw [memory]; exact state.mask)
  · intro valid i hi
    apply Eq.trans _ (source i (by omega)).symm
    by_cases small : i < 32
    · exact (kept 664 32 (by decide) (by decide) (Or.inr (by decide)) i small).trans
        ((by rw [memory] : v.external[stackPtr s - 664 + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - 664 + BitVec.ofNat 64 i]?).trans (state.selected valid i small))
    · have selected := value (i-32) (by omega)
      simp only [valid, ite_true, secondSite, BitVec.ofNat_eq_ofNat, memory] at selected
      have offset : BitVec.ofNat 64 i = 32 + BitVec.ofNat 64 (i-32) := by
        change BitVec.ofNat 64 i = BitVec.ofNat 64 32 + BitVec.ofNat 64 (i-32)
        rw [← BitVec.ofNat_add]
        congr 1
        omega
      have addr (a b : BitVec 64) (h : -a + 32 = -b) :
          stackPtr s - a + (32 + BitVec.ofNat 64 (i-32)) =
            stackPtr s - b + BitVec.ofNat 64 (i-32) := by
        rw [← BitVec.add_assoc]
        congr 1
        simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc] using congrArg (stackPtr s + ·) h
      rw [offset, addr 664 632 (by decide +kernel), addr 744 712 (by decide +kernel)]
      exact selected

end P256.Proofs.Sec1.Affine.Compact.Finish
