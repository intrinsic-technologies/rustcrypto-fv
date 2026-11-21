import P256.Proofs.Sec1.Affine.Compressed.Finish.State
import P256.Proofs.Sec1.Affine.Compressed.Finish.SelectSetup
import P256.Proofs.Sec1.Affine.Compressed.Finish.SelectCall
import P256.Proofs.Sec1.Representation
import P256.Proofs.Common.Field.SquareRoot.Exponent.ReadDigit.State
import P256.Proofs.Common.Memory.LoadByte

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC
open ScalarFrame FieldCall

def firstSite : BinaryCallSite 3360 760 0x114380 128 where
  codeOffset := 0x1016c
  disp := 0x420f
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨768,664,384,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 744
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def secondSite : BinaryCallSite 3360 760 0x114380 128 where
  codeOffset := 0x10188
  disp := 0x41f3
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨768,632,352,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 712
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

theorem select_first_choice [Bindings] {s t : RamState} {point : Option Curve.Point}
    (state : Prepared s t point) :
    ((memLoad t.external (stackPtr t + 88) 32).setWidth 64).setWidth 8 =
      if point.isSome then 1 else 0 := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
    P256.Proofs.Common.Field.SquareRoot.memLoad_setWidth_of_le _ _ (by decide) (by decide)]
  have address : stackPtr t + 88 = stackPtr s - 744 + 72 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  rw [address]
  have decoded := state.decoded
  cases point with
  | none => rw [P256.Proofs.Common.Memory.memLoad8_of_byte decoded]; rfl
  | some p => rw [P256.Proofs.Common.Memory.memLoad8_of_byte decoded.2]; rfl

theorem select_x [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : Prepared s t point) : ∃ fuel u, Advances boundary fuel t u ∧ XSelected s u point := by
  obtain ⟨n,v,run,ready,_,effect⟩ := select_first_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x1015b selectFirstBytes
      (by decide) (by decide +kernel))
    ⟨state.rip, stack_readable pre.toCalleePre state.toFrameState (by decide) (by decide)⟩
  have memory := effect.agrees.external (by simp [selectFirstEffect, Effect.components, Component.Covers])
  have frame := state.toFrameState.after_registers ready effect.agrees
    (by simp [selectFirstEffect, Effect.components, Component.Covers])
    (by simp [selectFirstEffect, Effect.components])
  have values := effect.writes
  simp only [selectFirstEffect, Write.AllHold] at values
  have flag := select_first_choice state
  obtain ⟨m,u,called,finished,rip,value,saved,kept,_⟩ := select_bytes_call
    pre.toCalleePre frame firstSite
    ((congrArg (BitVec.setWidth 8) values.2.2.2).trans flag)
    effect.rip (values.2.2.1.trans state.rax)
    ((effect.agrees.read (n := 64) (r := 2) (by simp [selectFirstEffect, Effect.components])).trans state.rdx)
    (values.2.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
  have source : ∀ i < 73, u.external[stackPtr s - 744 + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - 744 + BitVec.ofNat 64 i]? := by
    intro i hi
    exact (kept 744 73 (by decide) (by decide) (Or.inr (by decide)) i hi).trans
      (by rw [memory]; rfl)
  refine ⟨n+m,u,run.trans called,finished,rip,?_,state.decoded.of_bytes_eq source,?_,?_,?_⟩
  · exact (saved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp [selectFirstEffect, Effect.components])).trans state.output)
  · exact (saved .r14 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 14) (by simp [selectFirstEffect, Effect.components])).trans state.validity)
  · exact (congrArg (BitVec.setWidth 8) ((saved .rbp (by simp)).trans values.1)).trans flag
  · intro valid i hi
    have selected := value i hi
    simp only [valid, ite_true, firstSite, BitVec.ofNat_eq_ofNat, memory] at selected
    exact selected.trans (source i (by omega)).symm

theorem select_y [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : XSelected s t point) : ∃ fuel u, Advances boundary fuel t u ∧ Selected s u point := by
  obtain ⟨n,v,run,ready,_,effect⟩ := select_second_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10171 selectSecondBytes
      (by decide) (by decide +kernel)) state.rip
  have memory := effect.agrees.external (by simp [selectSecondEffect, Effect.components, Component.Covers])
  have frame := state.toFrameState.after_registers ready effect.agrees
    (by simp [selectSecondEffect, Effect.components, Component.Covers])
    (by simp [selectSecondEffect, Effect.components])
  have values := effect.writes
  simp only [selectSecondEffect, Write.AllHold] at values
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
      ((effect.agrees.read (n := 64) (r := 3) (by simp [selectSecondEffect, Effect.components])).trans state.output)
  · exact (saved .r14 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 14) (by simp [selectSecondEffect, Effect.components])).trans state.validity)
  · exact (congrArg (BitVec.setWidth 8) ((saved .rbp (by simp)).trans
      (effect.agrees.read (n := 64) (r := 5) (by simp [selectSecondEffect, Effect.components])))).trans state.choice
  · intro valid i hi
    apply Eq.trans _ (source i (by omega)).symm
    by_cases small : i < 32
    · exact (kept 384 32 (by decide) (by decide) (Or.inr (by decide)) i small).trans
        ((by rw [memory] : v.external[stackPtr s - 384 + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - 384 + BitVec.ofNat 64 i]?).trans (state.selected valid i small))
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
      rw [offset, addr 384 352 (by decide +kernel), addr 744 712 (by decide +kernel)]
      exact selected

end P256.Proofs.Sec1.Affine.Compressed.Finish
