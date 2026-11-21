import P256.Proofs.Sec1.Affine.Compact.Select.State
import P256.Proofs.Sec1.Affine.Compact.Select.Setup
import P256.Proofs.Sec1.Affine.Compressed.Finish.SelectCall
import P256.Proofs.Sec1.Representation
import P256.Proofs.Common.Field.SquareRoot.Exponent.ReadDigit.State
import P256.Proofs.Common.Memory.LoadByte

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Select

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC
open ScalarFrame FieldCall

def firstSite : BinaryCallSite 3360 760 0x114380 128 where
  codeOffset := 0x1025a
  disp := 0x4121
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨768,384,480,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 744
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def secondSite : BinaryCallSite 3360 760 0x114380 128 where
  codeOffset := 0x10276
  disp := 0x4105
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨768,352,448,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 712
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

theorem select_first_choice [Bindings] {s t : RamState} {point : Option Curve.Point}
    (state : Initialized s t point) :
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
    (state : Initialized s t point) : ∃ fuel u, Advances boundary fuel t u ∧ XSelected s u point := by
  obtain ⟨n,v,run,ready,_,effect⟩ := select_first_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10246 selectFirstBytes
      (by decide) (by decide +kernel))
    ⟨state.rip, stack_readable pre.toCalleePre state.toFrameState (by decide) (by decide)⟩
  have memory := effect.agrees.external (by simp [selectFirstEffect, Effect.components, Component.Covers])
  have frame := state.toFrameState.after_registers ready effect.agrees
    (by simp [selectFirstEffect, Effect.components, Component.Covers])
    (by simp [selectFirstEffect, Effect.components])
  have values := effect.writes
  simp only [selectFirstEffect, Write.AllHold] at values
  have flag := select_first_choice state
  obtain ⟨m,u,called,finished,rip,value,saved,kept,_⟩ := Compressed.Finish.select_bytes_call
    pre.toCalleePre frame firstSite
    ((congrArg (BitVec.setWidth 8) values.2.2.2.2).trans flag)
    effect.rip (values.2.2.1.trans state.rax)
    (values.2.2.2.1.trans state.source)
    (values.2.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
  have source : ∀ i < 73, u.external[stackPtr s - 744 + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - 744 + BitVec.ofNat 64 i]? := by
    intro i hi
    exact (kept 744 73 (by decide) (by decide) (Or.inr (by decide)) i hi).trans
      (by rw [memory]; rfl)
  refine ⟨n+m,u,run.trans called,finished,rip,?_,state.decoded.of_bytes_eq source,?_,?_,?_,?_⟩
  · exact (saved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp [selectFirstEffect, Effect.components])).trans state.output)
  · have zeroX := state.identity.1
    have decoded := state.decoded
    cases point with
    | none =>
      apply zeroX.of_bytes_eq
      intro i hi
      simpa only [Option.isSome_none, Bool.false_eq_true, ite_false, firstSite,
        BitVec.ofNat_eq_ofNat, memory] using value i hi
    | some p =>
      cases p with
      | infinity =>
        apply decoded.1.1.of_bytes_eq
        intro i hi
        simpa only [Option.isSome_some, ite_true, firstSite,
          BitVec.ofNat_eq_ofNat, memory] using value i hi
      | affine x y =>
        apply decoded.1.1.of_bytes_eq
        intro i hi
        simpa only [Option.isSome_some, ite_true, firstSite,
          BitVec.ofNat_eq_ofNat, memory] using value i hi
  · apply state.identity.2.1.of_bytes_eq
    intro i hi
    have eqn := kept 352 32 (by decide) (by decide) (Or.inl (by decide)) i hi
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
      BitVec.reduceAdd, memory, BitVec.ofNat_eq_ofNat] using eqn
  · exact (saved .r13 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 13) (by simp [selectFirstEffect, Effect.components])).trans state.zero)
  · exact (congrArg (BitVec.setWidth 8) ((saved .rbp (by simp)).trans values.1)).trans flag

theorem select_y [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : XSelected s t point) : ∃ fuel u, Advances boundary fuel t u ∧ Selected s u point := by
  obtain ⟨n,v,run,ready,_,effect⟩ := select_second_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x1025f selectSecondBytes
      (by decide) (by decide +kernel)) state.rip
  have memory := effect.agrees.external (by simp [selectSecondEffect, Effect.components, Component.Covers])
  have frame := state.toFrameState.after_registers ready effect.agrees
    (by simp [selectSecondEffect, Effect.components, Component.Covers])
    (by simp [selectSecondEffect, Effect.components])
  have values := effect.writes
  simp only [selectSecondEffect, Write.AllHold] at values
  have flag : (v.regValue .rcx).setWidth 8 = if point.isSome then 1 else 0 := by
    have reg : v.regValue .rcx = ((t.regValue .rbp).setWidth 32).setWidth 64 := values.2.2.2
    rw [reg, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
    exact state.choice
  obtain ⟨m,u,called,finished,rip,value,saved,kept,_⟩ := Compressed.Finish.select_bytes_call
    pre.toCalleePre frame secondSite flag effect.rip
    (values.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
    (values.2.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
    (values.2.2.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
  have source : ∀ i < 73, u.external[stackPtr s - 744 + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - 744 + BitVec.ofNat 64 i]? := by
    intro i hi
    exact (kept 744 73 (by decide) (by decide) (Or.inr (by decide)) i hi).trans
      (by rw [memory]; rfl)
  refine ⟨n+m,u,run.trans called,finished,rip,?_,state.decoded.of_bytes_eq source,?_,?_,?_,?_⟩
  · exact (saved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp [selectSecondEffect, Effect.components])).trans state.output)
  · apply state.x.of_bytes_eq
    intro i hi
    exact (kept 480 32 (by decide) (by decide) (Or.inr (by decide)) i hi).trans
      (by rw [memory]; rfl)
  · have zeroY := state.zeroY
    have decoded := state.decoded
    cases point with
    | none =>
      apply zeroY.of_bytes_eq
      intro i hi
      simpa only [Option.isSome_none, Bool.false_eq_true, ite_false, secondSite,
        BitVec.ofNat_eq_ofNat, memory] using value i hi
    | some p =>
      cases p with
      | infinity =>
        apply decoded.1.2.1.of_bytes_eq
        intro i hi
        simpa only [Option.isSome_some, ite_true, secondSite, BitVec.ofNat_eq_ofNat, memory, BitVec.sub_eq_add_neg,
          BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using value i hi
      | affine x y =>
        apply decoded.1.2.1.of_bytes_eq
        intro i hi
        simpa only [Option.isSome_some, ite_true, secondSite, BitVec.ofNat_eq_ofNat, memory, BitVec.sub_eq_add_neg,
          BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using value i hi
  · exact (saved .r13 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 13) (by simp [selectSecondEffect, Effect.components])).trans state.zero)
  · exact (congrArg (BitVec.setWidth 8) ((saved .rbp (by simp)).trans
      (effect.agrees.read (n := 64) (r := 5) (by simp [selectSecondEffect, Effect.components])))).trans state.choice

end P256.Proofs.Sec1.Affine.Compact.Select
