import P256.Proofs.Sec1.Affine.Compact.Select
import P256.Proofs.Sec1.Affine.Compact.Flags.Mask
import P256.Proofs.Sec1.Affine.Compact.Flags.Value
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Memory
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Memory.LoadByte

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Flags

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC
open ScalarFrame

def infinityFlag : Option Curve.Point → BitVec 8
  | some (.affine _ _) => 0
  | _ => 1

structure Flagged [Bindings] (s t : RamState) (point : Option Curve.Point) : Prop
    extends Frame s t where
  rip : t.RIP = 0x110294
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (stackPtr s - 480) (Select.xCoordinate point)
  y : Field.MontgomeryAt t (stackPtr s - 448) (Select.yCoordinate point)
  zero : t.regValue .r13 = 0
  choice : (t.regValue .rbp).setWidth 8 = if point.isSome then 1 else 0
  infinity : (t.regValue .r14).setWidth 8 = infinityFlag point
  mask : memLoad t.external (stackPtr s - 748) 8 = -(if point.isSome then 1 else 0)

theorem mask_preserves {t u : RamState} (effect : (maskEffect t).Holds t u)
    {offset len : Nat} (above : 13 ≤ offset) (bound : offset + len ≤ 2^64) :
    ∀ i < len, u.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply Uncompressed.Output.bytes_of_offsets effect.agrees bound
  intro address count member
  simp only [maskEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
    Operand.component, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    Component.mem.injEq, reduceCtorEq, Nat.reduceDiv] at member
  obtain ⟨rfl,rfl⟩ := member
  exact ⟨12,rfl,by decide,Or.inl above⟩

theorem prepare_flags [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : Select.Selected s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Flagged s u point := by
  have hp : MaskPre t := by
    refine ⟨state.rip, ?_, ?_⟩
    · have hw := stack_writable pre.toCalleePre state.toFrameState
        (offset := 12) (len := 1) (by decide) (by decide) (by decide)
      exact ⟨hw.low, hw.mem, hw.tables⟩
    · intro offset len bound
      exact stack_code pre.toCalleePre state.toFrameState (by decide) (by decide) bound
  obtain ⟨n,a,runA,readyA,_,effectA⟩ := mask_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x1027b maskBytes
      (by decide) (by decide +kernel)) hp
  have frameA : Frame s a := by
    apply state.toFrameState.after_effect pre.toCalleePre (by decide) readyA effectA.agrees
    · intro c hc address ha
      simp only [maskEffect,Effect.components,List.map_cons,List.map_nil,Write.component,
        Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,Nat.reduceDiv,or_assoc] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      refine ⟨workRegion s 3360,by simp,?_⟩
      apply work_contains pre.toCalleePre (offset := 748) (len := 1) (by decide) (by decide)
      simpa only [scalar_stack_address (frameOffset := 760) (offset := 12) state.rsp (by decide) (by decide), Nat.reduceSub, BitVec.ofNat_eq_ofNat] using ha
    all_goals simp [maskEffect,Effect.components]
  have lowA : (a.regValue .rax).setWidth 8 = -(if point.isSome then 1 else 0) := by
    have h : a.regValue .rax = mergeGPR 8 (-(t.regValue .rbp).setWidth 8)
        (((t.regValue .rbp).setWidth 32).setWidth 64) := effectA.writes.2
    rw [h, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8, state.choice]
  have sourceA : AffineResultAt a (stackPtr s - 744) point := by
    apply state.decoded.of_bytes_eq
    intro i hi
    have h := mask_preserves effectA (offset := 16) (len := 73) (by decide) (by decide) i hi
    simpa only [scalar_stack_address (frameOffset := 760) (offset := 16) state.rsp (by decide) (by decide), Nat.reduceSub, BitVec.ofNat_eq_ofNat] using h
  obtain ⟨m,u,runU,readyU,_,effectU⟩ := value_correct boundary pre.outerBoundary a
    (readyToStep frameA.machine frameA.bindingsSupported)
    (programText_slice (programLoaded_codeIn frameA.loaded) 0x10283 valueBytes
      (by decide) (by decide +kernel))
    ⟨effectA.rip, stack_readable pre.toCalleePre frameA (by decide) (by decide)⟩
  have memory := effectU.agrees.external (by simp [valueEffect,Effect.components,Component.Covers])
  have frameU := frameA.after_registers readyU effectU.agrees
    (by simp [valueEffect,Effect.components,Component.Covers]) (by simp [valueEffect,Effect.components])
  have value : flagValue a = infinityFlag point := by
    unfold flagValue
    rw [lowA]
    have address : stackPtr a + 80 = stackPtr s - 744 + 64 := by
      rw [frameA.rsp]
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [address]
    cases point with
    | none => simp [infinityFlag]
    | some p =>
      cases p with
      | infinity => rw [P256.Proofs.Common.Memory.memLoad8_of_byte sourceA.1.2.2]; decide +kernel
      | affine x y =>
        rw [P256.Proofs.Common.Memory.memLoad8_of_byte sourceA.1.2.2]
        change (((0 : BitVec 8) ^^^ 1) &&& -1) ^^^ 1 = 0
        decide +kernel
  refine ⟨n+m,u,runA.trans runU,frameU,effectU.rip,?_,?_,?_,?_,?_,?_,?_⟩
  · exact ((effectA.agrees.trans effectU.agrees).read (n := 64) (r := 3)
      (by simp [maskEffect,valueEffect,Effect.components])).trans state.output
  · apply state.x.of_bytes_eq
    intro i hi
    rw [memory]
    have h := mask_preserves effectA (offset := 280) (len := 32) (by decide) (by decide) i hi
    simpa only [scalar_stack_address (frameOffset := 760) (offset := 280) state.rsp (by decide) (by decide), Nat.reduceSub, BitVec.ofNat_eq_ofNat] using h
  · apply state.y.of_bytes_eq
    intro i hi
    rw [memory]
    have h := mask_preserves effectA (offset := 312) (len := 32) (by decide) (by decide) i hi
    simpa only [scalar_stack_address (frameOffset := 760) (offset := 312) state.rsp (by decide) (by decide), Nat.reduceSub, BitVec.ofNat_eq_ofNat] using h
  · exact ((effectA.agrees.trans effectU.agrees).read (n := 64) (r := 13)
      (by simp [maskEffect,valueEffect,Effect.components])).trans state.zero
  · exact (congrArg (BitVec.setWidth 8) ((effectA.agrees.trans effectU.agrees).read
      (n := 64) (r := 5) (by simp [maskEffect,valueEffect,Effect.components]))).trans state.choice
  · have h : u.regValue .r14 = mergeGPR 8 (flagValue a)
        ((memLoad a.external (stackPtr a + 80) 8).setWidth 64) := effectU.writes
    rw [h, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8, value]
  · rw [memory]
    have h : memLoad a.external (stackPtr t + 12) 8 = -(t.regValue .rbp).setWidth 8 := effectA.writes.1
    have address : stackPtr t + 12 = stackPtr s - 748 := by
      rw [state.rsp]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [address, state.choice] at h
    exact h

end P256.Proofs.Sec1.Affine.Compact.Flags
