import P256.Proofs.Ecdh.Normalize.Finish.State
import P256.Proofs.Ecdh.Normalize.Finish.SelectSetup
import P256.Proofs.PublicPoint.Normalize.Invert.SelectCall
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Operations Standards.SECG.ECC Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Program.FieldCall

def firstSite : BinaryCallSite 3464 2056 0x114380 128 where
  codeOffset := 0x4c5
  disp := 0x13eb6
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨2064,1808,1976,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 1040
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

def secondSite : BinaryCallSite 3464 2056 0x114380 128 where
  codeOffset := 0x4e1
  disp := 0x13e9a
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨2064,1776,1944,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 1008
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

structure XSelected [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (point : Projective) : Prop extends FrameState s t 32 3464 2056 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x1004ca
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (stackPtr s - 1976)
    (if decide (point.z ≠ 0) then point.x * Curve.inverse domain.p point.z % domain.p else 0)
  y : Field.MontgomeryAt t (stackPtr s - 1008)
    (point.y * Curve.inverse domain.p point.z % domain.p)
  zeroY : Field.MontgomeryAt t (stackPtr s - 1776) 0
  choice : (t.regValue .rbp).setWidth 8 = if point.z = 0 then 0 else 1

theorem select_x [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : Prepared s t boundary point) : ∃ u, XSelected s u boundary point := by
  obtain ⟨n,v,run,ready,_,effect⟩ := select_first_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x4bb selectFirstBytes
      (by decide) (by decide +kernel)) state.rip
  have memory := effect.agrees.external (by simp [selectFirstEffect, Effect.components, Component.Covers])
  have frame := state.toFrameState.after_registers ready effect.agrees
    (by simp [selectFirstEffect, Effect.components, Component.Covers])
    (by simp [selectFirstEffect, Effect.components])
  have values := effect.writes
  simp only [selectFirstEffect, Write.AllHold] at values
  have flag := select_flag state.choice values.2.2
  have choice : (v.regValue .rcx).setWidth 8 = if decide (point.z ≠ 0) then 1 else 0 := by
    by_cases hz : point.z = 0 <;> simpa [hz] using flag
  obtain ⟨m,u,called,finished,rip,value,saved,bytes,_⟩ := PublicPoint.Normalize.select_binary_call
    (op := fun x y => if decide (point.z ≠ 0) then y else x)
    pre frame firstSite
    (fun w hp hc hx hy => Projective.Multiply.Machine.Lookup.Select.field_select_low8_correct hp hx hy
      ((congrArg (BitVec.setWidth 8) hc).trans choice))
    effect.rip (values.2.1.trans state.rax)
    ((effect.agrees.read (n := 64) (r := 2) (by simp [selectFirstEffect, Effect.components])).trans state.rdx)
    (values.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
    (state.zeroX.of_bytes_eq (by intro i hi; rw [memory]; rfl))
    (state.x.of_bytes_eq (by intro i hi; rw [memory]; rfl))
  refine ⟨u,finished,?_,rip,?_,value,?_,?_,?_⟩
  · obtain ⟨fuel,previous⟩ := state.execution
    exact ⟨fuel+n+m,(previous.trans run).trans called⟩
  · exact (saved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp [selectFirstEffect, Effect.components])).trans state.output)
  · apply state.y.of_bytes_eq
    intro i hi
    exact (bytes 1008 32 (by decide) (by decide) (Or.inl (by decide)) i hi).trans
      (by rw [memory]; rfl)
  · apply state.zeroY.of_bytes_eq
    intro i hi
    exact (bytes 1776 32 (by decide) (by decide) (Or.inl (by decide)) i hi).trans
      (by rw [memory]; rfl)
  · exact (congrArg (BitVec.setWidth 8) ((saved .rbp (by simp)).trans
      (effect.agrees.read (n := 64) (r := 5) (by simp [selectFirstEffect, Effect.components])))).trans state.choice

theorem select_y [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : XSelected s t boundary point) :
    ∃ u, Selected s u boundary
      (if decide (point.z ≠ 0) then point.x * Curve.inverse domain.p point.z % domain.p else 0) := by
  obtain ⟨n,v,run,ready,_,effect⟩ := select_second_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x4ca selectSecondBytes
      (by decide) (by decide +kernel)) state.rip
  have memory := effect.agrees.external (by simp [selectSecondEffect, Effect.components, Component.Covers])
  have frame := state.toFrameState.after_registers ready effect.agrees
    (by simp [selectSecondEffect, Effect.components, Component.Covers])
    (by simp [selectSecondEffect, Effect.components])
  have values := effect.writes
  simp only [selectSecondEffect, Write.AllHold] at values
  have flag := select_flag state.choice values.2.2.2
  have choice : (v.regValue .rcx).setWidth 8 = if decide (point.z ≠ 0) then 1 else 0 := by
    by_cases hz : point.z = 0 <;> simpa [hz] using flag
  obtain ⟨m,u,called,finished,rip,_,saved,bytes,_⟩ := PublicPoint.Normalize.select_binary_call
    (op := fun x y => if decide (point.z ≠ 0) then y else x)
    pre frame secondSite
    (fun w hp hc hx hy => Projective.Multiply.Machine.Lookup.Select.field_select_low8_correct hp hx hy
      ((congrArg (BitVec.setWidth 8) hc).trans choice))
    effect.rip
    (values.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
    (values.2.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
    (values.2.2.1.trans (scalar_stack_address state.rsp (by decide) (by decide)))
    (state.zeroY.of_bytes_eq (by intro i hi; rw [memory]; rfl))
    (state.y.of_bytes_eq (by intro i hi; rw [memory]; rfl))
  refine ⟨u,finished,?_,rip,?_,?_⟩
  · obtain ⟨fuel,previous⟩ := state.execution
    exact ⟨fuel+n+m,(previous.trans run).trans called⟩
  · exact (saved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp [selectSecondEffect, Effect.components])).trans state.output)
  · apply state.x.of_bytes_eq
    intro i hi
    exact (bytes 1976 32 (by decide) (by decide) (Or.inr (by decide)) i hi).trans
      (by rw [memory]; rfl)

theorem select [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : Prepared s t boundary point) :
    ∃ u, Selected s u boundary
      (if decide (point.z ≠ 0) then point.x * Curve.inverse domain.p point.z % domain.p else 0) := by
  obtain ⟨u, selected⟩ := select_x pre state
  exact select_y pre selected

theorem selected_xBytes (point : Projective) :
    Encoding.natToOctets 32
      (if decide (point.z ≠ 0) then point.x * Curve.inverse domain.p point.z % domain.p else 0) =
      P256.Spec.Points.xBytes point.toAffine := by
  by_cases hz : point.z = 0 <;> simp [Projective.toAffine, P256.Spec.Points.xBytes, hz]

end P256.Proofs.Ecdh.Normalize.Finish
