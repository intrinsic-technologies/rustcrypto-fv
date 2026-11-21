import P256.Proofs.Sec1.Affine.Compact.Normalize.State
import P256.Proofs.Sec1.Affine.Compact.Normalize.Arguments
import P256.Proofs.Sec1.Affine.Compact.Compare
import P256.Proofs.Sec1.Affine.Compact.Finish.State
import P256.Proofs.PublicPoint.Normalize.Invert.SelectCall
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Normalize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC
open ScalarFrame FieldCall

def minimumSite : BinaryCallSite 3360 760 0x114380 128 where
  codeOffset := 0x104fb
  disp := 0x3e80
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := ⟨768,632,88,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  stack := rfl
  outputSaved := by decide
  rightOffset := 560
  rightAbove := by decide
  rightEnd := by decide
  rightApart := by decide

theorem select_minimum [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : Decoded s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Finish.Prepared s u point := by
  obtain ⟨n,a,runA,frameA,ripA,choice,savedA,keptA,_⟩ := Compare.compare_correct
    pre state.toFrameState state.rip state.canonicalNegative state.canonicalY state.zero
  have yA : Field.MontgomeryAt a (stackPtr s-632) (Select.yCoordinate point) :=
    state.y.of_bytes_eq (keptA 632 32 (by decide) (by decide) (Or.inr (by decide)))
  have negativeA : Field.MontgomeryAt a (stackPtr s-560) (Spec.Points.negElement (Select.yCoordinate point)) :=
    state.negative.of_bytes_eq (keptA 560 32 (by decide) (by decide) (Or.inr (by decide)))
  obtain ⟨m,v,runV,readyV,_,effect⟩ := minimum_setup boundary pre.outerBoundary a
    (readyToStep frameA.machine frameA.bindingsSupported)
    (programText_slice (programLoaded_codeIn frameA.loaded) 0x104ea minimumBytes
      (by decide) (by decide +kernel)) ripA
  have agrees : AgreesExcept [.reg 7,.reg 1,.reg 6,.reg 2,.rip] a v := effect.agrees
  have frameV := frameA.after_registers readyV agrees (by simp [Component.Covers]) (by simp)
  have memory := agrees.external (by simp [Component.Covers])
  have values := effect.writes
  change v.regValue .rdi = stackPtr a+672 ∧
    v.regValue .rcx = ((a.regValue .rax).setWidth 8).setWidth 64 ∧
    v.regValue .rsi = a.regValue .r12 ∧ v.regValue .rdx = a.regValue .r15 at values
  let smaller := decide (Spec.Points.negElement (Select.yCoordinate point) < Select.yCoordinate point)
  have flag : (v.regValue .rcx).setWidth 8 = if smaller then 1 else 0 := by
    rw [values.2.1,BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),BitVec.setWidth_eq,choice]
    by_cases h : Spec.Points.negElement (Select.yCoordinate point) < Select.yCoordinate point
    · simp [smaller,h]
    · simp [smaller,h]
  obtain ⟨k,u,runU,frameU,ripU,value,savedU,keptU,_⟩ := PublicPoint.Normalize.select_binary_call
    (op := fun x y => if smaller then y else x) pre.toCalleePre frameV minimumSite
    (fun v hp hc hx hy => Projective.Multiply.Machine.Lookup.Select.field_select_low8_correct hp hx hy
      ((congrArg (BitVec.setWidth 8) hc).trans flag))
    effect.rip (values.2.2.1.trans ((savedA .r12 (by simp)).trans state.r12))
    (values.2.2.2.trans ((savedA .r15 (by simp)).trans state.r15))
    (values.1.trans (scalar_stack_address (frameOffset := 760) frameA.rsp (by decide) (by decide)))
    (yA.of_bytes_eq (fun i hi => by rw [memory]; rfl))
    (negativeA.of_bytes_eq (fun i hi => by rw [memory]; rfl))
  refine ⟨n+m+k,u,(runA.trans runV).trans runU,frameU,ripU,?_,?_,?_,?_,?_,?_⟩
  · exact (savedU .rbx (by simp)).trans ((agrees.read (n := 64) (r := 3) (by simp)).trans
      ((savedA .rbx (by simp)).trans state.output))
  · apply state.x.of_bytes_eq
    intro i hi
    exact (keptU 480 32 (by decide) (by decide) (Or.inr (by decide)) i hi).trans
      ((by rw [memory] : v.external[stackPtr s-480+BitVec.ofNat 64 i]? =
        a.external[stackPtr s-480+BitVec.ofNat 64 i]?).trans
        (keptA 480 32 (by decide) (by decide) (Or.inl (by decide)) i hi))
  · simpa only [Spec.Points.compactY,smaller,decide_eq_true_eq,minimumSite,BitVec.ofNat_eq_ofNat] using value
  · exact (congrArg (BitVec.setWidth 8) ((savedU .rbp (by simp)).trans
      ((agrees.read (n := 64) (r := 5) (by simp)).trans (savedA .rbp (by simp))))).trans state.choice
  · exact (congrArg (BitVec.setWidth 8) ((savedU .r14 (by simp)).trans
      ((agrees.read (n := 64) (r := 14) (by simp)).trans (savedA .r14 (by simp))))).trans state.infinity
  · apply Eq.trans _ state.mask
    apply memLoad_congr
    intro i hi
    have hU := keptU 748 1 (by decide) (by decide) (Or.inr (by decide)) i hi
    have hA := keptA 748 1 (by decide) (by decide) (Or.inr (by decide)) i hi
    have hv : v.external[stackPtr s-BitVec.ofNat 64 748+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-BitVec.ofNat 64 748+BitVec.ofNat 64 i]? := by
      simpa only [memory] using hA
    change (u.external[stackPtr s-748+BitVec.ofNat 64 i]?).getD 0 =
      (t.external[stackPtr s-748+BitVec.ofNat 64 i]?).getD 0
    simpa only [BitVec.ofNat_eq_ofNat] using congrArg (fun v : Option UInt8 => v.getD 0) (hU.trans hv)

end P256.Proofs.Sec1.Affine.Compact.Normalize
