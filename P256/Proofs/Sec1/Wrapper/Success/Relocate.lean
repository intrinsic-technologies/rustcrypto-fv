import P256.Proofs.Sec1.Wrapper.Success.Copy
import P256.Proofs.Sec1.Wrapper.Success.Setup
import P256.Proofs.Sec1.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC

theorem relocate [Bindings] {initial s : RamState} {input : ByteArray} {slices : Array Input}
    {point : Curve.Point} (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (state : ReturnState initial s) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x10184b) (affine : Sec1.AffineAt s (stackPtr initial - 224) point) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReturnState initial t ∧
      t.RIP = 0x10186b ∧ t.regValue .rsi = stackPtr initial - 96 ∧
      t.regValue .rdi = stackPtr initial - 232 ∧ t.regValue .rdx = 0 ∧
      Sec1.AffineAt t (stackPtr initial - 96) point ∧
      AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 6,.reg 7,.flags,.rip,
        .mem (stackPtr initial - 96) 72] s t := by
  obtain ⟨n,a,ha,ra,_,ea⟩ := setup (returnBoundary initial) outside s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x184b setupBytes
      (by decide) (by decide +kernel)) rip
  have fa : AgreesExcept [.reg 6,.reg 0,.reg 1,.reg 7,.rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have sa := state.after_registers ra fa (by simp [Component.Covers]) (by simp) (by simp)
  have args : a.regValue .rsi = stackPtr s + 8 ∧ a.regValue .rax = stackPtr s + 136 ∧
      a.regValue .rcx = 9 ∧ a.regValue .rdi = stackPtr s + 136 := ea.writes
  have src : a.regValue .rsi = stackPtr initial - 224 := by
    rw [args.1,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have saved : a.regValue .rax = stackPtr initial - 96 := by
    rw [args.2.1,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have dst : a.regValue .rdi = stackPtr initial - 96 := args.2.2.2.trans args.2.1.symm |>.trans saved
  have avoids := (valid.separation.2 (callStack publicKeyFromSec1Bytes initial) (by simp)).2
  obtain ⟨b,hb,sb,ipb,fb,copied⟩ := stack_copy sa valid.stackAvailable.1 avoids outside
    (count := 9) (source := 224) (destination := 96) (codeOffset := 0x1860)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide +kernel) ea.rip src dst args.2.2.1
  have ab : Sec1.AffineAt b (stackPtr initial - 96) point :=
    affine.of_bytes_eq (fun i hi => (copied i (by omega)).trans (by rw [ma]; rfl))
  have ax : b.regValue .rax = stackPtr initial - 96 :=
    (fb.read (n := 64) (r := 0) (by simp [copyComponents])).trans saved
  obtain ⟨m,t,ht,rt,_,et⟩ := serializer_setup (returnBoundary initial) outside b
    (readyToStep sb.machine sb.bindingsSupported)
    (programText_slice (programLoaded_codeIn sb.loaded) 0x1863 serializerSetupBytes
      (by decide) (by decide +kernel)) ipb
  have ft : AgreesExcept [.reg 7,.reg 6,.reg 2,.flags,.rip] b t := et.agrees
  have mt := ft.external (by simp [Component.Covers])
  have ta : t.regValue .rdi = stackPtr b ∧ t.regValue .rsi = b.regValue .rax ∧
      t.regValue .rdx = 0 := et.writes
  exact ⟨_,t,(ha.trans hb).trans ht,
    sb.after_registers rt ft (by simp [Component.Covers]) (by simp) (by simp),
    et.rip,ta.2.1.trans ax,ta.1.trans sb.rsp,ta.2.2,
    ab.of_bytes_eq (fun _ _ => by rw [mt]),
    ((fa.trans fb).trans ft).mono (by simp [copyComponents])⟩

end P256.Proofs.Sec1.Wrapper.Success
