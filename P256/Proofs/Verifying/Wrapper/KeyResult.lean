import P256.Proofs.Verifying.Wrapper.KeyReturn
import P256.Proofs.Verifying.Wrapper.PrepareAffine

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC

structure AffineReady [Bindings] (initial s : RamState) (point : Curve.Point) : Prop
    extends ReturnState initial s where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  frame : MemoryWriteFrame initial s (wrapperRegions verifyingKeyVerify initial)
  rip : s.RIP = 0x103118
  output : s.regValue .r12 = initial.regValue .rcx
  capacity : s.regValue .r13 = initial.regValue .r8
  pointers : s.regValue .r14 = initial.regValue .rdi
  lengths : s.regValue .rbx = initial.regValue .rdx
  count : s.regValue .r15 = 3
  pointAt : Sec1.AffineAt s (stackPtr initial-112) point

theorem key_result [Bindings] {initial s t u : RamState} {key signature message : ByteArray}
    {slices : Array Input} {point : Curve.Point}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : KeyCopied initial s key) (outside : ¬ InProgram (returnBoundary initial).rip)
    (decoded : Points.decodePublicKey key = some point)
    (output : t.regValue .rdi = stackPtr initial-208) (sp : stackPtr t = stackPtr initial-288)
    (ret : (returnBoundary t).rip = 0x1030f8)
    (ag : AgreesExcept (keyCallComponents initial) s t)
    (execution : ∃ fuel, Advances (returnBoundary initial) fuel initial t)
    (callee : CalleeResult t u (returnBoundary initial) 80 3680)
    (result : Sec1.PublicKeyResultAt u (t.regValue .rdi) (Points.decodePublicKey key)) :
    ∃ v, AffineReady initial v point := by
  have stateU := state.toReturnState.after_key_result call ag sp output callee
  have frameTU := callee.stack_frame (savedBytes := 40) call.stackAvailable.1 sp output
    (by decide) (by decide) (by decide) (by decide)
  have frameU := memoryWriteFrame_trans (memoryWriteFrame_trans state.frame (key_call_frame call ag))
    (work_frame call.stackAvailable.1 frameTU)
  have ripU : u.RIP = 0x1030f8 := callee.rip.trans ret
  have tag : memLoad u.external (stackPtr initial-208) 64 = 0 ∧
      Sec1.AffineAt u (stackPtr initial-200) point := by
    rw [decoded,output] at result
    cases point with
    | infinity => exact result.elim
    | affine x y =>
      refine ⟨result.1,?_⟩
      have address : stackPtr initial-208+8 = stackPtr initial-200 := by
        simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
        rfl
      simpa only [Sec1.PublicKeyResultAt,address] using result.2
  obtain ⟨fuel,v,run,stateV,ripV,pointV,agV,frameUV⟩ :=
    prepare_affine call stateU outside ripU tag.1 tag.2
  obtain ⟨nf,first⟩ := execution
  obtain ⟨nc,inner⟩ := callee.execution
  refine ⟨v,stateV,⟨nf+nc+fuel,(first.trans inner).trans run⟩,
    memoryWriteFrame_trans frameU (work_frame call.stackAvailable.1 frameUV),ripV,
    ?_,?_,?_,?_,?_,pointV⟩
  · exact (agV.read (n := 64) (r := 12) (by simp)).trans
      ((callee.calleeSaved .r12 (by simp)).trans
        ((ag.read (n := 64) (r := 12) (by simp [keyCallComponents])).trans state.output))
  · exact (agV.read (n := 64) (r := 13) (by simp)).trans
      ((callee.calleeSaved .r13 (by simp)).trans
        ((ag.read (n := 64) (r := 13) (by simp [keyCallComponents])).trans state.capacity))
  · exact (agV.read (n := 64) (r := 14) (by simp)).trans
      ((callee.calleeSaved .r14 (by simp)).trans
        ((ag.read (n := 64) (r := 14) (by simp [keyCallComponents])).trans state.pointers))
  · exact (agV.read (n := 64) (r := 3) (by simp)).trans
      ((callee.calleeSaved .rbx (by simp)).trans
        ((ag.read (n := 64) (r := 3) (by simp [keyCallComponents])).trans state.lengths))
  · exact (agV.read (n := 64) (r := 15) (by simp)).trans
      ((callee.calleeSaved .r15 (by simp)).trans
        ((ag.read (n := 64) (r := 15) (by simp [keyCallComponents])).trans state.count))

end P256.Proofs.Verifying.Wrapper
