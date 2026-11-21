import P256.Proofs.Verifying.Wrapper.KeyResult
import P256.Proofs.Verifying.Wrapper.SignatureCall
import P256.Proofs.Verifying.Wrapper.SignatureTag
import P256.Proofs.Verifying.Wrapper.CalleeReturn
import P256.Proofs.SignatureFromDer.Fixed.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC
open SecretKeyFromBytes.Scalar (Nat256At)

structure SignatureDecoded [Bindings] (initial s : RamState) (point : Curve.Point) (r scalarS : Nat) : Prop
    extends ReturnState initial s where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  frame : MemoryWriteFrame initial s (wrapperRegions verifyingKeyVerify initial)
  rip : s.RIP = 0x10314b
  output : s.regValue .r12 = initial.regValue .rcx
  capacity : s.regValue .r13 = initial.regValue .r8
  pointers : s.regValue .r14 = initial.regValue .rdi
  lengths : s.regValue .rbx = initial.regValue .rdx
  count : s.regValue .r15 = 3
  pointAt : Sec1.AffineAt s (stackPtr initial-112) point
  rAt : Nat256At s (stackPtr initial-200) r
  sAt : Nat256At s (stackPtr initial-168) scalarS

theorem decode_signature [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input} {point : Curve.Point} {r scalarS : Nat}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : AffineReady initial s point) (outside : ¬ InProgram (returnBoundary initial).rip)
    (decoded : Ecdsa.decodeSignature signature = some (r,scalarS)) :
    ∃ v, SignatureDecoded initial v point r scalarS := by
  obtain ⟨na,a,runA,stateA,ripA,inputA,lengthA,_,agA⟩ := signature_read call state.toReturnState
    state.frame outside state.rip state.count state.pointers state.lengths
  have frameA : MemoryWriteFrame initial a (wrapperRegions verifyingKeyVerify initial) := by
    intro address away
    rw [agA.external (by simp [Component.Covers])]
    exact state.frame address away
  obtain ⟨t,pre,length,bytes,output,sp,ret,agT,nt,runT⟩ :=
    enter_signature_decoder call stateA frameA outside ripA inputA lengthA
  obtain ⟨u,callee,result⟩ := SignatureFromDer.Fixed.signature_decode_correct pre length bytes
  have frameAT : MemoryWriteFrame a t #v[workRegion initial] := by
    apply agT.memoryWriteFrame
    intro c hc address covered
    simp only [signatureCallComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    exact ⟨workRegion initial,by simp,work_contains call.stackAvailable.1
      (by decide) (by decide) covered⟩
  have frameTU := callee.stack_frame (savedBytes := 40) call.stackAvailable.1 sp output
    (by decide) (by decide) (by decide) (by decide)
  have stateU := stateA.after_callee call.stackAvailable.1 agT frameAT
    (by simp [signatureCallComponents]) sp callee frameTU
  have pointA : Sec1.AffineAt a (stackPtr initial-112) point := state.pointAt.of_bytes_eq
    (by intro i hi; rw [agA.external (by simp [Component.Covers])])
  have pointT : Sec1.AffineAt t (stackPtr initial-112) point := by
    apply pointA.of_bytes_eq
    intro i hi
    apply agT.byte
    intro c hc covered
    simp only [signatureCallComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j,hj,he⟩ := covered
    exact stack_sub_apart (a := 288) (b := 112) (na := 8) (nb := 65)
      call.stackAvailable.1 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide)) j hj i hi he.symm
  have pointU : Sec1.AffineAt u (stackPtr initial-112) point := by
    apply pointT.of_bytes_eq
    intro i hi
    exact callee.stack_byte call.stackAvailable.1 (frameOffset := 280) sp output
      (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)) hi
  have values : loadBytes u.external (stackPtr initial-208) 8 = .ok (0 : BitVec 64) ∧
      Nat256At u (stackPtr initial-200) r ∧ Nat256At u (stackPtr initial-168) scalarS := by
    simp only [SignatureFromDer.Fixed.ResultAt,decoded,output] at result
    have addrR : stackPtr initial-208+8 = stackPtr initial-200 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    have addrS : stackPtr initial-208+40 = stackPtr initial-168 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    simpa only [addrR,addrS] using result
  obtain ⟨v,runV,stateV,ripV,memoryV,agV⟩ := signature_tag_branch stateU call.stackAvailable.1
    outside (callee.rip.trans ret) values.1
  obtain ⟨nf,first⟩ := state.execution
  obtain ⟨nc,inner⟩ := callee.execution
  have frameU := memoryWriteFrame_trans
    (memoryWriteFrame_trans frameA (work_frame call.stackAvailable.1 frameAT))
    (work_frame call.stackAvailable.1 frameTU)
  refine ⟨v,stateV,⟨_,(((first.trans runA).trans runT).trans inner).trans runV⟩,?_,ripV,
    ?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro address away
    rw [memoryV]
    exact frameU address away
  · exact (agV.read (n := 64) (r := 12) (by simp)).trans
      ((callee.calleeSaved .r12 (by simp)).trans
        (((agA.trans agT).read (n := 64) (r := 12) (by simp [signatureCallComponents])).trans state.output))
  · exact (agV.read (n := 64) (r := 13) (by simp)).trans
      ((callee.calleeSaved .r13 (by simp)).trans
        (((agA.trans agT).read (n := 64) (r := 13) (by simp [signatureCallComponents])).trans state.capacity))
  · exact (agV.read (n := 64) (r := 14) (by simp)).trans
      ((callee.calleeSaved .r14 (by simp)).trans
        (((agA.trans agT).read (n := 64) (r := 14) (by simp [signatureCallComponents])).trans state.pointers))
  · exact (agV.read (n := 64) (r := 3) (by simp)).trans
      ((callee.calleeSaved .rbx (by simp)).trans
        (((agA.trans agT).read (n := 64) (r := 3) (by simp [signatureCallComponents])).trans state.lengths))
  · exact (agV.read (n := 64) (r := 15) (by simp)).trans
      ((callee.calleeSaved .r15 (by simp)).trans
        (((agA.trans agT).read (n := 64) (r := 15) (by simp [signatureCallComponents])).trans state.count))
  · exact pointU.of_bytes_eq (by intro i hi; rw [memoryV])
  · simpa only [Nat256At,memoryV] using values.2.1
  · simpa only [Nat256At,memoryV] using values.2.2

end P256.Proofs.Verifying.Wrapper
