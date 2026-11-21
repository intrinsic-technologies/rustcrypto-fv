import P256.Proofs.Verifying.Wrapper.SignatureResult
import P256.Proofs.Verifying.Wrapper.SignatureCopy.Run

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC
open SecretKeyFromBytes.Scalar

structure SignatureReady [Bindings] (initial s : RamState) (point : Curve.Point) (r scalarS : Nat) : Prop
    extends ReturnState initial s where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  frame : MemoryWriteFrame initial s (wrapperRegions verifyingKeyVerify initial)
  rip : s.RIP = 0x1031a0
  output : s.regValue .r12 = initial.regValue .rcx
  capacity : s.regValue .r13 = initial.regValue .r8
  pointers : s.regValue .r14 = initial.regValue .rdi
  lengths : s.regValue .rbx = initial.regValue .rdx
  count : s.regValue .r15 = 3
  pointAt : Sec1.AffineAt s (stackPtr initial-112) point
  rAt : Nat256At s (stackPtr initial-280) r
  sAt : Nat256At s (stackPtr initial-248) scalarS

theorem copy_signature [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input} {point : Curve.Point} {r scalarS : Nat}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : SignatureDecoded initial s point r scalarS)
    (outside : ¬ InProgram (returnBoundary initial).rip) :
    ∃ u, SignatureReady initial u point r scalarS := by
  obtain ⟨fuel,u,run,su,rip,ag,words⟩ :=
    SignatureCopy.copy_correct call state.toReturnState outside state.rip
  have sp : stackPtr u = stackPtr s := ag.read (n := 64) (r := 4)
    (by simp [SignatureCopy.components])
  have frame : MemoryWriteFrame s u #v[workRegion initial] := by
    apply ag.memoryWriteFrame
    intro c hc a covered
    simp only [SignatureCopy.components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    rw [state.rsp] at covered
    exact ⟨workRegion initial,by simp,work_contains call.stackAvailable.1
      (by decide) (by decide) covered⟩
  have copyNat {x : Nat} (q : Nat) (bound : q < 2)
      (value : Nat256At s (stackPtr s+BitVec.ofNat 64 (80+32*q)) x) :
      Nat256At u (stackPtr s+BitVec.ofNat 64 (32*q)) x := by
    apply nat256At_of_memLoad_limbs value.1
    · have readable := su.local_readable call.stackAvailable.1
        (offset := 32*q) (len := 32) (by omega)
      rw [sp] at readable
      exact readable.mem
    · intro j hj
      have copied := words (4*q+j) (by omega)
      have source := value.memLoad_limb j hj
      have dst : 8*(4*q+j) = 32*q+8*j := by omega
      rw [dst] at copied
      simp only [BitVec.ofNat_add,BitVec.add_assoc] at copied source ⊢
      exact copied.trans source
  have r0 : Nat256At u (stackPtr initial-280) r := by
    have src : stackPtr s+BitVec.ofNat 64 (80+32*0) = stackPtr initial-200 := by
      rw [state.rsp]
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    have dst : stackPtr s+BitVec.ofNat 64 (32*0) = stackPtr initial-280 := by
      rw [state.rsp,BitVec.add_zero]
    simpa only [dst] using copyNat 0 (by decide) (src.symm ▸ state.rAt)
  have s0 : Nat256At u (stackPtr initial-248) scalarS := by
    have src : stackPtr s+BitVec.ofNat 64 (80+32*1) = stackPtr initial-168 := by
      rw [state.rsp]
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    have dst : stackPtr s+BitVec.ofNat 64 (32*1) = stackPtr initial-248 := by
      rw [state.rsp]
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    simpa only [dst] using copyNat 1 (by decide) (src.symm ▸ state.sAt)
  obtain ⟨nf,first⟩ := state.execution
  refine ⟨u,su,⟨nf+fuel,first.trans run⟩,
    memoryWriteFrame_trans state.frame (work_frame call.stackAvailable.1 frame),rip,
    ?_,?_,?_,?_,?_,?_,r0,s0⟩
  · exact (ag.read (n := 64) (r := 12) (by simp [SignatureCopy.components])).trans state.output
  · exact (ag.read (n := 64) (r := 13) (by simp [SignatureCopy.components])).trans state.capacity
  · exact (ag.read (n := 64) (r := 14) (by simp [SignatureCopy.components])).trans state.pointers
  · exact (ag.read (n := 64) (r := 3) (by simp [SignatureCopy.components])).trans state.lengths
  · exact (ag.read (n := 64) (r := 15) (by simp [SignatureCopy.components])).trans state.count
  · apply state.pointAt.of_bytes_eq
    intro i hi
    apply ag.byte
    intro c hc covered
    simp only [SignatureCopy.components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    rw [state.rsp] at covered
    obtain ⟨j,hj,he⟩ := covered
    exact stack_sub_apart (a := 280) (b := 112) (na := 64) (nb := 65)
      call.stackAvailable.1 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide)) j hj i hi he.symm

end P256.Proofs.Verifying.Wrapper
