import P256.Proofs.Verifying.Core.Finish.Tail.Encode
import P256.Proofs.Verifying.Core.Finish.Select
import P256.Proofs.Verifying.Core.Finish.CopyXRun
import P256.Proofs.Verifying.Core.Finish.CanonicalSetup
import P256.Proofs.Ecdh.Normalize.Conversion.Wrapper
import P256.Proofs.Program.FieldCall.Unary

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field
open SecretKeyFromBytes.Scalar (Nat256At)

def canonicalLayout : StackCallLayout 9992 32 32 40 :=
  ⟨1184,600,1048,by decide,by decide,by decide,by decide,by decide,by decide,Or.inr (by decide)⟩

theorem canonical_value [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x r : Nat} {nonzero : Bool} (pre : Core.Pre s boundary)
    (state : Selected s t x r nonzero) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ u.RIP = 0x10e04c ∧
      Nat256At u (frameBase s+128) (if nonzero then x else 0) ∧
      Nat256At u (frameBase s+704) r ∧ memLoad u.external (frameBase s+384) 64 = s.regValue .rdi := by
  obtain ⟨n,a,runA,frameA,ripA,xA,gA⟩ := CopyX.run pre state.toFrameState state.rip state.x
  obtain ⟨m,b,runB,frameB,eB,memB⟩ := CanonicalSetup.setup pre frameA ripA
  have source : b.regValue .rsi = stackPtr s-600 := by
    have h : b.regValue .rsi = stackPtr a+576 := eB.writes.2.2
    rw [h,frameA.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have dest : b.regValue .rdi = stackPtr s-1048 := by
    have h : b.regValue .rdi = stackPtr a+128 := eB.writes.1
    rw [h,frameA.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have xB : MontgomeryAt b (stackPtr s-600) (if nonzero then x else 0) :=
    xA.of_bytes_eq (fun _ _ => congrArg (fun e => e[_]?) memB)
  obtain ⟨k,u,runU,frameU,ripU,value,regs,bytes,_⟩ := FieldCall.unary_call
    (resultAt := fun u p => Nat256At u p (if nonzero then x else 0))
    pre.toCalleePre frameB canonicalLayout rfl (by decide)
    0xe047 0xffff9cb4 (by decide) (by decide +kernel) (by decide +kernel) (by decide)
    (inProgram_of_textOffset 0x7d00 (by decide))
    (fun _ cp hx => Ecdh.Normalize.Conversion.callee_correct cp hx)
    eB.rip source dest xB
  have addr : frameBase s+704 = stackPtr s-472#64 := by
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  have scalarA : Nat256At a (frameBase s+704) r := by
    refine ⟨state.scalar.1,fun i hi => ?_⟩
    rw [← state.scalar.2 i hi]
    apply gA.byte
    intro c hc ha
    simp only [Copy32.components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl <;> try exact ha.elim
    obtain ⟨j,hj,he⟩ := ha
    have outAddr : stackPtr s-600 = frameBase s+576 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [outAddr] at he
    exact RangeApart.offsets (frameBase s) (a := 576) (b := 704)
      (by decide) (by decide) (Or.inl (by decide)) j hj i hi he.symm
  refine ⟨n+m+k,u,(runA.trans runB).trans runU,frameU,ripU,?_,?_,?_⟩
  · simpa only [canonicalLayout,frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc,
      BitVec.reduceNeg,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using value
  · refine ⟨scalarA.1,fun i hi => ?_⟩
    rw [addr,bytes 472 32 (by decide) (by decide) (Or.inl (by decide)) i hi,memB,← addr]
    exact scalarA.2 i hi
  · apply Eq.trans _ state.output
    have pointerA : memLoad a.external (frameBase s+384) 64 = memLoad t.external (frameBase s+384) 64 := by
      apply memLoad_congr (n := 64)
      intro i hi
      change (a.external[_]?).getD 0 = (t.external[_]?).getD 0
      congr 1
      apply gA.byte
      intro c hc ha
      simp only [Copy32.components,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl <;> try exact ha.elim
      obtain ⟨j,hj,he⟩ := ha
      have outAddr : stackPtr s-600 = frameBase s+576 := by
        simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
      rw [outAddr] at he
      exact RangeApart.offsets (frameBase s) (a := 576) (b := 384)
        (by decide) (by decide) (Or.inr (by decide)) j hj i hi he.symm
    apply Eq.trans _ pointerA
    have addr : frameBase s+384 = stackPtr s-792#64 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [addr]
    apply memLoad_congr (n := 64)
    intro i hi
    change (u.external[_]?).getD 0 = (a.external[_]?).getD 0
    rw [bytes 792 8 (by decide) (by decide) (Or.inl (by decide)) i hi,memB]

theorem canonical [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x r : Nat} {nonzero : Bool} (pre : Core.Pre s boundary)
    (state : Selected s t x r nonzero) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ u.RIP = 0x10e098 ∧
      ((if nonzero then x else 0) < 2^256 ∧
        (⟨(frameBase s+392).toNat,32⟩ : MemoryRegion).HasBytes u.external
          (Standards.SECG.ECC.Encoding.natToOctets 32 (if nonzero then x else 0))) ∧
      Nat256At u (frameBase s+704) r ∧ memLoad u.external (frameBase s+384) 64 = s.regValue .rdi := by
  obtain ⟨n,a,runA,frameA,ripA,xA,rA,outA⟩ := canonical_value pre state
  obtain ⟨m,u,runU,frameU,ripU,outU,bytesU,rU⟩ := Tail.encode pre frameA ripA xA rA
  exact ⟨n+m,u,runA.trans runU,frameU,ripU,⟨xA.1,bytesU⟩,rU,outU.trans outA⟩

end P256.Proofs.Verifying.Core.Finish
