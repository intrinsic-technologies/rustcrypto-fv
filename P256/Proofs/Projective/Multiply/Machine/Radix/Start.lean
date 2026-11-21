import P256.Proofs.Projective.Multiply.Machine.Radix.SerializeCall
import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles.Progress

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar (Nat256At)

theorem serialize_last {s t u : RamState}
    (ag : AgreesExcept (serializeComponents s) t u) :
    memLoad u.external (stackPtr s-48) 8 = memLoad t.external (stackPtr s-48) 8 := by
  have p : RangeApart (stackPtr s-128) 8 (stackPtr s-48) 1 := by
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd,
      BitVec.add_zero] using RangeApart.offsets (stackPtr s-128) (a := 0) (b := 80)
        (len := 8) (count := 1) (by decide) (by decide) (.inl (by decide))
  have q : RangeApart (stackPtr s-40) 32 (stackPtr s-48) 1 := by
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd,
      BitVec.add_zero] using RangeApart.offsets (stackPtr s-48) (a := 8) (b := 0)
        (len := 32) (count := 1) (by decide) (by decide) (.inr (by decide))
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr s-48+BitVec.ofNat 64 i]?).getD 0 =
    (t.external[stackPtr s-48+BitVec.ofNat 64 i]?).getD 0
  rw [ag.memory]
  intro c hc covered
  simp only [serializeComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact covered.elim
  · obtain ⟨j,hj,eq⟩ := covered
    exact p j hj i hi eq.symm
  · obtain ⟨j,hj,eq⟩ := covered
    exact q j hj i hi eq.symm

theorem start_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136)
    (scalar : Nat256At s (s.regValue .rsi) d) :
    ∃ t fuel, Advances boundary fuel s t ∧ ExtractionState s t d 0 ∧
      t.RIP = 0x10b77f ∧ t.regValue .rbx = s.regValue .rdi := by
  obtain ⟨u,run,st,rip,out,source,_⟩ := prologue_correct pre
  obtain ⟨v,fuel,init,sv,ripv,effect⟩ := initialize_correct pre st rip
  have dest : v.regValue .rdi = stackPtr s-40 := by
    have h : v.regValue .rdi = stackPtr u+80 := effect.writes.1
    rw [h,st.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have src : v.regValue .rsi = s.regValue .rsi :=
    (effect.agrees.read (n := 64) (r := 6) (by simp [initializeEffect,Effect.components])).trans source
  obtain ⟨t,count,called,frame,ipt,bytes,ag⟩ := serialize_call pre sv scalar ripv src dest
  refine ⟨t,3+fuel+count,(run.trans init).trans called,⟨frame,bytes,?_,?_,?_⟩,ipt,?_⟩
  · intro i hi
    omega
  · have last : memLoad v.external (stackPtr u+72) 8 = 0 := effect.writes.2.2.2.2.2.2.2.2.2
    have address : stackPtr u+72 = stackPtr s-48 := by
      rw [st.rsp]
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    rw [address] at last
    exact (serialize_last ag).trans last
  · omega
  · exact ((effect.agrees.trans ag).read (n := 64) (r := 3)
      (by simp [initializeEffect,Effect.components,serializeComponents])).trans out

end P256.Proofs.Projective.Multiply.Machine.Radix
