import P256.Proofs.Signing.Wrapper.Entry.Construct.Execute
import P256.Proofs.Signing.Wrapper.Entry.Construct.Preserve

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Construct

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar

theorem prepare_tail [Bindings] {initial s : RamState} {secret message : ByteArray} {d : Nat}
    (ctx : Context initial secret message) (state : State initial s 520)
    (rip : s.RIP=0x102677) (scalar : Nat256At s (stackPtr s+64) d) :
    ∃ fuel c, Advances (returnBoundary initial) fuel s c ∧ State initial c 520 ∧
      c.RIP=0x1026f1 ∧ Nat256At c (stackPtr c+64) d ∧
      c.regValue .rax=BitVec.ofNat 64 d ∧
      c.regValue .rsi=stackPtr initial-448#64 ∧
      c.regValue .rdi=stackPtr initial-144#64 ∧ c.regValue .rcx=12 ∧
      (∀ r ∈ [Syntax.Reg.r12,.r13,.r15],c.regValue r=s.regValue r) ∧
      (∀ off : Nat, 312 ≤ off → off+8 ≤ 336 →
        memLoad c.external (stackPtr s+BitVec.ofNat 64 off) 64 =
          memLoad s.external (stackPtr s+BitVec.ofNat 64 off) 64) := by
  obtain ⟨na,a,runA,sa,ea⟩ := clear ctx state rip
  obtain ⟨nb,b,runB,sb,eb⟩ := clearcopy ctx sa ea.rip
  obtain ⟨nc,c,runC,sc,ec⟩ := reparguments ctx sb eb.rip
  have spa : stackPtr a=stackPtr s := sa.rsp.trans state.rsp.symm
  have spb : stackPtr b=stackPtr s := sb.rsp.trans state.rsp.symm
  have spc : stackPtr c=stackPtr s := sc.rsp.trans state.rsp.symm
  have scalarA : Nat256At a (stackPtr a+64) d := by
    rw [spa]
    exact ⟨scalar.1,fun i hi => (clear_bytes ea hi).trans (scalar.2 i hi)⟩
  have scalarB : Nat256At b (stackPtr b+64) d := by
    rw [spb,← spa]
    exact ⟨scalarA.1,fun i hi => (clearcopy_bytes eb hi).trans (scalarA.2 i hi)⟩
  have scalarC : Nat256At c (stackPtr c+64) d := by
    rw [spc,← spb]
    exact ⟨scalarB.1,fun i hi => (reparguments_bytes ec hi).trans (scalarB.2 i hi)⟩
  have src : c.regValue .rsi=stackPtr initial-448#64 := by
    have h : a.regValue .rsi=stackPtr s+72 := ea.writes.1
    have h2 : b.regValue .rsi=a.regValue .rsi := eb.agrees.read (n := 64) (r := 6) (by simp [ClearCopy.effect,Effect.components])
    have h3 : c.regValue .rsi=b.regValue .rsi := ec.agrees.read (n := 64) (r := 6) (by simp [RepArguments.effect,Effect.components])
    exact h3.trans (h2.trans (h.trans (address state (by decide))))
  have dst : c.regValue .rdi=stackPtr initial-144#64 :=
    (show c.regValue .rdi=stackPtr b+376 from ec.writes.2.1).trans (address sb (by decide))
  have word : c.regValue .rax=BitVec.ofNat 64 d := by
    have h : c.regValue .rax=memLoad b.external (stackPtr b+64) 64 := ec.writes.1
    have hb := scalarB.memLoad_limb 0 (by decide)
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.div_one,BitVec.add_zero] at hb
    exact h.trans hb
  refine ⟨na+nb+nc,c,(runA.trans runB).trans runC,sc,ec.rip,scalarC,word,src,dst,ec.writes.2.2,?_,?_⟩
  · have ag := (ea.agrees.trans eb.agrees).trans ec.agrees
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ag.read (n := 64) (r := 12) (by simp [Clear.effect,ClearCopy.effect,RepArguments.effect,Effect.components])
    · exact ag.read (n := 64) (r := 13) (by simp [Clear.effect,ClearCopy.effect,RepArguments.effect,Effect.components])
    · exact ag.read (n := 64) (r := 15) (by simp [Clear.effect,ClearCopy.effect,RepArguments.effect,Effect.components])

  · intro off low high
    have ag := (ea.agrees.trans eb.agrees).trans ec.agrees
    apply memLoad_agrees_apart ag
    intro addr len member
    simp only [Clear.effect,ClearCopy.effect,RepArguments.effect,Effect.components,
      Write.component,Operand.component,List.map_cons,List.map_nil,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,false_or,or_assoc,Component.mem.injEq,
      reduceCtorEq] at member
    rcases member with h|h|h|h|h|h|h|h
    all_goals obtain ⟨rfl,rfl⟩ := h
    all_goals
      intro i hi j hj eq
      change stackPtr _ + _ + _ = stackPtr s + _ + _ at eq
      try rw [spa] at eq
      rw [BitVec.add_assoc,BitVec.add_assoc] at eq
      have en := congrArg BitVec.toNat ((BitVec.add_right_inj (stackPtr s)).mp eq)
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat,BitVec.reduceToNat] at en
      omega

end P256.Proofs.Signing.Wrapper.Entry.Construct
