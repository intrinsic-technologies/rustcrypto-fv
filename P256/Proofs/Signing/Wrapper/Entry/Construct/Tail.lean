import P256.Proofs.Signing.Wrapper.Entry.Construct.PrepareTail
import P256.Proofs.Signing.Wrapper.Entry.Construct.Execute
import P256.Proofs.Signing.Wrapper.Entry.Construct.Preserve
import P256.Proofs.Signing.Wrapper.Entry.Construct.Rep
import P256.Proofs.Signing.Wrapper.Entry.Construct.Guards

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Construct

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar

theorem tail [Bindings] {initial s : RamState} {secret message : ByteArray} {d : Nat}
    (ctx : Context initial secret message) (state : State initial s 520)
    (rip : s.RIP=0x102677) (scalar : Nat256At s (stackPtr s+64) d)
    (count : s.regValue .r13=2) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ State initial t 520 ∧
      t.RIP=0x102706 ∧ Nat256At t (stackPtr initial-152) d ∧
      (∀ r ∈ [Syntax.Reg.r12,.r15],t.regValue r=s.regValue r) ∧
      (∀ off : Nat, 312 ≤ off → off+8 ≤ 336 →
        memLoad t.external (stackPtr s+BitVec.ofNat 64 off) 64 =
          memLoad s.external (stackPtr s+BitVec.ofNat 64 off) 64) := by
  obtain ⟨slices,call⟩ := ctx.call
  have outside := outer_boundary call ctx.machine ctx.bindingsSupported
  obtain ⟨np,c,runP,sc,ipc,scalarC,wordC,src,dst,countC,regsC,slotsC⟩ :=
    prepare_tail ctx state rip scalar
  obtain ⟨dstate,runD,rd,ipd,gd,bytes⟩ := Rep.run call outside sc.bindingsSupported
    (readyToStep sc.machine sc.bindingsSupported) sc.directionFlag sc.loaded sc.allocated
    ipc src dst countC
  have sd := after ctx sc runD rd gd (by
    intro co hc addr ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    exact ⟨workRegion initial,by simp,work_contains call.stackAvailable.1
      (by decide) (by decide) ha⟩) (by simp) (by simp)
  obtain ⟨ne,e,runE,se,ee⟩ := finalstore ctx sd ipd
  have spd : stackPtr dstate=stackPtr s := sd.rsp.trans state.rsp.symm
  have spe : stackPtr e=stackPtr s := se.rsp.trans state.rsp.symm
  have word : memLoad e.external (stackPtr e+368) 64=BitVec.ofNat 64 d := by
    have h : memLoad e.external (stackPtr dstate+368) 64=dstate.regValue .rax := ee.writes
    have hd : dstate.regValue .rax=c.regValue .rax := gd.read (n := 64) (r := 0) (by simp)
    rw [spe,← spd]
    exact h.trans (hd.trans wordC)
  have scalarE : Nat256At e (stackPtr e+368) d := by
    refine ⟨scalar.1,fun i hi => ?_⟩
    by_cases low : i<8
    · have hb := (Bytes.of_memLoad (n := 64) (readable ctx se (off := 368) (len := 8) (by decide)).mem) i low
      change e.external[stackPtr e+368+BitVec.ofNat 64 i]?=
        some (storedByte (memLoad e.external (stackPtr e+368) 64) i) at hb
      rw [word,ReadBe.storedByte_ofNat64 _ _ low] at hb
      exact hb
    · have hcopy := bytes (i-8) (by omega)
      have ac : stackPtr c+72=stackPtr initial-448 := address sc (off := 72) (by decide)
      have ad : stackPtr dstate+376=stackPtr initial-144 := address sd (off := 376) (by decide)
      rw [← ad,← ac] at hcopy
      have h := (finalstore_bytes ee (i := i-8) (by omega)).trans hcopy
      have eq1 : (368 : BitVec 64)+BitVec.ofNat 64 i=376+BitVec.ofNat 64 (i-8) := by
        change BitVec.ofNat 64 368+BitVec.ofNat 64 i=BitVec.ofNat 64 376+BitVec.ofNat 64 (i-8)
        rw [← BitVec.ofNat_add,← BitVec.ofNat_add]; congr 1; omega
      have eq2 : (72 : BitVec 64)+BitVec.ofNat 64 (i-8)=64+BitVec.ofNat 64 i := by
        change BitVec.ofNat 64 72+BitVec.ofNat 64 (i-8)=BitVec.ofNat 64 64+BitVec.ofNat 64 i
        rw [← BitVec.ofNat_add,← BitVec.ofNat_add]; congr 1; omega
      rw [spe,← spd,BitVec.add_assoc,eq1,← BitVec.add_assoc]
      apply h.trans
      rw [BitVec.add_assoc,eq2,← BitVec.add_assoc]
      exact scalarC.2 i hi
  have agAll := gd.trans ee.agrees
  have h13 : e.regValue .r13=2 :=
    (agAll.read (n := 64) (r := 13) (by simp [FinalStore.effect,Effect.components])).trans ((regsC .r13 (by simp)).trans count)
  obtain ⟨t,runF,st,ipt,gf⟩ := count_branch ctx se ee.rip h13
  refine ⟨np+12+ne+2,t,((runP.trans runD).trans runE).trans runF,
    st,ipt,?_,?_,?_⟩
  · have memory := gf.external (by simp [Component.Covers])
    have addr : stackPtr e+368=stackPtr initial-152 := address se (off := 368) (by decide)
    rw [addr] at scalarE
    exact ⟨scalarE.1,fun i hi => by rw [memory]; exact scalarE.2 i hi⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact (gf.read (n := 64) (r := 12) (by simp)).trans
        ((agAll.read (n := 64) (r := 12) (by simp [FinalStore.effect,Effect.components])).trans
          (regsC .r12 (by simp)))
    · exact (gf.read (n := 64) (r := 15) (by simp)).trans
        ((agAll.read (n := 64) (r := 15) (by simp [FinalStore.effect,Effect.components])).trans
          (regsC .r15 (by simp)))
  · intro off low high
    have repSlot : memLoad dstate.external (stackPtr s+BitVec.ofNat 64 off) 64 =
        memLoad c.external (stackPtr s+BitVec.ofNat 64 off) 64 := by
      apply memLoad_agrees_apart gd
      intro addr len member
      simp only [List.mem_cons,List.not_mem_nil,or_false,false_or,
        Component.mem.injEq,reduceCtorEq] at member
      obtain ⟨rfl,rfl⟩ := member
      have dstAddress : stackPtr initial-144=stackPtr s+376 := (address state (off := 376) (by decide)).symm
      rw [dstAddress]
      intro i hi j hj eq
      exact (show OffsetsApart 376 96 (BitVec.ofNat 64 off) 8 by
        simp only [OffsetsApart,BitVec.toNat_sub,BitVec.toNat_ofNat,BitVec.reduceToNat]
        omega).ne (stackPtr s) hi hj (by decide) eq
    have lastSlot : memLoad e.external (stackPtr s+BitVec.ofNat 64 off) 64 =
        memLoad dstate.external (stackPtr s+BitVec.ofNat 64 off) 64 := by
      apply memLoad_agrees_apart ee.agrees
      intro addr len member
      simp only [FinalStore.effect,Effect.components,Write.component,Operand.component,
        List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,Component.mem.injEq,reduceCtorEq] at member
      obtain ⟨rfl,rfl⟩ := member
      change RangeApart (stackPtr dstate+368) 8 _ 8
      rw [spd]
      intro i hi j hj eq
      exact (show OffsetsApart 368 8 (BitVec.ofNat 64 off) 8 by
        simp only [OffsetsApart,BitVec.toNat_sub,BitVec.toNat_ofNat,BitVec.reduceToNat]
        omega).ne (stackPtr s) hi hj (by decide) eq
    rw [gf.external (by simp [Component.Covers])]
    exact lastSlot.trans (repSlot.trans (slotsC off low high))

end P256.Proofs.Signing.Wrapper.Entry.Construct
