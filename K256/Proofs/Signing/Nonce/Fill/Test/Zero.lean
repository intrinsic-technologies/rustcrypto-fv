import K256.Proofs.Signing.Nonce.Fill.Test.Memory
import K256.Proofs.Signing.Nonce.Fill.Test.Arithmetic
import K256.Proofs.Generate.Generator.Sample.Calls
import K256.Proofs.Verify.Choice
import K256.Proofs.Verify.LIR.Fn100a40

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
open Generate.Generator.Multiply (scalarWords)
open Initialize (State StateAt)
open Verify.Core (Registers Reaches)

theorem testScratch_in {fr : Activation} (env : Environment fr)
    (i : BitVec 64) (n : Nat)
    (range : i.toNat + n ≤ 40 ∨ 72 ≤ i.toNat ∧ i.toNat + n ≤ 104 ∨
      152 ≤ i.toNat ∧ i.toNat + n ≤ 160) :
    InRegions (testScratch fr) (sp fr + i) n := by
  have depth := env.depth
  have limit := env.limit
  have addr := env.slotNat i (by omega : i.toNat ≤ 232)
  rcases range with h|h|h
  · refine ⟨⟨(sp fr - 8).toNat,48⟩, List.mem_cons_self .., ?_⟩
    change (sp fr - 8).toNat ≤ _ ∧ _ + n ≤ (sp fr - 8).toNat + 48 ∧ _ + n ≤ 2^64
    rw [addr,env.pushNat]
    omega
  · refine ⟨⟨(sp fr+72).toNat,32⟩, by simp only [testScratch,List.mem_cons,true_or,or_true], ?_⟩
    change (sp fr + 72).toNat ≤ _ ∧ _ + n ≤ (sp fr + 72).toNat + 32 ∧ _ + n ≤ 2^64
    rw [addr,env.slotNat 72 (by decide)]
    simp only [BitVec.reduceToNat]
    omega
  · refine ⟨⟨(sp fr+152).toNat,8⟩, by simp only [testScratch,List.mem_cons,true_or,or_true], ?_⟩
    change (sp fr + 152).toNat ≤ _ ∧ _ + n ≤ (sp fr + 152).toNat + 8 ∧ _ + n ≤ 2^64
    rw [addr,env.slotNat 152 (by decide)]
    simp only [BitVec.reduceToNat]
    omega

private theorem testScratch_push_in {fr : Activation} (env : Environment fr) :
    InRegions (testScratch fr) (sp fr - 8) 8 := by
  refine ⟨⟨(sp fr - 8).toNat,48⟩, List.mem_cons_self .., ?_⟩
  change (sp fr - 8).toNat ≤ _ ∧ _ + 8 ≤ (sp fr - 8).toNat + 48 ∧ _ + 8 ≤ 2^64
  have := env.limit
  rw [env.pushNat]
  omega

private theorem testWordAddr (p : BitVec 64) (i : Nat) :
    wordAddr p 64 i = p + BitVec.ofNat 64 (8*i) := rfl

theorem readStoreApart {m : Ram} {a b : BitVec 64} {v : BitVec 64}
    (apart : RangeApart b 8 a 8) : memLoad (memStore m b v) a 64 = memLoad m a 64 :=
  memLoad_memStore_of_rangeApart _ _ _ _ _ apart

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2048 in
private theorem zeroCall {fr : Activation} {state : State} {a : Registers} (env : Environment fr)
    {m : Ram} (d : Decoded fr state a m) :
    ∃ b n, program.runBlock (dialect Extracted.programImage) ⟨.l100c8a,a,m⟩ =
      .call ⟨.l127f50,b,n⟩ (Verify.resumeAt .l100cf5 0x100cf5) ∧
      b[4] = ⟨64,sp fr - 8⟩ ∧ b[7] = ⟨64,sp fr + 72⟩ ∧ b[2] = ⟨64,sp fr + 8⟩ ∧
      b[6] = ⟨64,4⟩ ∧ b[1] = ⟨64,4⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m n (testScratch fr) ∧ memLoad n (sp fr - 8) 64 = 0x100cf5 ∧
      WordsAt n (sp fr + 72) 64 (scalarWords (candidate state).1) ∧
      WordsAt n (sp fr + 8) 64 (#v[0,0,0,0] : Vector (BitVec 64) 4) := by
  have stack := d.toFrame.stack
  have rsp : a[4].get 64 = sp fr := congrArg (Value.get 64) d.atoms.1
  have r12 := congrArg (Value.get 64) d.r12
  have read0 : memLoad m (sp fr + 8) 64 = (scalarWords (candidate state).1)[0] := by
    simpa only [testWordAddr, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.add_zero] using d.words 0 (by decide)
  have read1 : memLoad m (sp fr + 16) 64 = (scalarWords (candidate state).1)[1] := by
    simpa only [testWordAddr, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.add_zero] using d.words 1 (by decide)
  have read2 : memLoad m (sp fr + 24) 64 = (scalarWords (candidate state).1)[2] := by
    simpa only [testWordAddr, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.add_zero] using d.words 2 (by decide)
  have read3 : memLoad m (sp fr + 32) 64 = (scalarWords (candidate state).1)[3] := by
    simpa only [testWordAddr, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.add_zero] using d.words 3 (by decide)
  have depth := env.depth
  have limit := env.limit
  refine ⟨?_,?_,?run,?post⟩
  case run =>
    cfg_eval [rsp,r12,read0,read1,read2,read3]
    segment_words [rsp,r12,read0,read1,read2,read3]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l100c8a)
    rfl
  case post =>
    refine ⟨rfl,rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_⟩
    · rintro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · apply RamWriteFrame.memStore _ _ (testScratch_push_in env)
      repeat' apply RamWriteFrame.memStore _ _ (testScratch_in env _ _ (by decide))
      exact RamWriteFrame.refl _ _
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · intro i hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl|rfl|rfl|rfl <;>
        simp only [testWordAddr,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] <;>

        simp only [BitVec.sub_eq_add_neg] <;>
        simp (disch := first | decide | exact RangeApart.of_offsets rfl rfl (by decide)) only
          [readStoreApart,memLoad_memStore_same]
    · intro i hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl|rfl|rfl|rfl <;>
        simp only [testWordAddr,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] <;>

        simp only [BitVec.sub_eq_add_neg] <;>
        simp (disch := first | decide | exact RangeApart.of_offsets rfl rfl (by decide)) only
          [readStoreApart,memLoad_memStore_same] <;> rfl

structure Compared (fr : Activation) (state : State) (a : Registers) (m : Ram) : Prop
    extends Tested fr state a m where
  zero : a[0].get 8 = if (candidate state).1 = 0 then 1 else 0

theorem testZero {fr : Activation} {state : State} {a : Registers} (env : Environment fr)
    {m : Ram} (d : Decoded fr state a m) :
    ∃ b n, Reaches .l100c8a a m .l100cf5 b n ∧ Compared fr state b n := by
  obtain ⟨b,n,call,rs,di,dx,si,cx,keep,writes,ret,words,zeros⟩ := zeroCall env d
  let child := {fr with
    original := n, rsp := sp fr - 8, low := sp fr - 8,
    ret := 0x100cf5, rdi := sp fr + 72, rdx := sp fr + 8, rsi := 4, rcx := 4,
    rbx := a[3].get 64, rbp := a[5].get 64, r8 := a[8].get 64, r9 := a[9].get 64,
    r12 := sp fr + 8, r13 := 32, r14 := a[14].get 64, r15 := fr.rsp + 600}
  have reg64 (i : Fin Reg.count) (hi : i.val ∈ Activation.entryNumbers) :
      a[i] = ⟨64,a[i].get 64⟩ := by
    have h := d.widths i hi
    generalize a[i] = v at h ⊢
    cases v with
    | mk w v => cases h; rfl
  have left := ((d.toFrame.slot env 72 32 (by decide)).readable).of_frame writes
  have right := ((d.toFrame.slot env 8 32 (by decide)).readable).of_frame writes
  have retRead := (d.toFrame.pushSlot env).readable.of_frame writes
  have atoms := d.atoms
  simp only [Fn100a40.frameAt,Fn100a40.frameAtG1,Atom.All,Atom.Holds] at atoms
  obtain ⟨_,df,mx,ft,fc,_,_,_,_,_,_,_,_,_,_,_,_,_,_,aligned,_⟩ := atoms
  have entry : Atom.All Extracted.programImage b n (Proofs.LIR.Fn127f50.frameAt .l127f50 child) := by
    refine ⟨rs,(keep 22 (by decide)).trans df,cx,dx,
      (keep 3 (by decide)).trans (reg64 3 (by decide)),
      (keep 5 (by decide)).trans (reg64 5 (by decide)),si,di,
      (keep 8 (by decide)).trans (reg64 8 (by decide)),
      (keep 9 (by decide)).trans (reg64 9 (by decide)),
      (keep 12 (by decide)).trans d.r12,(keep 13 (by decide)).trans d.r13,
      (keep 14 (by decide)).trans (reg64 14 (by decide)),(keep 15 (by decide)).trans d.r15,
      (keep 39 (by decide)).trans mx,(keep 50 (by decide)).trans ft,(keep 51 (by decide)).trans fc,
      retRead,ret,by change (0x100cf5#64).toNat < 2^32; decide,Nat.le_refl _,?_,trivial⟩
    change (sp fr - 8).toNat % 16 = 8
    rw [env.pushNat]
    have := env.depth
    omega
  obtain ⟨out,run,tag,done_,_,aw,same,iffEq,binary⟩ :=
    Generate.Generator.Sample.ctEq_call Common.fnCode_subset_programImage child rfl rfl left right b entry
  have reached := Verify.reachesOfCall call (Verify.Transfer.compareExec rfl run) tag
  change out.store = n at same
  rw [same] at reached
  rw [← Proofs.LIR.Fn127f50.doneAt_canonical] at done_
  simp only [Proofs.LIR.Fn127f50.doneAt,Atom.All,Atom.Holds] at done_
  obtain ⟨rsp',df',bx',bp',r12',r13',r14',r15',mx',ft',fc',_⟩ := done_
  have rsp'' : out.values[4] = ⟨64,sp fr⟩ :=
    rsp'.trans (congrArg (Value.mk 64) (BitVec.sub_add_cancel _ _))
  have preserved (i : Fin Reg.count) (hi : i.val ∈ [4,22,39,50,51]) :
      out.values[i] = a[i] := by
    rcases i with ⟨i,h⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · exact rsp''.trans d.atoms.1.symm
    · exact df'.trans df.symm
    · exact mx'.trans mx.symm
    · exact ft'.trans ft.symm
    · exact fc'.trans fc.symm
  have widths (i : Fin Reg.count) (hi : i.val ∈ Activation.entryNumbers) :
      out.values[i].width = 64 := by
    rcases i with ⟨i,h⟩
    simp only [Activation.entryNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact aw ⟨1,h⟩ (by change 1 ∈ Activation.argumentNumbers; decide)
    · exact aw ⟨2,h⟩ (by change 2 ∈ Activation.argumentNumbers; decide)
    · exact congrArg Value.width bx'
    · exact congrArg Value.width rsp''
    · exact congrArg Value.width bp'
    · exact aw ⟨6,h⟩ (by change 6 ∈ Activation.argumentNumbers; decide)
    · exact aw ⟨7,h⟩ (by change 7 ∈ Activation.argumentNumbers; decide)
    · exact aw ⟨8,h⟩ (by change 8 ∈ Activation.argumentNumbers; decide)
    · exact aw ⟨9,h⟩ (by change 9 ∈ Activation.argumentNumbers; decide)
    · exact congrArg Value.width r12'
    · exact congrArg Value.width r13'
    · exact congrArg Value.width r14'
    · exact congrArg Value.width r15'
  have beq : out.values[0].get 8 = 1 ↔ (candidate state).1 = 0 := by
    change _ ↔ _ at iffEq
    rw [iffEq, ← nonceLimbs_zero (candidateBound state)]
    constructor
    · intro h i hi
      have z : (#v[0,0,0,0] : Vector (BitVec 64) 4)[i] = 0 := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl|rfl|rfl|rfl <;> rfl
      exact (words i hi).symm.trans ((h i hi).trans ((zeros i hi).trans z))
    · intro h i hi
      rw [show memLoad n (wordAddr (sp fr + 72) 64 i) 64 = _ from words i hi, h i hi,
        show memLoad n (wordAddr (sp fr + 8) 64 i) 64 = _ from zeros i hi]
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl|rfl|rfl|rfl <;> rfl
  refine ⟨out.values,n,reached,⟨⟨d.toFrame.testStores env writes preserved widths,
    stateAfter writes (testStateOutside env) d.stateAt,words,r13',r15'⟩,?_⟩⟩
  split
  · rename_i h
    exact beq.mpr h
  · rename_i h
    exact binary.resolve_right fun one => h (beq.mp one)

end K256.Proofs.Signing.Nonce.Fill
