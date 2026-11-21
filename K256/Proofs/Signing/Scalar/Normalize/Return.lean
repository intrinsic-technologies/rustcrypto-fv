import K256.Proofs.Signing.Scalar.Normalize.State
import K256.Proofs.Verify.LIR.Fn104c90

namespace K256.Proofs.Signing.Scalar.Normalize

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Verify.LIR Generate.Generator.Multiply Standards.SECG.DomainParameters.Secp256k1

private abbrev Limbs := Vector (BitVec 64) 4

private def writeback (m : Ram) (sp : BitVec 64) (flag : BitVec 8) (r s : Limbs) : Ram :=
  let m := memStore m (sp - 96) flag
  let m := memStore m (sp + 40) r[3]
  let m := memStore m (sp + 32) r[2]
  let m := memStore m (sp + 24) r[1]
  let m := memStore m (sp + 16) r[0]
  let m := memStore m (sp + 48) s[0]
  let m := memStore m (sp + 56) s[1]
  let m := memStore m (sp + 64) s[2]
  memStore m (sp + 72) s[3]

private theorem writeback_words (m : Ram) (sp : BitVec 64) (flag : BitVec 8) (r s : Limbs) :
    WordsAt (writeback m sp flag r s) (sp + 16) 64 r ∧
    WordsAt (writeback m sp flag r s) (sp + 48) 64 s := by
  constructor <;> intro i hi
  all_goals
    obtain rfl|rfl|rfl|rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
    all_goals
      simp only [writeback, wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
      segment_words [] <;> rfl

private theorem writeback_frame {fr : Activation} {r s : Nat} {m : Ram} (input : Inputs fr r s)
    (before : RamWriteFrame fr.original m [fr.region]) (flag : BitVec 8) (w z : Limbs) :
    RamWriteFrame fr.original (writeback m fr.rsp flag w z) [fr.region,⟨fr.rdi.toNat,64⟩] := by
  have initial : RamWriteFrame fr.original m [fr.region,⟨fr.rdi.toNat,64⟩] := by
    apply (RamWriteFrame.refl _ _).trans before
    intro t ht
    obtain rfl := List.mem_singleton.mp ht
    exact ⟨_,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩
  have room := input.room
  have high := input.high
  unfold writeback
  iterate 9 apply RamWriteFrame.memStore
  exact initial
  all_goals
    first
    | refine ⟨fr.region,List.mem_cons_self,?_⟩
      simp only [InRegion, Activation.region, input.low, BitVec.toNat_sub, BitVec.reduceToNat,
        Nat.reducePow, Nat.reduceDiv]
      omega
    | refine ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),?_⟩
      simp only [InRegion, input.dst, BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow, Nat.reduceDiv]
      omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem returnBlock {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    {wr ws wn : Limbs} {f : BitVec 8}
    (atoms : Atom.All Extracted.programImage a m (Fn104c90.frameAt .l104d5e fr))
    (dst : fr.rdi = fr.rsp + 16) (src : fr.rsi = fr.rsp + 200)
    (read : Readable m (fr.rsp + 200) 64) (write : Writable Extracted.programImage m (fr.rsp+16) 64)
    (rWords : WordsAt m (fr.rsp+200) 64 wr) (sWords : WordsAt m (fr.rsp+232) 64 ws)
    (nWords : WordsAt m (fr.rsp-128) 64 wn) (flag : a[0].get 8 = f) :
    ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l104d5e,a,m⟩ = .returned out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn104c90.doneAt fr) ∧
      out.store = writeback m fr.rsp f wr (if f = 0 then ws else wn) := by
  simp only [Fn104c90.frameAt, Fn104c90.frameAtG5, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp,df,bx,bp,r13,r14,mx,ft,fc,s3,s12,s14,s15,rr,ret,small,stack,_⟩ := atoms
  have rsp : a[4].get 64 = fr.rsp - 136 := congrArg (Value.get 64) sp
  have rbx : a[3].get 64 = fr.rsp + 16 := (congrArg (Value.get 64) bx).trans dst
  have srcReg : a[14].get 64 = fr.rsp + 200 := (congrArg (Value.get 64) r14).trans src
  have al : (a[0].get 64).setWidth 8 = f := (BitVec.setWidth_setWidth_of_le _ (by decide)).trans flag
  obtain ⟨r0,r1,r2,r3⟩ := Verify.Core.Components.wordsToLoads (off := 200) rWords
  obtain ⟨x0,x1,x2,x3⟩ := Verify.Core.Components.wordsToLoads (off := 232) sWords
  change memLoad m (fr.rsp + 200) 64 = _ at r0
  change memLoad m (fr.rsp + 208) 64 = _ at r1
  change memLoad m (fr.rsp + 216) 64 = _ at r2
  change memLoad m (fr.rsp + 224) 64 = _ at r3
  change memLoad m (fr.rsp + 232) 64 = _ at x0
  change memLoad m (fr.rsp + 240) 64 = _ at x1
  change memLoad m (fr.rsp + 248) 64 = _ at x2
  change memLoad m (fr.rsp + 256) 64 = _ at x3
  have n0 := nWords 0 (by decide)
  change memLoad m (wordAddr (fr.rsp-128) 64 0) 64 = wn[0] at n0
  rw [show wordAddr (fr.rsp-128) 64 0 = fr.rsp - 128 by unfold wordAddr; bv_omega] at n0
  have n1 := nWords 1 (by decide)
  change memLoad m (wordAddr (fr.rsp-128) 64 1) 64 = wn[1] at n1
  rw [show wordAddr (fr.rsp-128) 64 1 = fr.rsp - 120 by unfold wordAddr; bv_omega] at n1
  have n2 := nWords 2 (by decide)
  change memLoad m (wordAddr (fr.rsp-128) 64 2) 64 = wn[2] at n2
  rw [show wordAddr (fr.rsp-128) 64 2 = fr.rsp - 112 by unfold wordAddr; bv_omega] at n2
  have n3 := nWords 3 (by decide)
  change memLoad m (wordAddr (fr.rsp-128) 64 3) 64 = wn[3] at n3
  rw [show wordAddr (fr.rsp-128) 64 3 = fr.rsp - 104 by unfold wordAddr; bv_omega] at n3
  have test : (!(testFlags (f &&& f)).ZF.getD false) = decide (f ≠ 0) := by
    simp [testFlags, Bool.beq_eq_decide_eq]
  refine ⟨?_,?run,?tag,?done_,?memory⟩
  case run =>
    cfg_eval [rsp,rbx,srcReg,al]
    segment_words [rsp,rbx,srcReg,al,r0,r1,r2,r3,x0,x1,x2,x3,n0,n1,n2,n3,s3,s12,s14,s15,ret,test]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first | slot_guard using code_l104d5e | assumption)
    refine Eq.trans (ite_eq_left ⟨by slot_guard using code_l104d5e, small⟩) ?_
    rfl
  case tag => rfl
  case done_ =>
    simp only [Fn104c90.doneAt,Atom.All,Atom.Holds]
    exact ⟨rfl,df,rfl,bp,rfl,r13,rfl,rfl,mx,ft,fc,trivial⟩
  case memory =>
    by_cases h : f = 0#8 <;> simp [writeback,h]

theorem finish {fr : Activation} {a : Verify.Core.Registers} {r s : Nat}
    (input : Inputs fr r s) {m : Ram} (saved : Saved fr a m)
    (flag : a[0].get 8 = (if s > domain.n / 2 then 1 else 0))
    (negated : WordsAt m (fr.rsp - 128) 64 (scalarWords (domain.n - s))) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l104d5e,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn104c90.doneAt fr) ∧
      WordsAt out.store fr.rdi 64 (scalarWords r) ∧
      WordsAt out.store (fr.rdi + 32) 64 (scalarWords (if s > domain.n / 2 then domain.n - s else s)) ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat,64⟩] := by
  obtain ⟨rWords,sWords⟩ := input.words_of_frame saved.frame
  rw [input.src] at rWords sWords
  rw [show fr.rsp + 200 + 32 = fr.rsp + 232 by bv_omega] at sWords
  have read := input.read.of_frame saved.frame
  have write := input.write.of_frame saved.frame
  rw [input.src] at read
  rw [input.dst] at write
  obtain ⟨out,run,tag,done_,store⟩ :=
    returnBlock saved.atoms input.dst input.src read write rWords sWords negated flag
  refine ⟨out, .done (by simp only [Program.step, run, Transfer.next]), tag, done_, ?_, ?_, ?_⟩
  · rw [store,input.dst]
    exact (writeback_words ..).1
  · rw [store,input.dst,show fr.rsp + 16 + 32 = fr.rsp + 48 by bv_omega]
    have h := (writeback_words m fr.rsp
      (if s > domain.n / 2 then (1 : BitVec 8) else 0) (scalarWords r)
      (if (if s > domain.n / 2 then (1 : BitVec 8) else 0) = 0 then scalarWords s
        else scalarWords (domain.n-s))).2
    by_cases hs : s > domain.n / 2 <;> simpa only [hs,ite_true,ite_false,(by decide : (1 : BitVec 8) ≠ 0)] using h
  · rw [store]
    exact writeback_frame input saved.frame _ _ _

end K256.Proofs.Signing.Scalar.Normalize
