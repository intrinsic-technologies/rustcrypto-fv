import K256.Proofs.Signing.Nonce.Fill.Test.Zero

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Common.Invert.LinearCombination (subRaw borrow subWord)
open Initialize (State)
open Verify.Core (Registers Reaches)

private theorem zero_and_borrow {v : Value} {k : Nat}
    (h : v.get 8 = if k = 0 then 1 else 0) :
    ((~~~v.get 8) &&& ((if k < domain.n then 1 else 0 : BitVec 64).setWidth 8)) &&& 1 =
      if 0 < k ∧ k < domain.n then 1 else 0 := by
  rw [h]
  by_cases z : k = 0
  · rw [ite_eq_left z, ite_eq_right (show ¬ (0 < k ∧ k < domain.n) by omega)]
    split <;> decide +kernel
  · rw [ite_eq_right z]
    by_cases l : k < domain.n
    · rw [ite_eq_left l, ite_eq_left (show 0 < k ∧ k < domain.n by omega)]
      decide +kernel
    · rw [ite_eq_right l, ite_eq_right (show ¬ (0 < k ∧ k < domain.n) by omega)]
      decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2048 in
theorem testRange {fr : Activation} {state : State} {a : Registers} (env : Environment fr)
    {m : Ram} (d : Compared fr state a m) :
    ∃ b n, Reaches .l100cf5 a m (testTarget (candidate state).1) b n ∧ Tested fr state b n := by
  let k := (candidate state).1
  let w := scalarWords k
  let u := scalarWords domain.n
  have stack := d.toFrame.stack
  have lim := env.limit
  have depth := env.depth
  have src := (env.window.readable.sub
    (a := fr.rsp + 600) (n := 32) (by rw [env.addNat 600 (by decide)]; simp only [BitVec.reduceToNat]; omega)
    (by rw [env.addNat 600 (by decide)]; simp only [BitVec.reduceToNat]; omega)).of_frame d.writes
  have rsp : a[4].get 64 = sp fr := congrArg (Value.get 64) d.atoms.1
  have r15 : a[15].get 64 = fr.rsp + 600 := congrArg (Value.get 64) d.r15
  have x0 : memLoad m (sp fr + 72) 64 = w[0] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using d.words 0 (by decide)
  have x1 : memLoad m (sp fr + 80) 64 = w[1] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using d.words 1 (by decide)
  have x2 : memLoad m (sp fr + 88) 64 = w[2] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using d.words 2 (by decide)
  have x3 : memLoad m (sp fr + 96) 64 = w[3] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using d.words 3 (by decide)
  have orders := d.toFrame.orderWords env
  have y0 : memLoad m (fr.rsp + 600) 64 = u[0] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using orders 0 (by decide)
  have y1 : memLoad m (fr.rsp + 608) 64 = u[1] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using orders 1 (by decide)
  have y2 : memLoad m (fr.rsp + 616) 64 = u[2] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using orders 2 (by decide)
  have y3 : memLoad m (fr.rsp + 624) 64 = u[3] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using orders 3 (by decide)
  have rangeFlag := nonceOrderFlag k (candidateBound state)
  let stepWord (x y c : BitVec 64) := (0#64 - c).sshiftRight 63 + x - y
  let c0 := borrow w[0] u[0] (w[0] - u[0])
  let c1 := borrow w[1] u[1] (stepWord w[1] u[1] c0)
  let c2 := borrow w[2] u[2] (stepWord w[2] u[2] c1)
  let c3 := borrow w[3] u[3] (stepWord w[3] u[3] c2)
  have flag : c3 = if k < domain.n then 1 else 0 := by
    dsimp only [c3,c2,c1,c0,stepWord]
    simpa only [subWord_reassoc,subRaw,nonceLimbs] using rangeFlag
  have getLow : (a[0].get 64).setWidth 8 = a[0].get 8 :=
    BitVec.setWidth_setWidth_of_le _ (by decide)
  have readOther (mem : Ram) (v : BitVec 64) (i : BitVec 64)
      (h : 72 ≤ i.toNat) :
      memLoad (memStore mem (sp fr + 8) v) (sp fr + i) 64 =
        memLoad mem (sp fr + i) 64 := by
    apply readStoreApart
    apply RangeApart.of_offsets rfl rfl
    have iMax := i.isLt
    simp only [BitVec.toNat_sub,BitVec.reduceToNat]
    omega
  have upperAddr (i : BitVec 64) : fr.rsp + i = sp fr + (232 + i) := by unfold sp; bv_omega
  have readOrder (mem : Ram) (v : BitVec 64) (i : BitVec 64)
      (h : 600 ≤ i.toNat) (h' : i.toNat ≤ 624) :
      memLoad (memStore mem (sp fr + 8) v) (fr.rsp + i) 64 =
        memLoad mem (fr.rsp + i) 64 := by
    rw [upperAddr i]
    apply readOther
    rw [BitVec.toNat_add]
    simp only [BitVec.reduceToNat]
    omega
  have extractLow (v : BitVec 64) : v.extractLsb' 0 8 = v.setWidth 8 := rfl
  have low : ((~~~a[0].get 8) &&& ((if k < domain.n then 1 else 0 : BitVec 64).setWidth 8)) &&& 1 =
      (if 0 < k ∧ k < domain.n then 1 else 0) := zero_and_borrow d.zero
  have condEq : (¬ (((~~~a[0].get 8) &&& c3.setWidth 8) &&& 1) = 0) =
      (¬ ((if 0 < k ∧ k < domain.n then 1 else 0) : BitVec 8) = 0) :=
    congrArg (fun q : BitVec 8 => ¬ q = 0)
      ((congrArg (fun q : BitVec 64 => ((~~~a[0].get 8) &&& q.setWidth 8) &&& 1) flag).trans low)
  have branch (args : Registers) (mem : Ram) :
      (if ¬ ((if 0 < k ∧ k < domain.n then 1 else 0) : BitVec 8) = 0 then
        (Transfer.jump ⟨.l100df5,args,mem⟩ : Transfer Value Ram Label signature Reg.count)
      else .jump ⟨.l100dd3,args,mem⟩) = .jump ⟨testTarget k,args,mem⟩ := by
    by_cases h : 0 < k ∧ k < domain.n
    · rw [ite_eq_left h, ite_eq_left (by decide)]
      rw [show testTarget k = .l100df5 from ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right (by decide)]
      rw [show testTarget k = .l100dd3 from ite_eq_right h]
  have eq : ∃ (b : Registers) (n : Ram),
      program.runBlock (dialect Extracted.programImage) ⟨.l100cf5,a,m⟩ =
        (if ¬ ((if 0 < k ∧ k < domain.n then 1 else 0) : BitVec 8) = 0 then
          .jump ⟨.l100df5,b,n⟩ else .jump ⟨.l100dd3,b,n⟩) ∧ Tested fr state b n := by
    refine ⟨?_,?_,?run,?post⟩
    case run =>
      cfg_eval [rsp,r15,x0,x1,x2,x3,y0,y1,y2,y3]
      segment_words [rsp,r15,x0,x1,x2,x3,y0,y1,y2,y3]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l100cf5)
      simp (disch := decide) only [readOrder,extractLow,y1,y2,y3,setWidth_mergeGPR8,getLow]
      change (if ¬ (((~~~a[0].get 8) &&& c3.setWidth 8) &&& 1) = 0 then _ else _) = _
      refine (ite_cond_congr condEq).trans ?_
      rfl
    case post =>
      have inSlot (j : Nat) (hj : j ≤ 8) :
          InRegions [⟨(sp fr + 8).toNat,8⟩] (sp fr + 8) j := by
        refine ⟨_,List.mem_singleton_self _,?_⟩
        change (sp fr + 8).toNat ≤ _ ∧ _ + j ≤ (sp fr + 8).toNat + 8 ∧ _ + j ≤ 2^64
        rw [env.slotNat 8 (by decide)]
        simp only [BitVec.reduceToNat]
        omega
      have leftApart : Outside [⟨(sp fr + 8).toNat,8⟩] (sp fr + 72) 32 := by
        refine ⟨?_, fun r hr => ?_⟩
        · rw [env.slotNat 72 (by decide)]
          simp only [BitVec.reduceToNat]
          omega
        · obtain rfl := List.mem_singleton.mp hr
          right
          change (sp fr+8).toNat + 8 ≤ (sp fr+72).toNat
          rw [env.slotNat 8 (by decide),env.slotNat 72 (by decide)]
          simp only [BitVec.reduceToNat]
          omega
      refine ⟨d.toFrame.testStores env ?writes ?_ ?_,
        stateAfter ?writes (testStateOutside env) d.stateAt,
        d.words.of_frame ?saved (by decide) leftApart, d.r13, d.r15⟩
      · iterate 5 apply RamWriteFrame.memStore _ _ (testScratch_in env 8 _ (by decide))
        exact RamWriteFrame.refl _ _
      · rintro ⟨i,hi⟩ h
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl|rfl|rfl|rfl|rfl <;> rfl
      · rintro ⟨i,hi⟩ h
        have hw := d.widths ⟨i,hi⟩ h
        simp only [Activation.entryNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact hw
      · iterate 5 apply RamWriteFrame.memStore _ _ (inSlot _ (by decide))
        exact RamWriteFrame.refl _ _
  obtain ⟨b,n,step,post⟩ := eq
  refine ⟨b,n,.step (b := ⟨⟨testTarget k,b,n⟩,[]⟩) ?_ (.refl _),post⟩
  change (program.runBlock _ _).next _ _ = _
  rw [step.trans (branch b n)]
  rfl

end K256.Proofs.Signing.Nonce.Fill
