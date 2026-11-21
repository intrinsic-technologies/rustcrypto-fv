import K256.Proofs.Signing.Scalar.Normalize.State
import K256.Proofs.Verify.LIR.Fn104c90
import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.ScalarNeg
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Scalar.Normalize

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Verify.LIR Generate.Generator.Multiply Standards.SECG.DomainParameters.Secp256k1

private abbrev W := BitVec 64
private abbrev Limbs := Vector W 4
private abbrev Regs := Verify.Core.Registers

private def writes (sp : W) : List MemoryRegion := [⟨(sp - 464).toNat, 432⟩]

local macro "stack_bounds" : tactic => `(tactic|
  (simp only [InRegion, writes, BitVec.toNat_add, BitVec.toNat_sub, BitVec.reduceToNat,
    Nat.reducePow, Nat.reduceDiv] at *
   omega))

local macro "stack_addresses" : tactic => `(tactic|
  simp -failIfUnchanged only [Lift.reduceAddOffset, Lift.reduceSubOffset, Lift.reduceAddNeg,
    Lift.reduceSubNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero, BitVec.add_assoc])

private theorem stackSlot {sp : W} (room : 464 ≤ sp.toNat) (high : sp.toNat + 264 < 2^32)
    (off : W) (len : Nat) (fit : len ≤ off.toNat) (depth : off.toNat ≤ 464)
    (inside : 32 ≤ off.toNat - len) : InRegions (writes sp) (sp - off) len := by
  refine ⟨_,List.mem_singleton_self _,?_⟩
  unfold InRegion
  rw [show (sp - off).toNat = sp.toNat - off.toNat from
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
  stack_bounds

private theorem stackSub {sp : W} {m : Ram} (w : Writable Extracted.programImage m (sp - 464) 464)
    (off : W) (len : Nat) (fit : len ≤ off.toNat) (depth : off.toNat ≤ 464) :
    Writable Extracted.programImage m (sp - off) len :=
  w.of_offsets (addr_sub sp off) (addr_sub sp 464) (by
    simp only [BitVec.toNat_sub, BitVec.reduceToNat, Nat.reducePow]
    omega)

private theorem loadStored64 (m : Ram) (addr v : W) :
    memLoad (memStore m addr v) addr 64 = v :=
  memLoad_memStore_same m addr v (by decide) (by decide)

private theorem loadBelow {m : Ram} {sp off src : W} {n : Nat} (v : BitVec n)
    (apart : n / 8 ≤ (src- (0-off)).toNat ∧ 8 ≤ ((0-off)-src).toNat) :
    memLoad (memStore m (sp-off) v) (sp+src) 64 = memLoad m (sp+src) 64 :=
  memLoad_memStore_of_rangeApart m _ _ v 64 (RangeApart.of_offsets (addr_sub _ _) rfl apart)

private theorem loadSeparate {m : Ram} {sp off src : W} {n k : Nat} (v : BitVec n)
    (apart : n / 8 ≤ (off-src).toNat ∧ k / 8 ≤ (src-off).toNat) :
    memLoad (memStore m (sp-off) v) (sp-src) k = memLoad m (sp-src) k :=
  memLoad_memStore_of_rangeApart m _ _ v k (RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _) (by
    rwa [show (0 : W)-src-(0-off) = off-src by bv_omega,
      show (0 : W)-off-(0-src) = src-off by bv_omega]))

private theorem wordLoads {base : W} {m : Ram} {w : Limbs} (words : WordsAt m base 64 w) :
    memLoad m base 64 = w[0] ∧ memLoad m (base+8) 64 = w[1] ∧
    memLoad m (base+16) 64 = w[2] ∧ memLoad m (base+24) 64 = w[3] := by
  refine ⟨?_, words 1 (by decide), words 2 (by decide), words 3 (by decide)⟩
  simpa only [wordAddr, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using words 0 (by decide)

private abbrev kept : List Nat := [3,5,13,14,22,39,50,51]
local macro "kept_regs" : tactic => `(tactic|
  (rintro ⟨i,_⟩ hi
   simp only [kept,List.mem_cons,List.not_mem_nil,or_false] at hi
   rcases hi with h|h|h|h|h|h|h|h <;> subst i <;> rfl))

private def stage (m : Ram) (sp : W) (w : Limbs) : Ram :=
  let m := memStore m (sp-104) w[3]
  let m := memStore m (sp-112) w[2]
  let m := memStore m (sp-120) w[1]
  let m := memStore m (sp-128) w[0]
  memStore m (sp-144) (0x104d49 : W)

private theorem stage_words (m : Ram) (sp : W) (w : Limbs) :
    WordsAt (stage m sp w) (sp-128) 64 w := by
  intro i hi
  obtain rfl|rfl|rfl|rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
  all_goals
    simp only [stage,wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat]
    stack_addresses
    simp -failIfUnchanged (disch := decide) only [loadStored64, loadSeparate] <;> first | exact loadStored64 _ _ _ | rfl

set_option maxHeartbeats 900000 in
set_option maxRecDepth 4096 in
private theorem stageBlock {a : Regs} {m : Ram} {sp : W} {w : Limbs}
    (rsp : a[4].get 64 = sp-136) (src : a[14].get 64 = sp+200)
    (read : Readable m (sp+232) 32) (words : WordsAt m (sp+232) 64 w)
    (win : Writable Extracted.programImage m (sp-464) 464)
    (_room : 464 ≤ sp.toNat) (_high : sp.toNat+264 < 2^32) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l104d10,a,m⟩ =
        .call ⟨.l10a2d0,b,stage m sp w⟩ (Verify.resumeAt .l104d49 0x104d49) ∧
      b[4] = ⟨64,sp-144⟩ ∧ b[6] = ⟨64,sp-128⟩ ∧ b[7] = ⟨64,sp-64⟩ ∧
      b[12] = ⟨64,sp-64⟩ ∧ b[15] = ⟨64,sp+232⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ kept → b[i] = a[i]) := by
  obtain ⟨h0,w1,w2,w3⟩ := wordLoads words
  have h1 : memLoad m (sp+240) 64 = w[1] := by
    rw [show sp+240 = sp+232+8 by bv_omega]
    exact w1
  have h2 : memLoad m (sp+248) 64 = w[2] := by
    rw [show sp+248 = sp+232+16 by bv_omega]
    exact w2
  have h3 : memLoad m (sp+256) 64 = w[3] := by
    rw [show sp+256 = sp+232+24 by bv_omega]
    exact w3
  refine ⟨?_,?run,?post⟩
  case run =>
    cfg_eval [rsp,src,Lift.reduceAddOffset,Lift.reduceSubOffset,Lift.reduceAddNeg,Lift.reduceSubNeg,BitVec.reduceAdd,BitVec.reduceSub,BitVec.add_assoc]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l104d10)
    unfold stage
    stack_addresses
    simp -failIfUnchanged (disch := decide) only [loadBelow]
    simp only [h0,h1,h2,h3]
    rfl
  case post =>
    refine ⟨?_,?_,?_,?_,?_,by kept_regs⟩ <;> stack_addresses <;> rfl

set_option maxRecDepth 4096 in
private theorem modulusBlock (a : Regs) (m : Ram) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l10a2d0,a,m⟩ =
      .jump ⟨.l110b80,b,m⟩ ∧ b[2] = ⟨64,0x2021a0#64⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ (([4,6,7,12,15] ++ kept) : List Nat) → b[i] = a[i]) := by
  refine ⟨?_,?run,?post⟩
  case run => cfg_eval []; rfl
  case post =>
    refine ⟨rfl,?_⟩
    rintro ⟨i,_⟩ hi
    simp only [kept,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private def negateLabel : Generate.LIR.Label → Option Label
  | .l110b80 => some .l110b80
  | _ => none

private theorem negateBlocks (a : Generate.LIR.Label) (b : Label) (h : negateLabel a = some b) :
    Generate.Serialize.Relabel.block negateLabel (Generate.LIR.program.blocks a) =
      Generate.Serialize.Relabel.block some (program.blocks b) := by
  unfold negateLabel at h
  split at h <;> cases h
  with_unfolding_all rfl

set_option maxRecDepth 4096 in
private theorem copySetup {a : Regs} {m : Ram} {sp : W}
    (rsp : a[4].get 64 = sp-136) (src : a[12].get 64 = sp-64)
    (win : Writable Extracted.programImage m (sp-464) 464)
    (_room : 464 ≤ sp.toNat) (_high : sp.toNat+264 < 2^32) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l104d49,a,m⟩ =
        .call ⟨.l11c3f0,b,memStore m (sp-144) (0x104d56 : W)⟩ (Verify.resumeAt .l104d56 0x104d56) ∧
      b[4] = ⟨64,sp-144⟩ ∧ b[6] = ⟨64,sp-64⟩ ∧ b[7] = ⟨64,sp-128⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ 15 :: 12 :: kept → b[i] = a[i]) := by
  refine ⟨?_,?run,?post⟩
  case run =>
    cfg_eval [rsp,src,Lift.reduceAddOffset,Lift.reduceSubOffset,Lift.reduceAddNeg,Lift.reduceSubNeg,BitVec.reduceAdd,BitVec.reduceSub,BitVec.add_assoc]
    refine Eq.trans (ite_eq_left ?_) ?_
    · slot_guard using code_l104d49
    · stack_addresses; rfl
  case post =>
    refine ⟨?_,rfl,?_,?_⟩
    · stack_addresses; rfl
    · stack_addresses; rfl
    · rintro ⟨i,_⟩ hi
      simp only [kept,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem copyJump (a : Regs) (m : Ram) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l11c3f0,a,m⟩ =
      .jump ⟨.l11c400,b,m⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ (([4,6,7,12,15] ++ kept) : List Nat) → b[i] = a[i]) := by
  refine ⟨?_,?run,?post⟩
  case run => cfg_eval []; rfl
  case post =>
    rintro ⟨i,_⟩ hi
    simp only [kept,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem borrowOne {s : Nat} (bounds : s < domain.n) :
    let w := scalarWords s
    ParseSignature.Scalar.borrowChain w[0] w[1] w[2] w[3] = 1 := by
  let w := scalarWords s
  have val := Split.scalarWords_value s (Nat.lt_trans bounds (by decide +kernel))
  change w[0].toNat + 2^64 * (w[1].toNat + 2^64 * (w[2].toNat + 2^64 * w[3].toNat)) = s at val
  have packed : (w[3].toNat * 2^64 + w[2].toNat) * 2^128 + w[1].toNat * 2^64 + w[0].toNat = s := by
    omega
  change ParseSignature.Scalar.borrowChain w[0] w[1] w[2] w[3] = 1
  rw [ParseSignature.Scalar.borrowChain_eq, packed, ite_eq_left bounds]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private theorem borrowBlock {a : Regs} {m : Ram} {sp : W} {w : Limbs}
    (rsp : a[4].get 64 = sp-144) (src : a[6].get 64 = sp-64) (dst : a[7].get 64 = sp-128)
    (words : WordsAt m (sp-64) 64 w) (valid : ParseSignature.Scalar.borrowChain w[0] w[1] w[2] w[3] = 1)
    (win : Writable Extracted.programImage m (sp-464) 464)
    (room : 464 ≤ sp.toNat) (high : sp.toNat+264 < 2^32) :
    ∃ b pre, program.runBlock (dialect Extracted.programImage) ⟨.l11c400,a,m⟩ =
        .call ⟨.l127d50,b,memStore pre (sp-200-8) (0x11c4c4 : W)⟩ (Verify.resumeAt .l11c4c4 0x11c4c4) ∧
      b[4] = ⟨64,sp-200-8⟩ ∧ b[7] = ⟨64,1#64⟩ ∧ b[3] = ⟨64,sp-128⟩ ∧
      b[14] = ⟨64,w[0]⟩ ∧ b[15] = ⟨64,w[1]⟩ ∧ b[12] = ⟨64,w[2]⟩ ∧ b[13] = ⟨64,w[3]⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,22,39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m pre (writes sp) ∧
      memLoad pre (sp-184) 64 = a[3].get 64 ∧ memLoad pre (sp-176) 64 = a[12].get 64 ∧
      memLoad pre (sp-168) 64 = a[13].get 64 ∧ memLoad pre (sp-160) 64 = a[14].get 64 ∧
      memLoad pre (sp-152) 64 = a[15].get 64 ∧
      memLoad pre (sp-144) 64 = memLoad m (sp-144) 64 := by
  obtain ⟨h0,w1,w2,w3⟩ := wordLoads words
  have h1 : memLoad m (sp-56) 64 = w[1] := by
    rw [show sp-56 = sp-64+8 by bv_omega]
    exact w1
  have h2 : memLoad m (sp-48) 64 = w[2] := by
    rw [show sp-48 = sp-64+16 by bv_omega]
    exact w2
  have h3 : memLoad m (sp-40) 64 = w[3] := by
    rw [show sp-40 = sp-64+24 by bv_omega]
    exact w3
  have readByte (mem : Ram) (addr v : W) :
      memLoad (memStore mem addr v) addr 8 = v.extractLsb' 0 8 :=
    memLoad_memStore_within mem v 8 0 (BitVec.add_zero _).symm (by decide) (by decide) (by decide)
  refine ⟨?_,?_,?run,?post⟩
  case run =>
    cfg_eval [b_l11c400_1,b_l11c400_2,rsp,src,dst,loadStored64,readByte,
      Lift.reduceAddOffset,Lift.reduceSubOffset,Lift.reduceAddNeg,Lift.reduceSubNeg,BitVec.reduceAdd,BitVec.reduceSub]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l11c400)
    simp -failIfUnchanged (disch := decide) only [loadSeparate]
    simp only [h0,h1,h2,h3]
    rw [show sp-200-8 = sp-208 by bv_omega] <;> rfl
  case post =>
    refine ⟨?_,?_,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · stack_addresses; rfl
    · let byte := (ParseSignature.Scalar.borrowChain w[0] w[1] w[2] w[3]).extractLsb' 0 8
      change (⟨64,((mergeGPR 8 (byte &&& 1) (byte.setWidth 64)).setWidth 8).setWidth 64⟩ : Value) = _
      rw [show byte = 1 by dsimp only [byte]; rw [valid]; rfl]
      rfl
    · rintro ⟨i,_⟩ hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl <;> rfl
    · repeat' apply RamWriteFrame.memStore _ _ (by
        refine ⟨_,List.mem_singleton_self _,?_⟩
        stack_bounds)
      exact .refl _ _
    all_goals
      stack_addresses
      simp -failIfUnchanged (disch := decide) only [loadStored64, loadSeparate] <;> first | exact loadStored64 _ _ _ | rfl

private abbrev copyKept : List Nat := [3,5,12,13,14,15,22,39,50,51]

set_option maxRecDepth 4096 in
private theorem copyBranch {a : Regs} {m : Ram} {sp : W}
    (rsp : a[4].get 64 = sp-200) (one : a[0] = ⟨64,1#64⟩)
    (win : Writable Extracted.programImage m (sp-464) 464)
    (_room : 464 ≤ sp.toNat) (_high : sp.toNat+264 < 2^32) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l11c4c4,a,m⟩ =
        .jump ⟨.l11c4cc,b,memStore m (sp-193) (1 : BitVec 8)⟩ ∧
      b[4] = a[4] ∧ b[3] = a[3] ∧ b[12] = a[12] ∧ b[13] = a[13] ∧
      b[14] = a[14] ∧ b[15] = a[15] ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,22,39,50,51] → b[i] = a[i]) := by
  have low : a[0].get 64 = 1 := by rw [one]; rfl
  refine ⟨?_,?run,?post⟩
  case run =>
    cfg_eval [rsp,low,Lift.reduceAddOffset,Lift.reduceSubOffset,Lift.reduceAddNeg,Lift.reduceSubNeg,BitVec.reduceAdd,BitVec.reduceSub,BitVec.add_assoc]
    refine Eq.trans (ite_eq_left ?_) ?_
    · slot_guard using code_l11c4c4
    · stack_addresses; rfl
  case post =>
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
    rintro ⟨i,_⟩ hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> rfl

private def copied (m : Ram) (sp : W) (w : Limbs) : Ram :=
  let m := memStore m (sp-128) w[0]
  let m := memStore m (sp-120) w[1]
  let m := memStore m (sp-112) w[2]
  memStore m (sp-104) w[3]

private theorem copied_words (m : Ram) (sp : W) (w : Limbs) :
    WordsAt (copied m sp w) (sp-128) 64 w := by
  intro i hi
  obtain rfl|rfl|rfl|rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
  all_goals
    simp only [copied,wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat]
    stack_addresses
    simp -failIfUnchanged (disch := decide) only [loadStored64, loadSeparate] <;> first | exact loadStored64 _ _ _ | rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 900000 in
private theorem copyReturn {a old : Regs} {m : Ram} {sp : W} {w : Limbs}
    (rsp : a[4].get 64 = sp-200) (dst : a[3].get 64 = sp-128)
    (w0 : a[14].get 64 = w[0]) (w1 : a[15].get 64 = w[1])
    (w2 : a[12].get 64 = w[2]) (w3 : a[13].get 64 = w[3])
    (b3 : memLoad m (sp-184) 64 = old[3].get 64)
    (b12 : memLoad m (sp-176) 64 = old[12].get 64)
    (b13 : memLoad m (sp-168) 64 = old[13].get 64)
    (b14 : memLoad m (sp-160) 64 = old[14].get 64)
    (b15 : memLoad m (sp-152) 64 = old[15].get 64)
    (tag : memLoad m (sp-144) 64 = 0x104d56)
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,12,13,14,15] → old[i].width = 64)
    (win : Writable Extracted.programImage m (sp-464) 464)
    (_room : 464 ≤ sp.toNat) (_high : sp.toNat+264 < 2^32) :
    ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l11c4cc,a,m⟩ = .returned out ∧
      out.tag = some ⟨64,0x104d56#64⟩ ∧ out.values[4] = ⟨64,sp-136⟩ ∧
      out.store = copied m sp w ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,12,13,14,15] → out.values[i] = old[i]) ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,22,39,50,51] → out.values[i] = a[i]) := by
  have small : (0x104d56 : W).toNat < 2^32 := by decide
  refine ⟨?_,?run,?post⟩
  case run =>
    cfg_eval [rsp,dst,w0,w1,w2,w3,Lift.reduceAddOffset,Lift.reduceSubOffset,Lift.reduceAddNeg,Lift.reduceSubNeg,BitVec.reduceAdd,BitVec.reduceSub,BitVec.add_assoc]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l11c4cc)
    simp -failIfUnchanged (disch := decide) only [loadSeparate]
    simp only [b3,b12,b13,b14,b15,tag,small, and_true]
    refine Eq.trans (ite_eq_left ?_) ?_
    · first | slot_guard using code_l11c4cc | exact ⟨by slot_guard using code_l11c4cc, trivial⟩
    · rfl
  case post =>
    refine ⟨rfl,?_,?_,?_,?_⟩
    · stack_addresses; rfl
    · unfold copied <;> stack_addresses <;> rfl
    · have eq64 (i : Fin Reg.count) (hi : i.val ∈ [3,12,13,14,15]) :
          (⟨64,old[i].get 64⟩ : Value) = old[i] := by
        have h := widths i hi
        generalize old[i] = v at h ⊢
        cases v with | mk n x => cases h; rfl
      rintro ⟨i,hi⟩ hm
      refine Eq.trans ?_ (eq64 _ hm)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl|rfl <;> rfl
    · rintro ⟨i,_⟩ hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem sameWrites (sp : W) : RegionsWithin (writes sp) (writes sp) :=
  fun r h => ⟨r,h,Nat.le_refl _,Nat.le_refl _⟩

set_option maxHeartbeats 600000 in
private theorem copyRun {a : Regs} {m : Ram} {sp : W} {s : Nat}
    (rsp : a[4].get 64 = sp-144) (src : a[6].get 64 = sp-64) (dst : a[7].get 64 = sp-128)
    (words : WordsAt m (sp-64) 64 (scalarWords s)) (bound : s < domain.n)
    (ret : memLoad m (sp-144) 64 = 0x104d56)
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,12,13,14,15] → a[i].width = 64)
    (win : Writable Extracted.programImage m (sp-464) 464)
    (room : 464 ≤ sp.toNat) (high : sp.toNat+264 < 2^32) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l11c3f0,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,0x104d56#64⟩ ∧ out.values[4] = ⟨64,sp-136⟩ ∧
      WordsAt out.store (sp-128) 64 (scalarWords s) ∧ RamWriteFrame m out.store (writes sp) ∧
      (∀ i : Fin Reg.count, i.val ∈ copyKept → out.values[i] = a[i]) := by
  obtain ⟨b,jump,bKeep⟩ := copyJump a m
  have breg (i : Fin Reg.count) (hi : i.val ∈ (([4,6,7,12,15] ++ kept) : List Nat)) :
      b[i].get 64 = a[i].get 64 := congrArg (Value.get 64) (bKeep i hi)
  obtain ⟨c,pre,call,csp,cone,c3,c14,c15,c12,c13,cKeep,preFrame,p3,p12,p13,p14,p15,preRet⟩ :=
    borrowBlock ((breg 4 (by decide)).trans rsp) ((breg 6 (by decide)).trans src)
      ((breg 7 (by decide)).trans dst) words (borrowOne bound) win room high
  have preWin := win.of_frame preFrame
  have work : Writable Extracted.programImage pre (sp-200-8-1) 1 := by
    rw [show sp-200-8-1 = sp-209 by bv_omega]
    exact stackSub preWin 209 1 (by decide) (by decide)
  have slot : Readable pre (sp-200-8) 8 := by
    rw [show sp-200-8 = sp-208 by bv_omega]
    exact (stackSub preWin 208 8 (by decide) (by decide)).readable
  obtain ⟨d,n,resume,dsp,d0,choiceFrame,dKeep⟩ :=
    Verify.resumeChoice call (congrArg (Value.get 64) csp) work slot (by decide)
  have one : d[0] = ⟨64,1#64⟩ := by rw [d0,cone]; rfl
  have preToN : RamWriteFrame pre n (writes sp) := by
    refine ((RamWriteFrame.refl pre _).memStore (0x11c4c4 : W) ?_).trans choiceFrame ?_
    · rw [show sp-200-8 = sp-208 by bv_omega]
      exact stackSlot room high _ _ (by decide) (by decide) (by decide)
    · intro reg hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨_,List.mem_singleton_self _,?_⟩
      change (sp-464).toNat ≤ (sp-200-8-1).toNat ∧ (sp-200-8-1).toNat + 1 ≤ (sp-464).toNat+432
      rw [show sp-200-8-1 = sp-209 by bv_omega]
      stack_bounds
  have nWin := preWin.of_frame preToN
  obtain ⟨e,branch,esp,e3,e12,e13,e14,e15,eKeep⟩ :=
    copyBranch (congrArg (Value.get 64) dsp) one nWin room high
  let q := memStore n (sp-193) (1 : BitVec 8)
  have qFrame : RamWriteFrame pre q (writes sp) :=
    preToN.memStore 1 (stackSlot room high 193 1 (by decide) (by decide) (by decide))
  have fromPre {off : W} (lo : 144 ≤ off.toNat) (hi : off.toNat ≤ 184) :
      memLoad q (sp-off) 64 = memLoad pre (sp-off) 64 := by
    have offset : (sp-off).toNat = sp.toNat-off.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    have off193 : (sp-193).toNat = sp.toNat-193 :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 193 ≤ sp.toNat; omega))
    have off208 : (sp-208).toNat = sp.toNat-208 :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 208 ≤ sp.toNat; omega))
    change memLoad (memStore n (sp-193) (1 : BitVec 8)) (sp-off) 64 = _
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
      apply RangeApart.of_toNat <;> simp only [off193, offset, Nat.reduceDiv] <;> omega)]
    have readPush : memLoad (memStore pre (sp-200-8) (0x11c4c4 : W)) (sp-off) 64 =
        memLoad pre (sp-off) 64 := by
      apply memLoad_memStore_of_rangeApart
      rw [show sp-200-8 = sp-208 by bv_omega]
      apply RangeApart.of_toNat <;> simp only [off208, offset, Nat.reduceDiv] <;> omega
    rw [← readPush]
    apply choiceFrame.memLoad_eq
    refine ⟨by rw [offset]; stack_bounds,fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    rw [show sp-200-8-1 = sp-209 by bv_omega, offset]
    stack_bounds
  have dp (i : Fin Reg.count) (hi : i.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51]) :
      d[i] = c[i] := dKeep i hi
  have ba (i : Fin Reg.count) (hi : i.val ∈ [3,12,13,14,15]) : b[i] = a[i] := by
    apply bKeep
    simp only [kept,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega
  have bw (i : Fin Reg.count) (hi : i.val ∈ [3,12,13,14,15]) : b[i].width = 64 := by
    rw [ba i hi]
    exact widths i hi
  obtain ⟨out,finish,tag,outSp,mem,outPop,outKeep⟩ := copyReturn
    (congrArg (Value.get 64) (esp.trans dsp)) (congrArg (Value.get 64) (e3.trans ((dp 3 (by decide)).trans c3)))
    (congrArg (Value.get 64) (e14.trans ((dp 14 (by decide)).trans c14)))
    (congrArg (Value.get 64) (e15.trans ((dp 15 (by decide)).trans c15)))
    (congrArg (Value.get 64) (e12.trans ((dp 12 (by decide)).trans c12)))
    (congrArg (Value.get 64) (e13.trans ((dp 13 (by decide)).trans c13)))
    ((fromPre (by decide) (by decide)).trans p3) ((fromPre (by decide) (by decide)).trans p12)
    ((fromPre (by decide) (by decide)).trans p13) ((fromPre (by decide) (by decide)).trans p14)
    ((fromPre (by decide) (by decide)).trans p15) ((fromPre (by decide) (by decide)).trans (preRet.trans ret))
    bw (preWin.of_frame qFrame) room high
  have run : program.Exec (dialect Extracted.programImage) ⟨⟨.l11c4cc,e,q⟩,[]⟩ out :=
    .done (by simp only [Program.step,finish,Transfer.next])
  have stepped : (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l11c3f0,a,m⟩,[]⟩ ⟨⟨.l11c400,b,m⟩,[]⟩ :=
    .single (by simp only [Program.sem,Program.step,jump,Transfer.next])
  have branched : (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l11c4c4,d,n⟩,[]⟩ ⟨⟨.l11c4cc,e,q⟩,[]⟩ :=
    .single (by simp only [Program.sem,Program.step,branch,Transfer.next,q])
  refine ⟨out,Program.Exec.of_sem ((stepped.trans (resume.trans branched)).exec run.sem),tag,outSp,
    mem.symm ▸ copied_words q sp _,?_,?_⟩
  · rw [mem]
    unfold copied
    iterate 4 apply RamWriteFrame.memStore _ _ (stackSlot room high _ _ (by decide) (by decide) (by decide))
    exact preFrame.trans qFrame (sameWrites sp)
  · intro i hi
    by_cases h : i.val ∈ [3,12,13,14,15]
    · exact (outPop i h).trans (ba i h)
    · have h' : i.val ∈ [5,22,39,50,51] := by
        simp only [copyKept,List.mem_cons,List.not_mem_nil,or_false] at hi h ⊢
        omega
      refine (outKeep i h').trans ((eKeep i h').trans ((dp i ?_).trans ((cKeep i h').trans (bKeep i ?_))))
      all_goals
        simp only [kept,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at h' ⊢
        omega

private def fillUnused (a : Regs) : Regs :=
  Vector.ofFn fun i => if i.val = 1 ∨ i.val = 8 ∨ i.val = 9 then ⟨64,0#64⟩ else a[i]

private theorem filledGet (a : Regs) (i : Fin Reg.count) :
    (fillUnused a)[i] = if i.val = 1 ∨ i.val = 8 ∨ i.val = 9 then ⟨64,0#64⟩ else a[i] := by
  simp only [fillUnused, Fin.getElem_fin, Vector.getElem_ofFn] <;> rfl

private theorem filledKeep (a : Regs) (i : Fin Reg.count) (h : ¬ (i.val = 1 ∨ i.val = 8 ∨ i.val = 9)) :
    (fillUnused a)[i] = a[i] := (filledGet a i).trans (ite_eq_right h)

private theorem filledClear (a : Regs) (i : Fin Reg.count) (h : i.val = 1 ∨ i.val = 8 ∨ i.val = 9) :
    (fillUnused a)[i] = ⟨64,0#64⟩ := (filledGet a i).trans (ite_eq_left h)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem negateRunBlock (a : Regs) (m : Ram) :
    program.runBlock (dialect Extracted.programImage) ⟨.l110b80,a,m⟩ =
      program.runBlock (dialect Extracted.programImage) ⟨.l110b80,fillUnused a,m⟩ := by
  cfg_eval [b_l110b80_1,b_l110b80_2,b_l110b80_3,b_l110b80_4,fillUnused,Fin.getElem_fin,Vector.getElem_ofFn, Fin.val_ofNat, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, true_or]
  simp -failIfUnchanged only [Vector.getElem_ofFn, Nat.reduceEqDiff, or_false, ↓reduceIte]

set_option maxHeartbeats 800000 in
theorem negate {fr : Activation} {a : Verify.Core.Registers} {r s : Nat}
    (input : Inputs fr r s) {m : Ram} (saved : Saved fr a m) :
    ∃ b n, Verify.Core.Reaches .l104d10 a m .l104d56 b n ∧ Saved fr b n ∧
      b[15].get 64 = fr.rsi + 32 ∧ WordsAt n (fr.rsp - 128) 64 (scalarWords (domain.n - s)) := by
  let sp := fr.rsp
  have room : 464 ≤ sp.toNat := input.room
  have high : sp.toNat + 264 < 2^32 := input.high
  have frLow : fr.low = sp-464 := input.low
  have spNat (off : W) (depth : off.toNat ≤ 464) :
      (sp-off).toNat = sp.toNat-off.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have within : RegionsWithin (writes sp) [fr.region] := by
    intro reg h
    obtain rfl := List.mem_singleton.mp h
    refine ⟨fr.region,List.mem_singleton_self _,?_⟩
    simp only [Activation.region,frLow,spNat 464 (by decide),BitVec.reduceToNat]
    change sp.toNat - 464 ≤ sp.toNat - 464 ∧
      sp.toNat - 464 + 432 ≤ sp.toNat - 464 + (sp.toNat - (sp.toNat - 464))
    omega
  have atoms := saved.atoms
  simp only [Fn104c90.frameAt,Fn104c90.frameAtG5,Atom.All,Atom.Holds] at atoms
  obtain ⟨rsp,df,bx,bp,r13,r14,mx,ft,fc,b3,b12,b14,b15,retRead,ret,small,stack,space,align,_⟩ := atoms
  have win : Writable Extracted.programImage m (sp-464) 464 := stack
  have sPtr : fr.rsi+32 = sp+232 := by rw [input.src]; change sp+200+32 = sp+232; bv_omega
  have read : Readable m (sp+232) 32 := by
    apply (input.read.of_frame saved.frame).of_offsets
    · rfl
    · exact input.src
    · decide
  have sw := (input.words_of_frame saved.frame).2
  rw [sPtr] at sw
  have a14 : a[14].get 64 = sp+200 := (congrArg (Value.get 64) r14).trans input.src
  obtain ⟨b,push,bsp,bsi,bdi,breg12,breg15,bKeep⟩ :=
    stageBlock (congrArg (Value.get 64) rsp) a14 read sw win room high
  let pre := stage m sp (scalarWords s)
  have preFrame : RamWriteFrame m pre (writes sp) := by
    unfold pre stage
    repeat' apply RamWriteFrame.memStore _ _ (stackSlot room high _ _ (by decide) (by decide) (by decide))
    exact .refl _ _
  have preWin := win.of_frame preFrame
  obtain ⟨c,modulus,cdx,cKeep⟩ := modulusBlock b pre
  have cs (i : Fin Reg.count) (hi : i.val ∈ kept) : c[i] = a[i] := by
    refine (cKeep i ?_).trans (bKeep i hi)
    simp only [kept,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega
  let child := {fr with
    original := pre, rsp := sp-144, low := sp-192,
    ret := 0x104d49, rsi := sp-128, rdi := sp-64, rdx := 0x2021a0,
    rcx := 0, r8 := 0, r9 := 0, rbx := fr.rdi, r12 := sp-64, r14 := fr.rsi, r15 := sp+232}
  have childWin : Writable Extracted.programImage pre (child.rsp-48) 48 := by
    change Writable _ _ (sp-144-48) 48
    rw [show sp-144-48 = sp-192 by bv_omega]
    exact stackSub preWin 192 48 (by decide) (by decide)
  have childAtoms : Atom.All Extracted.programImage (fillUnused c) pre
      (Generate.LIR.Fn110b80.frameAt .l110b80 child) := by
    simp only [Generate.LIR.Fn110b80.frameAt,Generate.LIR.Fn110b80.frameAtG1,Atom.All,Atom.Holds]
    have retSmall : child.ret.toNat < 2^32 := by change (0x104d49 : W).toNat < 2^32; decide
    have retWord : memLoad pre child.rsp 64 = child.ret := loadStored64 _ _ _
    have fit : child.low.toNat+48 ≤ child.rsp.toNat := by
      change (sp-192).toNat+48 ≤ (sp-144).toNat
      stack_bounds
    have aligned : child.rsp.toNat % 16 = 8 := by
      change (sp-144).toNat % 16 = 8
      change sp.toNat % 16 = 8 at align
      stack_bounds
    refine ⟨(filledKeep c 4 (by decide)).trans ((cKeep 4 (by decide)).trans bsp),
      (filledKeep c 22 (by decide)).trans ((cs 22 (by decide)).trans df),
      filledClear c 1 (by decide), (filledKeep c 2 (by decide)).trans cdx,
      (filledKeep c 3 (by decide)).trans ((cs 3 (by decide)).trans bx),
      (filledKeep c 5 (by decide)).trans ((cs 5 (by decide)).trans bp),
      (filledKeep c 6 (by decide)).trans ((cKeep 6 (by decide)).trans bsi),
      (filledKeep c 7 (by decide)).trans ((cKeep 7 (by decide)).trans bdi),
      filledClear c 8 (by decide), filledClear c 9 (by decide),
      (filledKeep c 12 (by decide)).trans ((cKeep 12 (by decide)).trans breg12),
      (filledKeep c 13 (by decide)).trans ((cs 13 (by decide)).trans r13),
      (filledKeep c 14 (by decide)).trans ((cs 14 (by decide)).trans r14),
      (filledKeep c 15 (by decide)).trans ((cKeep 15 (by decide)).trans breg15),
      (filledKeep c 39 (by decide)).trans ((cs 39 (by decide)).trans mx),
      (filledKeep c 50 (by decide)).trans ((cs 50 (by decide)).trans ft),
      (filledKeep c 51 (by decide)).trans ((cs 51 (by decide)).trans fc),
      (stackSub preWin 144 8 (by decide) (by decide)).readable, retWord, retSmall, childWin, fit,
      aligned,trivial⟩
  have loaded : ∀ b ∈ Extracted.programImage, pre[b.1]? = some b.2 := by
    have frame := saved.frame.trans preFrame within
    intro b hb
    apply (frame.outside b.1 ?_).trans (input.image b hb)
    refine ⟨by have := b.1.isLt; omega, fun reg hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change b.1.toNat+1 ≤ fr.low.toNat ∨ fr.low.toNat+(sp.toNat-fr.low.toNat) ≤ b.1.toNat
    rw [frLow,spNat 464 (by decide)]
    simp only [BitVec.reduceToNat]
    apply Classical.byContradiction
    intro h
    obtain ⟨hlo,hhi⟩ := not_or.mp h
    have lo : sp.toNat-464 ≤ b.1.toNat := by omega
    have hi : b.1.toNat - (sp.toNat-464) < 464 := by omega
    apply win.notCode b hb _ hi
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, spNat 464 (by decide)]
    simp only [BitVec.reduceToNat]
    have := b.1.isLt
    omega
  have aboveSrc : child.rsp.toNat+8 ≤ child.rsi.toNat := by dsimp only [child]; stack_bounds
  have aboveDst : child.rsp.toNat+8 ≤ child.rdi.toNat := by dsimp only [child]; stack_bounds
  have apart : child.rsi.toNat+32 ≤ child.rdi.toNat ∨ child.rdi.toNat+32 ≤ child.rsi.toNat := by
    dsimp only [child]; stack_bounds
  obtain ⟨out,run,tag,done_,_,childFrame,negWords⟩ :=
    Generate.Generator.Multiply.Prepare.scalarNegCall childAtoms loaded
      (stackSub preWin 128 32 (by decide) (by decide)).readable
      (stackSub preWin 64 32 (by decide) (by decide)) aboveSrc aboveDst apart rfl input.sBound
      (stage_words m sp _)
  have runFilled : program.Exec (dialect Extracted.programImage) ⟨⟨.l110b80,fillUnused c,pre⟩,[]⟩ out :=
    Generate.Serialize.Relabel.exec negateBlocks run rfl
  have runNeg : program.Exec (dialect Extracted.programImage) ⟨⟨.l110b80,c,pre⟩,[]⟩ out := by
    cases runFilled with
    | done run =>
      exact .done (by simpa only [Program.step,negateRunBlock c pre] using run)
    | next run rest =>
      exact .next (by simpa only [Program.step,negateRunBlock c pre] using run) rest
  have modStep : (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l10a2d0,b,pre⟩,[]⟩ ⟨⟨.l110b80,c,pre⟩,[]⟩ :=
    .single (by simp only [Program.sem,Program.step,modulus,Transfer.next])
  have reached := Verify.reachesOfCall push (Program.Exec.of_sem (modStep.exec runNeg.sem)) tag
  have delta := preFrame.trans childFrame (by
    intro reg h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    refine ⟨_,List.mem_singleton_self _,?_⟩
    rcases h with h | h
    · subst reg
      change (sp-464).toNat ≤ (sp-144).toNat-48 ∧ (sp-144).toNat-48+48 ≤ (sp-464).toNat+432
      rw [spNat 464 (by decide),spNat 144 (by decide)]
      simp only [BitVec.reduceToNat]
      omega
    · subst reg
      change (sp-464).toNat ≤ (sp-64).toNat ∧ (sp-64).toNat+32 ≤ (sp-464).toNat+432
      rw [spNat 464 (by decide),spNat 64 (by decide)]
      simp only [BitVec.reduceToNat]
      omega)
  have outWin := win.of_frame delta
  have vals := done_
  simp only [Generate.LIR.Fn110b80.doneAt,Atom.All,Atom.Holds] at vals
  obtain ⟨outSp,outDf,outBx,outBp,out12,out13,out14,out15,outMx,outFt,outFc,_⟩ := vals
  rw [show child.rsp + 8 = sp-136 by change sp-144+8 = sp-136; bv_omega] at outSp
  obtain ⟨d,copy,dsp,dsi,ddi,dKeep⟩ :=
    copySetup (congrArg (Value.get 64) outSp) (congrArg (Value.get 64) out12) outWin room high
  let pushed := memStore out.store (sp-144) (0x104d56 : W)
  have pushedFrame : RamWriteFrame m pushed (writes sp) :=
    delta.memStore (0x104d56 : W) (stackSlot room high 144 8 (by decide) (by decide) (by decide))
  have pushedWords : WordsAt pushed (sp-64) 64 (scalarWords (domain.n-s)) := by
    have h : WordsAt out.store (sp-64) 64 (scalarWords (domain.n-s)) := by
      simpa only [ite_eq_right (Nat.ne_of_gt input.sPos)] using negWords
    exact h.write_apart _ _ (RangeApart.of_offsets (addr_sub sp 144) (addr_sub sp 64) (by decide))
  have pushedWidths (i : Fin Reg.count) (hi : i.val ∈ [3,12,13,14,15]) : d[i].width = 64 := by
    have use : i.val ∈ 15 :: 12 :: kept := by
      simp only [kept,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega
    rw [dKeep i use]
    rcases i with ⟨i,hi'⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · exact congrArg Value.width outBx
    · exact congrArg Value.width out12
    · exact congrArg Value.width out13
    · exact congrArg Value.width out14
    · exact congrArg Value.width out15
  obtain ⟨last,exec,tag',stack',words,changed,lastKeep⟩ :=
    copyRun (congrArg (Value.get 64) dsp) (congrArg (Value.get 64) dsi) (congrArg (Value.get 64) ddi)
      pushedWords (by have := input.sPos; have := input.sBound; omega)
      (memLoad_memStore_same _ _ _ (by decide) (by decide))
      pushedWidths (win.of_frame pushedFrame) room high
  have total := pushedFrame.trans changed (sameWrites sp)
  have getSaved {off : W} (h : off.toNat ≤ 32) :
      memLoad last.store (sp-off) 64 = memLoad m (sp-off) 64 := by
    apply total.memLoad_eq
    refine ⟨by rw [spNat off (by omega)]; omega,fun reg hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    change (sp-464).toNat+432 ≤ (sp-off).toNat
    rw [spNat 464 (by decide),spNat off (by omega)]
    simp only [BitVec.reduceToNat] at *
    omega
  have lastFromOut (i : Fin Reg.count) (hi : i.val ∈ kept) : last.values[i] = out.values[i] := by
    refine (lastKeep i ?_).trans (dKeep i ?_)
    all_goals
      simp only [copyKept,kept,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega
  have sameRet := getSaved (off := 0) (by decide)
  rw [show sp-(0 : W) = sp by bv_omega] at sameRet
  have holds : Atom.All Extracted.programImage last.values last.store (Fn104c90.frameAt .l104d5e fr) :=
    ⟨stack',(lastFromOut 22 (by decide)).trans outDf,(lastFromOut 3 (by decide)).trans outBx,
      (lastFromOut 5 (by decide)).trans outBp,(lastFromOut 13 (by decide)).trans out13,
      (lastFromOut 14 (by decide)).trans out14,(lastFromOut 39 (by decide)).trans outMx,
      (lastFromOut 50 (by decide)).trans outFt,(lastFromOut 51 (by decide)).trans outFc,
      (getSaved (by decide)).trans b3,(getSaved (by decide)).trans b12,(getSaved (by decide)).trans b14,
      (getSaved (by decide)).trans b15,retRead.of_frame total,sameRet.trans ret,small,win.of_frame total,
      space,align,trivial⟩
  refine ⟨last.values,last.store,reached.trans (Verify.reachesOfCall copy exec tag'),
    ⟨holds,saved.frame.trans total within⟩,?_ ,words⟩
  rw [sPtr]
  exact congrArg (Value.get 64) (((lastKeep 15 (by decide)).trans (dKeep 15 (by decide))).trans out15)

end K256.Proofs.Signing.Scalar.Normalize
