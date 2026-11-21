import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.State
import K256.Proofs.Verify.Core.Lincomb.Recode.Memory
import K256.Proofs.Verify.Choice
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.State
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Multiply.Prepare (highBit)
open Generate.Curve

private def comparisonSlots (base : BitVec 64) : List MemoryRegion :=
  [⟨base.toNat, 0x28⟩, ⟨(base + 0x30).toNat, 0xa8⟩]

private theorem slotNat {base off : BitVec 64} (h : base.toNat + off.toNat < 2^64) :
    (base + off).toNat = base.toNat + off.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

private theorem inComparisonSlot {base off : BitVec 64} (low : base.toNat + 0xd8 ≤ 2^32)
    (fit : off.toNat + 8 ≤ 0x28 ∨ (0x30 ≤ off.toNat ∧ off.toNat + 8 ≤ 0xd8)) :
    InRegions (comparisonSlots base) (base + off) 8 := by
  have addr := slotNat (base := base) (off := off) (by omega)
  have mid : (base + 0x30).toNat = base.toNat + 48 := slotNat (by change base.toNat + 48 < 2^64; omega)
  rcases fit with h | h
  · refine ⟨_, .head _, ?_⟩
    simp only [InRegion, addr]
    omega
  · refine ⟨_, .tail _ (.head _), ?_⟩
    simp only [InRegion, addr, mid]
    omega

private abbrev choiceKept (a b : Registers) :=
  ∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51] → b[i] = a[i]

private theorem comparisonAccess {a : Registers} {m n : Ram} {sp : BitVec 64}
    (entry : RoutineEntry a m sp 0x558) (s : RamWriteFrame m n [scratch sp 0x558]) :
    Writable Extracted.programImage n (frameSp sp) 0x100 ∧
    Writable Extracted.programImage n (frameSp sp - 8) 8 ∧
    Writable Extracted.programImage n (frameSp sp - 8 - 1) 1 := by
  have window {off : BitVec 64} {len : Nat} (lower : off.toNat ≤ 0x558) (upper : len ≤ off.toNat) :=
    (Recode.stackSlot entry lower upper).of_frame s
  refine ⟨window (off := 696) (by decide) (by decide), ?_, ?_⟩
  · rw [show frameSp sp - 8 = sp - 704 by bv_omega]
    exact window (off := 704) (by decide) (by decide)
  · rw [show frameSp sp - 8 - 1 = sp - 705 by bv_omega]
    exact window (off := 705) (by decide) (by decide)

private theorem comparisonMem {a : Registers} {m : Ram} {sp : BitVec 64}
    (entry : RoutineEntry a m sp 0x558) {pre n o : Ram} {ret : BitVec 64}
    (localFrame : RamWriteFrame n pre (comparisonSlots (frameSp sp)))
    (pushedFrame : RamWriteFrame (memStore pre (frameSp sp - 8) ret) o
      [⟨(frameSp sp - 8 - 1).toNat,1⟩]) :
    RamWriteFrame pre o [scratch (frameSp sp) 9] ∧
    RamWriteFrame n o (scratch (frameSp sp) 9 :: comparisonSlots (frameSp sp)) := by
  have room := entry.room
  have base : (frameSp sp).toNat = sp.toNat - 696 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 696 ≤ sp.toNat; omega))
  have push : (frameSp sp - 8).toNat = (frameSp sp).toNat - 8 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 8 ≤ (frameSp sp).toNat; omega))
  have tmp : (frameSp sp - 8 - 1).toNat = (frameSp sp).toNat - 9 := by
    rw [show frameSp sp - 8 - 1 = frameSp sp - 9 by bv_omega]
    exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 9 ≤ (frameSp sp).toNat; omega))
  have below : RamWriteFrame pre o [scratch (frameSp sp) 9] := by
    refine ((RamWriteFrame.refl _ _).memStore ret ⟨_, .head _, ?_⟩).trans pushedFrame ?_
    · simp only [InRegion, scratch, push]
      have := sp.isLt
      omega
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, .head _, by simp only [scratch, tmp]; omega⟩
  have extend : RamWriteFrame n pre (scratch (frameSp sp) 9 :: comparisonSlots (frameSp sp)) :=
    ⟨fun x h => localFrame.outside x ⟨h.1, fun r hr => h.2 r (.tail _ hr)⟩, localFrame.present⟩
  refine ⟨below, extend.trans below ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, .head _, Nat.le_refl _, Nat.le_refl _⟩

private theorem advanceComparison {a b c : Registers} {m n o : Ram} {sp src tables digits : BitVec 64}
    (entry : RoutineEntry a m sp 0x558) (s : SplitFrame a m sp src tables digits b n)
    (foot : RamWriteFrame n o (scratch (frameSp sp) 9 :: comparisonSlots (frameSp sp)))
    (rsp : c[4] = ⟨64, frameSp sp⟩) (table : c[3] = b[3])
    (control : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i])
    (saved : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → c[i].width = 64)
    (args : ParseSignature.ArgumentWidths c) : SplitFrame a m sp src tables digits c o := by
  have room := entry.room
  have limit := entry.returnSlot.low
  have base : (frameSp sp).toNat = sp.toNat - 696 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 696 ≤ sp.toNat; omega))
  have mid : (frameSp sp + 0x30).toNat = (frameSp sp).toNat + 48 := slotNat (by change (frameSp sp).toNat + 48 < 2^64; omega)
  have outside (q : BitVec 64)
      (apart : q.toNat = (frameSp sp).toNat + 40 ∨
        (q.toNat ≥ (frameSp sp).toNat + 216 ∧ q.toNat + 8 ≤ sp.toNat)) :
      Outside (scratch (frameSp sp) 9 :: comparisonSlots (frameSp sp)) q 8 := by
    refine ⟨by omega, ?_⟩
    intro r hr
    simp only [comparisonSlots, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only [scratch] <;> omega
  have slot (off : BitVec 64) (h : off = 0x28 ∨ off = 0xd8) :
      memLoad o (frameSp sp + off) 64 = memLoad n (frameSp sp + off) 64 := by
    have offNat : off.toNat = 40 ∨ off.toNat = 216 := by rcases h with rfl | rfl <;> decide
    have addr := slotNat (base := frameSp sp) (off := off) (by omega)
    exact foot.memLoad_eq (outside _ (by omega))
  have preserve (off : BitVec 64) (lo : 8 ≤ off.toNat) (hi : off.toNat ≤ 48) :
      memLoad o (sp - off) 64 = memLoad n (sp - off) 64 := by
    have addr := BitVec.toNat_sub_of_le (x := sp) (y := off) (BitVec.le_def.mpr (by omega))
    exact foot.memLoad_eq (outside _ (by omega))
  refine ⟨⟨rsp,table.trans s.tableBase,saved,fun i h => (control i h).trans (s.control i h),
    (preserve 48 (by decide) (by decide)).trans s.rbx,
    (preserve 40 (by decide) (by decide)).trans s.r12,
    (preserve 32 (by decide) (by decide)).trans s.r13,
    (preserve 24 (by decide) (by decide)).trans s.r14,
    (preserve 16 (by decide) (by decide)).trans s.r15,
    (preserve 8 (by decide) (by decide)).trans s.rbp⟩,
    s.frame.trans foot ?_, (slot 0x28 (.inl rfl)).trans s.pointPtr,
    (slot 0xd8 (.inr rfl)).trans s.digitPtr,args⟩
  intro r hr
  simp only [comparisonSlots, List.mem_cons, List.not_mem_nil, or_false] at hr
  refine ⟨_,.head _,?_⟩
  rcases hr with rfl | rfl | rfl <;> dsimp only [scratch] <;> omega

private theorem comparisonReturn {a b c : Registers} {m n pre : Ram} {sp src tables digits ret : BitVec 64}
    {site next : Label} {sign : Int}
    (entry : RoutineEntry a m sp 0x558) (s : SplitFrame a m sp src tables digits b n)
    (call : program.runBlock (dialect Extracted.programImage) ⟨site,b,n⟩ =
      .call ⟨.l127d50,c,memStore pre (frameSp sp - 8) ret⟩ (Verify.resumeAt next ret))
    (rsp : c[4].get 64 = frameSp sp - 8)
    (flag : c[7] = ⟨64, (signByte sign).setWidth 64⟩)
    (localFrame : RamWriteFrame n pre (comparisonSlots (frameSp sp)))
    (table : c[3] = b[3])
    (control : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i])
    (saved : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → c[i].width = 64)
    (args : ParseSignature.ArgumentWidths c) (small : ret.toNat < 2^32) :
    ∃ d o, Reaches site b n next d o ∧ SplitFrame a m sp src tables digits d o ∧
      d[0] = ⟨64,(signByte sign).setWidth 64⟩ ∧
      RamWriteFrame pre o [scratch (frameSp sp) 9] ∧ choiceKept c d := by
  obtain ⟨_, slot, work⟩ := comparisonAccess entry s.frame
  obtain ⟨d,o,path,stack,byte,changes,keep⟩ :=
    Verify.resumeChoice call rsp (work.of_frame localFrame) (slot.readable.of_frame localFrame) small
  obtain ⟨below,whole⟩ := comparisonMem entry localFrame changes
  have ctl : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → d[i] = b[i] :=
    fun i hi => (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (control i hi)
  have sw : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → d[i].width = 64 :=
    fun i hi => (congrArg Value.width (keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))).trans (saved i hi)
  have aw : ParseSignature.ArgumentWidths d :=
    fun i hi => (congrArg Value.width (keep i (by simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega))).trans (args i hi)
  refine ⟨d,o,path,advanceComparison entry s whole stack ((keep 3 (by decide)).trans table)
    ctl sw aw,?_,below,keep⟩
  rw [byte,flag]
  unfold signByte
  split <;> rfl

private theorem keepAboveChoice {base off : BitVec 64} (low : base.toNat + 0x100 ≤ 2^32)
    (room : 9 ≤ base.toNat) (small : off.toNat ≤ 0xd8) {pre o : Ram}
    (frame : RamWriteFrame pre o [scratch base 9]) :
    memLoad o (base + off) 64 = memLoad pre (base + off) 64 := by
  have addr := slotNat (base := base) (off := off) (by omega)
  apply frame.memLoad_eq
  refine ⟨by rw [addr]; omega, ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  right
  simp only [scratch, addr]
  omega

private theorem comparisonFlag {x : Nat} (bound : x < domain.n) :
    let w := scalarWords x
    let z := (highBit w[0] w[1] w[2] w[3]).extractLsb' 0 8
    (⟨64, ((mergeGPR 8 (z &&& 1) (z.setWidth 64)).setWidth 8).setWidth 64⟩ : Value) =
      ⟨64,(signByte (centered x)).setWidth 64⟩ := by
  dsimp only
  rw [Generate.Generator.Multiply.Prepare.Bases.highBit_scalar bound]
  unfold Generate.Generator.Multiply.Prepare.Bases.flag signByte
  by_cases h : centered x < 0 <;> simp only [h, ite_true, ite_false] <;> rfl

private structure FirstCompared (a : Registers) (m : Ram) (sp src tables digits : BitVec 64)
    (k : Nat) (b : Registers) (n : Ram) : Prop extends SplitFrame a m sp src tables digits b n where
  sign : b[0] = ⟨64,(signByte (first k)).setWidth 64⟩
  halfLow : b[13].get 64 = 0xdfe92f46681b20a0
  zero15 : b[15].get 64 = 0
  low : b[14].get 64 = (scalarWords (splitSecond k))[0]
  midLow : b[12].get 64 = (scalarWords (splitSecond k))[1]
  midHigh : b[5].get 64 = (scalarWords (splitSecond k))[2]
  high : memLoad n (frameSp sp + 0xd0) 64 = (scalarWords (splitSecond k))[3]
  firstWords : WordsAt n (frameSp sp + 8) 64 (scalarWords (splitFirst k))

local macro "comparison_controls" : tactic => `(tactic| (
  rintro ⟨i,hi⟩ h
  change i ∈ [22,39,50,51] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h <;> subst i <;> rfl))

local macro "comparison_saved " s:ident : tactic => `(tactic| (
  rintro ⟨i,hi⟩ h
  have wid := $s ⟨i,hi⟩ h
  change i ∈ [3,5,12,13,14,15] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h | h <;> subst i <;> first | rfl | exact wid))

local macro "comparison_arguments " s:ident : tactic => `(tactic| (
  rintro ⟨i,hi⟩ h
  have wid := $s ⟨i,hi⟩ h
  change i ∈ Activation.argumentNumbers at h
  simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h | h <;> subst i <;> first | rfl | exact wid))

private theorem preserveFirstWords {base : BitVec 64} {pre o : Ram} {w : Vector (BitVec 64) 4}
    (low : base.toNat + 0x100 ≤ 2^32) (room : 9 ≤ base.toNat)
    (frame : RamWriteFrame pre o [scratch base 9])
    (words : WordsAt pre (base + 8) 64 w) : WordsAt o (base + 8) 64 w := by
  intro i hi
  have atWord := words i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  all_goals
    simp only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,
      BitVec.reduceAdd,BitVec.add_zero] at atWord ⊢
    exact (keepAboveChoice low room (by decide) frame).trans atWord

private def comparisonOperand (bits : BitVec 64) : Value :=
  let z := bits.extractLsb' 0 8
  ⟨64, ((mergeGPR 8 (z &&& 1) (z.setWidth 64)).setWidth 8).setWidth 64⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem compareFirstBlock {b : Registers} {n : Ram} {base : BitVec 64}
    {u v : Vector (BitVec 64) 4} (rsp : b[4].get 64 = base)
    (firstWords : WordsAt n (base + 0x38) 64 u) (secondWords : WordsAt n (base + 0xb0) 64 v)
    (win : Writable Extracted.programImage n base 0x100)
    (push : Writable Extracted.programImage n (base - 8) 8)
    (savedWidths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → b[i].width = 64)
    (argWidths : ParseSignature.ArgumentWidths b) :
    ∃ c pre,
      program.runBlock (dialect Extracted.programImage) ⟨.l10f221,b,n⟩ =
        .call ⟨.l127d50,c,memStore pre (base - 8) (0x10f326 : BitVec 64)⟩ (Verify.resumeAt .l10f326 0x10f326) ∧
      c[4].get 64 = base - 8 ∧
      c[7] = comparisonOperand (highBit u[0] u[1] u[2] u[3]) ∧
      RamWriteFrame n pre (comparisonSlots base) ∧ c[3] = b[3] ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i]) ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → c[i].width = 64) ∧
      ParseSignature.ArgumentWidths c ∧
      c[13].get 64 = 0xdfe92f46681b20a0 ∧ c[15].get 64 = 0 ∧ c[14].get 64 = v[0] ∧
      c[12].get 64 = v[1] ∧ c[5].get 64 = v[2] ∧ memLoad pre (base + 0xd0) 64 = v[3] ∧
      WordsAt pre (base + 8) 64 u := by
  have u0 : memLoad n (base + 0x38) 64 = u[0] := by
    simpa only [wordAddr, Nat.mul_zero, BitVec.ofNat_eq_ofNat,BitVec.add_zero] using firstWords 0 (by decide)
  have u1 : memLoad n (base + 0x40) 64 = u[1] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using firstWords 1 (by decide)
  have u2 : memLoad n (base + 0x48) 64 = u[2] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using firstWords 2 (by decide)
  have u3 : memLoad n (base + 0x50) 64 = u[3] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using firstWords 3 (by decide)
  have v0 : memLoad n (base + 0xb0) 64 = v[0] := by
    simpa only [wordAddr,Nat.mul_zero, BitVec.ofNat_eq_ofNat,BitVec.add_zero] using secondWords 0 (by decide)
  have v1 : memLoad n (base + 0xb8) 64 = v[1] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using secondWords 1 (by decide)
  have v2 : memLoad n (base + 0xc0) 64 = v[2] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using secondWords 2 (by decide)
  have v3 : memLoad n (base + 0xc8) 64 = v[3] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using secondWords 3 (by decide)
  have low := win.readable.low
  have fit : base.toNat + 0xd8 ≤ 2^32 := by omega
  refine ⟨?c,?pre,?run,?sp,?sign,?foot,?table,?control,?saved,?args,?half,?zero15,?v0,?v1,?v2,?v3,?words⟩
  case run =>
    cfg_eval [rsp,u0,u1,u2,u3,v0,v1,v2,v3]
    segment_words [u0,u1,u2,u3,v0,v1,v2,v3]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10f221)
    rfl
  case sign => rfl
  case foot =>
    iterate 13
      refine RamWriteFrame.memStore ?_ _ ?_
      rotate_left
      exact inComparisonSlot fit (by decide)
    exact .refl _ _
  case control => comparison_controls
  case saved => comparison_saved savedWidths
  case args => comparison_arguments argWidths
  case v3 =>
    segment_words [] <;> rfl
  case words =>
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    all_goals
      simp only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,
        BitVec.reduceAdd,BitVec.add_zero]
      segment_words [] <;> rfl
  all_goals rfl

private theorem compareFirst {a b : Registers} {m n : Ram} {sp src tables digits : BitVec 64} {k : Nat}
    (entry : RoutineEntry a m sp 0x558) (s : Residues a m sp src tables digits k b n) :
    ∃ c o, Reaches .l10f221 b n .l10f326 c o ∧ FirstCompared a m sp src tables digits k c o := by
  let base := frameSp sp
  let u := scalarWords (splitFirst k)
  let v := scalarWords (splitSecond k)
  have rsp : b[4].get 64 = base := congrArg (Value.get 64) s.rsp
  obtain ⟨win,push,_⟩ := comparisonAccess entry s.frame
  change Writable Extracted.programImage n base 0x100 at win
  change Writable Extracted.programImage n (base - 8) 8 at push
  have low := win.readable.low
  have room : 9 ≤ base.toNat := by
    have available := entry.room
    have pos : base.toNat = sp.toNat - 696 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 696 ≤ sp.toNat; omega))
    omega
  obtain ⟨c,pre,call,rs,flag,foot,table,control,saved,args,half,zero15,mid0,mid1,mid2,high,words⟩ :=
    compareFirstBlock rsp s.firstWords s.secondWords win push s.widths s.arguments
  obtain ⟨d,o,path,frame,sign,below,keep⟩ :=
    comparisonReturn entry s.toSplitFrame call rs
      (flag.trans (comparisonFlag (Nat.mod_lt _ (by decide) : splitFirst k < domain.n)))
      foot table control saved args (by decide)
  exact ⟨d,o,path,frame,sign,(congrArg (Value.get 64) (keep 13 (by decide))).trans half,
    (congrArg (Value.get 64) (keep 15 (by decide))).trans zero15,
    (congrArg (Value.get 64) (keep 14 (by decide))).trans mid0,
    (congrArg (Value.get 64) (keep 12 (by decide))).trans mid1,
    (congrArg (Value.get 64) (keep 5 (by decide))).trans mid2,
    (keepAboveChoice low room (by decide) below).trans high, preserveFirstWords low room below words⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem compareSecondBlock {b : Registers} {n : Ram} {base firstFlag : BitVec 64}
    {u v : Vector (BitVec 64) 4} (rsp : b[4].get 64 = base)
    (r13 : b[13].get 64 = 0xdfe92f46681b20a0) (r14 : b[14].get 64 = v[0])
    (r12 : b[12].get 64 = v[1]) (r5 : b[5].get 64 = v[2])
    (v3 : memLoad n (base + 0xd0) 64 = v[3])
    (rax : b[0].get 64 = firstFlag) (r15 : b[15].get 64 = 0)
    (firstWords : WordsAt n (base + 8) 64 u)
    (win : Writable Extracted.programImage n base 0x100)
    (push : Writable Extracted.programImage n (base - 8) 8)
    (savedWidths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → b[i].width = 64)
    (argWidths : ParseSignature.ArgumentWidths b) :
    ∃ c pre,
      program.runBlock (dialect Extracted.programImage) ⟨.l10f326,b,n⟩ =
        .call ⟨.l127d50,c,memStore pre (base - 8) (0x10f3c5 : BitVec 64)⟩ (Verify.resumeAt .l10f3c5 0x10f3c5) ∧
      c[4].get 64 = base - 8 ∧
      c[7] = comparisonOperand (highBit v[0] v[1] v[2] v[3]) ∧
      RamWriteFrame n pre (comparisonSlots base) ∧ c[3] = b[3] ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i]) ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → c[i].width = 64) ∧
      ParseSignature.ArgumentWidths c ∧
      c[14].get 8 = ((firstFlag.setWidth 32).setWidth 64).setWidth 8 ∧ c[12].get 64 = v[1] ∧ c[5].get 64 = v[2] ∧
      c[13].get 64 = v[3] ∧ memLoad pre (base + 0x30) 64 = v[0] ∧ WordsAt pre (base + 8) 64 u := by
  have low := win.readable.low
  have fit : base.toNat + 0xd8 ≤ 2^32 := by omega
  refine ⟨?c,?pre,?run,?sp,?sign,?foot,?table,?control,?saved,?args,?firstSign,?v1,?v2,?v3,?v0,?words⟩
  case run =>
    cfg_eval [rsp, r13, r14, r12, r5, v3, rax, r15]
    segment_words [r13,r14,r12,r5,v3,rax,r15]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10f326)
    rfl
  case sign => rfl
  case foot =>
    iterate 5
      refine RamWriteFrame.memStore ?_ _ ?_
      rotate_left
      exact inComparisonSlot fit (by decide)
    exact .refl _ _
  case control => comparison_controls
  case saved => comparison_saved savedWidths
  case args => comparison_arguments argWidths
  case firstSign => rfl
  case v1 => exact r12
  case v2 => exact r5
  case v0 =>
    segment_words [] <;> rfl
  case words =>
    intro i hi
    have w := firstWords i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    all_goals
      simp only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,
        BitVec.reduceAdd,BitVec.add_zero] at w ⊢
      segment_words [] <;> exact w
  all_goals rfl

private theorem compareSecond {a b : Registers} {m n : Ram} {sp src tables digits : BitVec 64} {k : Nat}
    (entry : RoutineEntry a m sp 0x558) (s : FirstCompared a m sp src tables digits k b n) :
    ∃ c o, Reaches .l10f326 b n .l10f3c5 c o ∧ Signs a m sp src tables digits k c o := by
  let base := frameSp sp
  let u := scalarWords (splitFirst k)
  let v := scalarWords (splitSecond k)
  have rsp : b[4].get 64 = base := congrArg (Value.get 64) s.rsp
  have r13 := s.halfLow
  have r14 := s.low
  have r12 := s.midLow
  have r5 := s.midHigh
  have v3 : memLoad n (base + 0xd0) 64 = v[3] := s.high
  have rax : b[0].get 64 = (signByte (first k)).setWidth 64 := by rw [s.sign, Value.get_mk]
  have r15 := s.zero15
  obtain ⟨win,push,_⟩ := comparisonAccess entry s.frame
  change Writable Extracted.programImage n base 0x100 at win
  change Writable Extracted.programImage n (base - 8) 8 at push
  have low := win.readable.low
  have room : 9 ≤ base.toNat := by
    have available := entry.room
    have pos : base.toNat = sp.toNat - 696 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 696 ≤ sp.toNat; omega))
    omega
  obtain ⟨c,pre,call,rs,flag,foot,table,control,saved,args,flag1,v1,v2,high,v0,words⟩ :=
    compareSecondBlock rsp r13 r14 r12 r5 v3 rax r15 s.firstWords win push s.widths s.arguments
  obtain ⟨d,o,path,frame,sign,below,keep⟩ :=
    comparisonReturn entry s.toSplitFrame call rs
      (flag.trans (comparisonFlag (Nat.mod_lt _ (by decide) : splitSecond k < domain.n)))
      foot table control saved args (by decide)
  have sign2 : d[0].get 8 = signByte (second k) := by
    rw [sign]
    unfold signByte
    split <;> rfl
  have sign1 : d[14].get 8 = signByte (first k) := by
    refine ((congrArg (Value.get 8) (keep 14 (by decide))).trans flag1).trans ?_
    unfold signByte
    split <;> rfl
  exact ⟨d,o,path,frame,sign1,sign2,
    preserveFirstWords low room below words,(keepAboveChoice low room (by decide) below).trans v0,
    (congrArg (Value.get 64) (keep 12 (by decide))).trans v1,
    (congrArg (Value.get 64) (keep 5 (by decide))).trans v2,
    (congrArg (Value.get 64) (keep 13 (by decide))).trans high⟩

theorem compareResidues {a b : Registers} {m n : Ram} {sp src tables digits : BitVec 64}
    {k : Nat} (entry : RoutineEntry a m sp 0x558) (_bound : k < domain.n)
    (state : Residues a m sp src tables digits k b n) :
    ∃ c o, Reaches .l10f221 b n .l10f3c5 c o ∧ Signs a m sp src tables digits k c o := by
  obtain ⟨c,o,left,staged⟩ := compareFirst entry state
  obtain ⟨d,p,right,signs⟩ := compareSecond entry staged
  exact ⟨d,p,left.trans right,signs⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
