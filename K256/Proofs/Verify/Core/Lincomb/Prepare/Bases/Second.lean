import K256.Proofs.Verify.Core.Lincomb.Prepare.Bases.Preserve
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Generate.Generator.Multiply.Prepare.Copy
import K256.Proofs.Common.Point.TableWords.Negate
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve
open Common.Tactic Common.Field Common.Point.TableWords

private abbrev secondBaseSite (negative : Bool) : Label :=
  if negative then .l10f6b9 else .l10f7fa

private abbrev SecondBaseKept (b c : Registers) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ [3,4,5,13,14,15,22,39,50,51] → c[i] = b[i]

local macro "second_base_kept" : tactic => `(tactic| (
  rintro ⟨i, hi⟩ h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h|h <;> subst i <;> rfl))

local macro "second_base_branch " rsp:ident check:ident flag:ident : tactic => `(tactic| (
  refine ⟨?out,Semantics.Reaches.single ?run,?keep,?r12⟩
  case run =>
    change (program.runBlock _ _).next _ [] = _
    simp only [secondBaseSite, Bool.false_eq_true, ite_false, ite_true] at $flag ⊢
    cfg_eval [($rsp), ($check), ($flag)]
    rfl
  case keep => second_base_kept
  case r12 => rfl))

private theorem branchSecondBase {a : Registers} {m : Ram} {q : Word}
    (rsp : a[4].get 64 = q) (read : Readable m (q+7) 1)
    (negative : Bool) (flag : memLoad m (q+7) 8 = if negative then 1 else 0) :
    ∃ b, Reaches .l10f6ae a m (secondBaseSite negative) b m ∧
      SecondBaseKept a b ∧ b[12] = a[12] := by
  have check : LoadOk m (q+7) 1 := ⟨read.low,read.present⟩
  cases negative
  · second_base_branch rsp check flag
  · second_base_branch rsp check flag

private theorem copySecondBase {a : Registers} {m : Ram} {q : Word}
    (rsp : a[4].get 64 = q) (df : a[22].get 1 = 0)
    (src : Readable m (q+0x100) 120) (dst : Writable Extracted.programImage m (q+0x1f0) 120)
    (apart : (q+0x100).toNat + 120 ≤ (q+0x1f0).toNat) :
    ∃ b, Reaches .l10f7fa a m .l10f812 b (memCopy m (q+0x1f0) (q+0x100) 120) ∧
      SecondBaseKept a b ∧ b[12] = a[12] := by
  have copy := Generate.Generator.Multiply.Prepare.copyGuard (count := 15) (size := 8) src
    (ParseSignature.storeOk_of_codeRange (off := 21) (len := 3) dst
      (fun v hv => Common.fnCode_subset_programImage v (code_l10f7fa v hv)) (by decide)) (Or.inl apart)
  refine ⟨?out,Semantics.Reaches.single ?run,?keep,?r12⟩
  case run =>
    change (program.runBlock _ _).next _ [] = _
    cfg_eval [rsp,df]
    refine Eq.trans (congrArg _ (ite_eq_left (Or.inr copy))) ?_
    rfl
  case keep => second_base_kept
  case r12 => rfl

private def storeSecondNegatedBase (m : Ram) (q : Word) (x y z : Limbs) : Ram :=
  let m := memStore m (q+0x210) x[4]
  let m := memStore m (q+0x208) x[3]
  let m := memStore m (q+0x200) x[2]
  let m := memStore m (q+0x1f8) x[1]
  let m := memStore m (q+0x1f0) x[0]
  let m := memStore m (q+0x240) z[0]
  let m := memStore m (q+0x248) z[1]
  let m := memStore m (q+0x250) z[2]
  let m := memStore m (q+0x258) z[3]
  let m := memStore m (q+0x260) z[4]
  let m := memStore m (q+0x218) (negateY y)[0]
  let m := memStore m (q+0x220) (negateY y)[1]
  let m := memStore m (q+0x228) (negateY y)[2]
  let m := memStore m (q+0x230) (negateY y)[3]
  memStore m (q+0x238) (negateY y)[4]
local macro "second_base_word " h:ident i:num : term =>
  `(by simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] using $h $i (by decide))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
private theorem negateSecondBase {a : Registers} {m : Ram} {q : Word} {x y z : Limbs}
    (rsp : a[4].get 64 = q) (fold : a[5].get 64 = 0x1000003d1)
    (negTop : a[12].get 64 = 0x3fffffffffffc) (negMiddle : a[13].get 64 = 0x3ffffffffffffc)
    (maskTop : a[14].get 64 = 0xffffffffffff) (maskMiddle : a[15].get 64 = 0xfffffffffffff)
    (win : Writable Extracted.programImage m (q+0x100) 0x168)
    (_high : q.toNat + 0x268 ≤ 2^32)
    (wx : WordsAt m (q+0x100) 64 x) (wy : WordsAt m (q+0x128) 64 y)
    (wz : WordsAt m (q+0x150) 64 z) :
    ∃ b, Reaches .l10f6b9 a m .l10f812 b (storeSecondNegatedBase m q x y z) ∧
      SecondBaseKept a b ∧ b[12].width = 64 := by
  have x0 : memLoad m (q+0x100) 64 = x[0] := second_base_word wx 0
  have x1 : memLoad m (q+0x108) 64 = x[1] := second_base_word wx 1
  have x2 : memLoad m (q+0x110) 64 = x[2] := second_base_word wx 2
  have x3 : memLoad m (q+0x118) 64 = x[3] := second_base_word wx 3
  have x4 : memLoad m (q+0x120) 64 = x[4] := second_base_word wx 4
  have y0 : memLoad m (q+0x128) 64 = y[0] := second_base_word wy 0
  have y1 : memLoad m (q+0x130) 64 = y[1] := second_base_word wy 1
  have y2 : memLoad m (q+0x138) 64 = y[2] := second_base_word wy 2
  have y3 : memLoad m (q+0x140) 64 = y[3] := second_base_word wy 3
  have y4 : memLoad m (q+0x148) 64 = y[4] := second_base_word wy 4
  have z0 : memLoad m (q+0x150) 64 = z[0] := second_base_word wz 0
  have z1 : memLoad m (q+0x158) 64 = z[1] := second_base_word wz 1
  have z2 : memLoad m (q+0x160) 64 = z[2] := second_base_word wz 2
  have z3 : memLoad m (q+0x168) 64 = z[3] := second_base_word wz 3
  have z4 : memLoad m (q+0x170) 64 = z[4] := second_base_word wz 4
  refine ⟨?_,Semantics.Reaches.single ?run,?keep,?width⟩
  case run =>
    change (program.runBlock _ _).next _ [] = _
    cfg_eval [rsp,fold,negTop,negMiddle,maskTop,maskMiddle]
    segment_words [x0,x1,x2,x3,x4,y0,y1,y2,y3,y4,z0,z1,z2,z3,z4]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_; slot_guard using code_l10f6b9)
    rfl
  case keep => second_base_kept
  case width => rfl


private abbrev secondBaseWrites (q : Word) : List MemoryRegion := [⟨(q+0x1f0).toNat,120⟩]

private theorem inSecondBase {q off : Word} {len : Nat}
    (low : (q+0x1f0).toNat + 120 ≤ 2^32) (fits : (off - 0x1f0).toNat + len ≤ 120) :
    InRegions (secondBaseWrites q) (q+off) len := by
  have addr := toNat_of_offsets (x := q) (a := q+off) (r := q+0x1f0) rfl rfl low fits
  exact ⟨_,List.mem_singleton_self _,by dsimp only [InRegion]; omega⟩

private theorem negatedSecondBaseFrame {m : Ram} {q : Word} {x y z : Limbs}
    (low : (q+0x1f0).toNat + 120 ≤ 2^32) :
    RamWriteFrame m (storeSecondNegatedBase m q x y z) (secondBaseWrites q) := by
  unfold storeSecondNegatedBase
  repeat' refine RamWriteFrame.memStore ?_ _ (inSecondBase low (by decide))
  exact RamWriteFrame.refl _ _

private theorem negatedSecondBaseStored {m : Ram} {q : Word} {x y z : Limbs} {p : Projective}
    (rx : FieldRepr x p.x 1) (ry : FieldRepr y p.y 1) (rz : FieldRepr z p.z 1) :
    p.neg.Stored (storeSecondNegatedBase m q x y z) (q+0x1f0) := by
  refine ⟨x,negateY y,z,?_,?_,?_,rx,negateY_repr ry,rz⟩
  all_goals
    intro i hi
    rcases (by omega : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4) with rfl|rfl|rfl|rfl|rfl
    all_goals
      simp only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,
        BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero]
      segment_words [storeSecondNegatedBase]

theorem secondSignedBase {a b : Registers} {m n : Ram} {sp tables digits : BitVec 64}
    {p : Curve.Point} {k : Nat} (entry : RoutineEntry a m sp 0x558)
    (digitsWrite : Writable Extracted.programImage m digits 544)
    (digitsApart : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩] digits 544)
    (firstBase : FirstBase a m sp tables digits p k b n)
    (endo : PointValueAt n (frameSp sp + 0x100) (endomorphism p)) :
    ∃ c o, Reaches .l10f6ae b n .l10f812 c o ∧ SignedPair a m sp tables digits p k c o := by
  let q := frameSp sp
  have room := entry.room
  have high := entry.returnSlot.low
  have qNat : q.toNat = sp.toNat - 696 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 696 ≤ sp.toNat; omega))
  have address (off : Word) (h : off.toNat ≤ 648) :
      (q+off).toNat = q.toNat + off.toNat := by
    rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]
  have stack := entry.stack.of_frame firstBase.frame
  have bottom : (sp-(0x558 : Word)).toNat = sp.toNat - 0x558 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr room)
  have slot (off : Word) (len : Nat) (h : off.toNat + len ≤ 648) :
      Writable Extracted.programImage n (q+off) len := by
    have eq := address off (by omega)
    exact stack.sub (by change (sp-(0x558 : Word)).toNat ≤ _; omega)
      (by change _ ≤ (sp-(0x558 : Word)).toNat + 0x558; omega)
  have before := address (0x178 : Word) (by decide)
  have dest := address (0x1f0 : Word) (by decide)
  have target := slot 0x1f0 120 (by decide)
  obtain ⟨p₁,valid₁,eq₁,stored₁⟩ := firstBase.point
  obtain ⟨p₂,valid₂,eq₂,stored₂⟩ := endo
  have finish {c : Registers} {o : Ram} (keep : SecondBaseKept b c) (width : c[12].width = 64)
      (frame : RamWriteFrame n o (secondBaseWrites q))
      (point : PointValueAt o (q+0x1f0) (signedBase (second k) (endomorphism p))) :
      SignedPair a m sp tables digits p k c o := by
    have kept (i : Fin Reg.count) (hi : i.val ∈ [3,5,13,14,15] ∨ i.val ∈ [22,39,50,51]) : c[i] = b[i] := by
      apply keep
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega
    have widths (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) : c[i].width = 64 := by
      by_cases h : i.val = 12
      · have eq : i = 12 := Fin.ext h
        rw [eq]
        exact width
      · exact (congrArg Value.width (kept i (Or.inl (by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)))).trans (firstBase.widths i hi)
    have signed := signedFrameAfter entry firstBase.toSignedFrame digitsWrite digitsApart frame
      (by
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        change sp.toNat - 0x558 ≤ (q+0x1f0).toNat ∧ (q+0x1f0).toNat + 120 ≤ sp.toNat - 48
        rw [dest]
        change _ ∧ q.toNat + 496 + 120 ≤ _
        omega)
      ((keep 4 (by decide)).trans firstBase.rsp) (keep 3 (by decide)) widths
      (fun i hi => kept i (.inr hi))
    exact ⟨signed,⟨p₁,valid₁,eq₁,stored₁.of_frame frame (by
      refine ⟨by change (q+0x178).toNat + 120 ≤ 2^64; rw [before]; change q.toNat + 376 + 120 ≤ _; omega,
        fun r hr => Or.inl ?_⟩
      obtain rfl := List.mem_singleton.mp hr
      change (q+0x178).toNat + 120 ≤ (q+0x1f0).toNat
      rw [before,dest]
      change q.toNat + 376 + 120 ≤ q.toNat + 496
      omega)⟩,point⟩
  by_cases neg : second k < 0
  · obtain ⟨c,branch,kept,top⟩ := branchSecondBase (q := q) (congrArg (Value.get 64) firstBase.rsp)
      (slot 7 1 (by decide)).readable true (by simpa only [signByte,neg,ite_true] using firstBase.sign)
    obtain ⟨x,y,z,wx,wy,wz,rx,ry,rz⟩ := stored₂.coordinates
    simp only [BitVec.add_assoc,BitVec.reduceAdd] at wy wz
    have rsp : c[4].get 64 = q := congrArg (Value.get 64) ((kept 4 (by decide)).trans firstBase.rsp)
    have fold : c[5].get 64 = 0x1000003d1 := congrArg (Value.get 64) ((kept 5 (by decide)).trans firstBase.fold)
    have negTop : c[12].get 64 = 0x3fffffffffffc := congrArg (Value.get 64) (top.trans firstBase.negTop)
    have negMiddle : c[13].get 64 = 0x3ffffffffffffc := congrArg (Value.get 64) ((kept 13 (by decide)).trans firstBase.negMiddle)
    have maskTop : c[14].get 64 = 0xffffffffffff := congrArg (Value.get 64) ((kept 14 (by decide)).trans firstBase.maskTop)
    have maskMiddle : c[15].get 64 = 0xfffffffffffff := congrArg (Value.get 64) ((kept 15 (by decide)).trans firstBase.maskMiddle)
    have low : q.toNat + 0x268 ≤ 2^32 := by omega
    obtain ⟨d,run,kept',width⟩ := negateSecondBase (q := q) (x := x) (y := y) (z := z)
      rsp fold negTop negMiddle maskTop maskMiddle (slot 0x100 0x168 (by decide)) low wx wy wz
    have resultFrame := negatedSecondBaseFrame (q := q) (m := n) (x := x) (y := y) (z := z) target.readable.low
    refine ⟨d,storeSecondNegatedBase n q x y z,branch.trans run,finish (fun i hi => (kept' i hi).trans (kept i hi))
      width resultFrame ?_⟩
    exact ⟨p₂.neg,Projective.neg_valid valid₂,by rw [Projective.neg_value,eq₂,signedBase,ite_eq_left neg],
      negatedSecondBaseStored rx ry rz⟩
  · obtain ⟨c,branch,kept,top⟩ := branchSecondBase (q := q) (congrArg (Value.get 64) firstBase.rsp)
      (slot 7 1 (by decide)).readable false (by simpa only [signByte,neg,ite_false,Bool.false_eq_true] using firstBase.sign)
    have rsp : c[4].get 64 = q := congrArg (Value.get 64) ((kept 4 (by decide)).trans firstBase.rsp)
    have df : c[22].get 1 = 0 :=
      congrArg (Value.get 1) ((kept 22 (by decide)).trans ((firstBase.control 22 (by decide)).trans entry.df))
    have apart : (q+0x100).toNat + 120 ≤ (q+0x1f0).toNat := by
      rw [address 0x100 (by decide),dest]
      change q.toNat + 256 + 120 ≤ q.toNat + 496
      omega
    obtain ⟨d,run,kept',top'⟩ := copySecondBase rsp df (slot 0x100 120 (by decide)).readable target apart
    let o := memCopy n (q+0x1f0) (q+0x100) 120
    have point : p₂.Stored o (q+0x1f0) := by
      have input : p₂.Stored n ((q+0x100) + BitVec.ofNat 64 0) := by
        simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using stored₂
      have copied := input.memCopy (src := q+0x100) (off := 0) (dst := q+0x1f0)
        (by decide : 120 ≤ 2^64) (by decide)
      simpa only [o,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using copied
    have resultFrame : RamWriteFrame n o (secondBaseWrites q) :=
      Sec1.Wrapper.Copy.memCopy_frame (RamWriteFrame.refl n _) (inSecondBase (off := 0x1f0) target.readable.low (by decide))
    refine ⟨d,o,branch.trans run,finish (fun i hi => (kept' i hi).trans (kept i hi))
      ((congrArg Value.width (top'.trans top)).trans (firstBase.widths 12 (by decide))) resultFrame ?_⟩
    exact ⟨p₂,valid₂,by rw [eq₂,signedBase,ite_eq_right neg],point⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
