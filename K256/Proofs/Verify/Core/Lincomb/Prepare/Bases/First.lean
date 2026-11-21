import K256.Proofs.Verify.Core.Lincomb.Prepare.Bases.Preserve
import K256.Proofs.Verify.Core.Lincomb.Prepare.Digits.Geometry
import K256.Proofs.Generate.Generator.Multiply.Lookup.Memory
import K256.Proofs.Common.Point.TableWords.Negate
import K256.Proofs.Sec1.Wrapper.Copy.Execution
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
open Generate.Generator.Multiply (Projective)
open Generate.Curve
open Common.Tactic Common.Field Common.Point.TableWords

private abbrev firstBranch (negative : Bool) : Label := if negative then .l10f578 else .l10f680

private structure FirstBranchRegisters (a b : Registers) (q : Word) : Prop where
  rsp : b[4] = ⟨64,q⟩
  lowOffset : b[1] = ⟨64,0x3ffffbfffff0bc⟩
  fold : b[6] = ⟨64,0x1000003d1⟩
  negTop : b[12] = ⟨64,0x3fffffffffffc⟩
  negMiddle : b[13] = ⟨64,0x3ffffffffffffc⟩
  maskTop : b[11] = ⟨64,0xffffffffffff⟩
  maskMiddle : b[15] = ⟨64,0xfffffffffffff⟩
  keep : ∀ i : Fin Reg.count, i.val ∈ [3,5,14,22,39,50,51] → b[i] = a[i]

private structure FirstJoinRegisters (a b : Registers) (q src : Word) : Prop where
  rsp : b[4] = ⟨64,q⟩
  src : b[10].get 64 = src
  fold : b[5] = ⟨64,0x1000003d1⟩
  negTop : b[12] = ⟨64,0x3fffffffffffc⟩
  negMiddle : b[13] = ⟨64,0x3ffffffffffffc⟩
  maskTop : b[14] = ⟨64,0xffffffffffff⟩
  maskMiddle : b[15] = ⟨64,0xfffffffffffff⟩
  keep : ∀ i : Fin Reg.count, i.val ∈ [3,22,39,50,51] → b[i] = a[i]

private theorem firstBaseJump {l r : Label} {a b : Registers} {m n : Ram}
    (step : program.runBlock (dialect Extracted.programImage) ⟨l,a,m⟩ = .jump ⟨r,b,n⟩) :
    Reaches l a m r b n := by
  apply Semantics.Reaches.single
  change (program.runBlock _ _).next _ [] = _
  rw [step]
  rfl

set_option maxRecDepth 2000 in
private theorem firstBaseHeader {a : Registers} {m : Ram} {q digits value : Word} {negative : Bool}
    (rsp : a[4] = ⟨64,q⟩) (bp : a[5].get 64 = digits) (ax : a[0].get 64 = value)
    (sign : a[14].get 8 = if negative then 1 else 0)
    (store : StoreOk Extracted.programImage m (digits+0x110) 8 0x10f55e 7) :
    ∃ b, Reaches .l10f52c a m (firstBranch negative) b (memStore m (digits+0x110) value) ∧
      FirstBranchRegisters a b q := by
  have signGet : (a[14].get 64).setWidth 8 = if negative then 1 else 0 := by
    simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)] using sign
  cases negative
  all_goals
    refine ⟨?_,firstBaseJump ?step,?post⟩
    case step =>
      cfg_eval [bp,ax,signGet,store,firstBranch,BitVec.and_self,testFlags]
      rfl
    case post =>
      refine ⟨rsp,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
      rintro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private abbrev firstPointWrites (q : Word) : List MemoryRegion := [⟨(q+0x178).toNat,120⟩]

set_option maxRecDepth 2000 in
private theorem firstBaseCopy {a b : Registers} {m : Ram} {q src : Word} {p : Projective}
    (args : FirstBranchRegisters a b q) (df : b[22].get 1 = 0)
    (ptr : memLoad m (q+0x28) 64 = src) (ptrRead : LoadOk m (q+0x28) 8)
    (read : Readable m src 120) (write : Writable Extracted.programImage m (q+0x178) 120)
    (apart : Outside (firstPointWrites q) src 120) (stored : p.Stored m src) :
    ∃ c o, Reaches .l10f680 b m .l10f69e c o ∧ FirstJoinRegisters a c q src ∧
      RamWriteFrame m o (firstPointWrites q) ∧ p.Stored o (q+0x178) := by
  have rsp : b[4].get 64 = q := congrArg (Value.get 64) args.rsp
  have ok : RepMovsOk Extracted.programImage m 0 src (q+0x178) 15 8 0x10f69b 3 :=
    Generate.Generator.Multiply.Lookup.copyGuard read
      (ParseSignature.storeOk_of_codeRange (off := 27) (len := 3) write
        (fun v hv => Common.fnCode_subset_programImage v (code_l10f680 v hv)) (by decide))
      (apart.2 _ (.head _))
  let o := memCopy m (q+0x178) src 120
  have frame : RamWriteFrame m o (firstPointWrites q) := by
    apply Sec1.Wrapper.Copy.memCopy_frame (RamWriteFrame.refl _ _)
    exact ⟨_,.head _,Nat.le_refl _,Nat.le_refl _,by have := write.readable.low; omega⟩
  refine ⟨?_,o,firstBaseJump ?step,?post,frame,Generate.Generator.Multiply.Lookup.copyStored stored⟩
  case step =>
    cfg_eval [rsp,df,ptr,ptrRead,args.fold,args.maskTop]
    rw [ite_eq_left (Or.inr ok)]
  case post =>
    refine ⟨args.rsp,rfl,?_,args.negTop,args.negMiddle,?_,args.maskMiddle,?_⟩
    · change Value.mk 64 (b[6].get 64) = _
      rw [args.fold]
      rfl
    · change Value.mk 64 (b[11].get 64) = _
      rw [args.maskTop]
      rfl
    · rintro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl
      · exact args.keep 3 (by decide)
      · exact args.keep 22 (by decide)
      · exact args.keep 39 (by decide)
      · exact args.keep 50 (by decide)
      · exact args.keep 51 (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2200000 in
private theorem firstBaseNegate {a b : Registers} {m : Ram} {q src : Word} {p : Projective}
    (args : FirstBranchRegisters a b q) (room : q.toNat+496 ≤ 2^64)
    (ptr : memLoad m (q+0x28) 64 = src) (ptrRead : LoadOk m (q+0x28) 8)
    (read : Readable m src 120) (write : Writable Extracted.programImage m (q+0x178) 120)
    (apart : Outside (firstPointWrites q) src 120) (stored : p.Stored m src) :
    ∃ c o, Reaches .l10f578 b m .l10f69e c o ∧ FirstJoinRegisters a c q src ∧
      RamWriteFrame m o (firstPointWrites q) ∧ p.neg.Stored o (q+0x178) := by
  have rsp : b[4].get 64 = q := congrArg (Value.get 64) args.rsp
  have sep := apart.2 _ (.head _)
  have fold : b[6].get 64 = 0x1000003d1 := congrArg (Value.get 64) args.fold
  have negTop : b[12].get 64 = 0x3fffffffffffc := congrArg (Value.get 64) args.negTop
  have negMiddle : b[13].get 64 = 0x3ffffffffffffc := congrArg (Value.get 64) args.negMiddle
  have lowOffset : b[1].get 64 = 0x3ffffbfffff0bc := congrArg (Value.get 64) args.lowOffset
  have maskTop : b[11].get 64 = 0xffffffffffff := congrArg (Value.get 64) args.maskTop
  have maskMiddle : b[15].get 64 = 0xfffffffffffff := congrArg (Value.get 64) args.maskMiddle
  obtain ⟨xl, yl, zl, wx, wy, wz, rx, ry, rz⟩ := stored.coordinates
  have x0 := wx 0 (by decide)
  have x1 := wx 1 (by decide)
  have x2 := wx 2 (by decide)
  have x3 := wx 3 (by decide)
  have x4 := wx 4 (by decide)
  have y0 := wy 0 (by decide)
  have y1 := wy 1 (by decide)
  have y2 := wy 2 (by decide)
  have y3 := wy 3 (by decide)
  have y4 := wy 4 (by decide)
  have z0 := wz 0 (by decide)
  have z1 := wz 1 (by decide)
  have z2 := wz 2 (by decide)
  have z3 := wz 3 (by decide)
  have z4 := wz 4 (by decide)
  simp only [wordAddr,Nat.reduceDiv,Nat.reduceMul,reduceAddOffset,BitVec.add_zero] at x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 z0 z1 z2 z3 z4
  refine ⟨?_,?_,firstBaseJump ?step,?regs,?frame,?point⟩
  case step =>
    cfg_eval [rsp,ptr,ptrRead,args.fold,args.negTop,args.negMiddle,args.lowOffset,args.maskTop,args.maskMiddle]
    segment_words [fold,negTop,negMiddle,lowOffset,maskTop,maskMiddle,x0,x1,x2,x3,x4,y0,y1,y2,y3,y4,z0,z1,z2,z3,z4]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10f578)
    rfl
  case regs =>
    refine ⟨args.rsp,rfl,rfl,args.negTop,args.negMiddle,rfl,args.maskMiddle,?_⟩
    · rintro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl
      · exact args.keep 3 (by decide)
      · exact args.keep 22 (by decide)
      · exact args.keep 39 (by decide)
      · exact args.keep 50 (by decide)
      · exact args.keep 51 (by decide)
  case frame =>
    have inside {off : Word} (lo : 376 ≤ off.toNat) (hi : off.toNat+8 ≤ 496) :
        InRegions (firstPointWrites q) (q+off) 8 := by
      refine ⟨_,.head _,?_⟩
      change (q+376).toNat ≤ (q+off).toNat ∧ (q+off).toNat+8 ≤ (q+376).toNat+120 ∧
        (q+off).toNat+8 ≤ 2^64
      simp only [BitVec.toNat_add, BitVec.reduceToNat,
        Nat.mod_eq_of_lt (by omega : q.toNat+off.toNat < 2^64),
        Nat.mod_eq_of_lt (by omega : q.toNat+376 < 2^64)]
      omega
    refine RamWriteFrame.memStore (a := q+448) (n := 64) ?_ _ (inside (off := 448) (by decide) (by decide))
    refine RamWriteFrame.memStore (a := q+440) (n := 64) ?_ _ (inside (off := 440) (by decide) (by decide))
    refine RamWriteFrame.memStore (a := q+432) (n := 64) ?_ _ (inside (off := 432) (by decide) (by decide))
    refine RamWriteFrame.memStore (a := q+424) (n := 64) ?_ _ (inside (off := 424) (by decide) (by decide))
    refine RamWriteFrame.memStore (a := q+416) (n := 64) ?_ _ (inside (off := 416) (by decide) (by decide))
    refine RamWriteFrame.memStore (a := q+408) (n := 64) ?_ _ (inside (off := 408) (by decide) (by decide))
    refine RamWriteFrame.memStore (a := q+400) (n := 64) ?_ _ (inside (off := 400) (by decide) (by decide))
    refine RamWriteFrame.memStore (a := q+392) (n := 64) ?_ _ (inside (off := 392) (by decide) (by decide))
    refine RamWriteFrame.memStore (a := q+384) (n := 64) ?_ _ (inside (off := 384) (by decide) (by decide))
    refine RamWriteFrame.memStore (a := q+376) (n := 64) ?_ _ (inside (off := 376) (by decide) (by decide))
    refine RamWriteFrame.memStore (a := q+456) (n := 64) ?_ _ (inside (off := 456) (by decide) (by decide))
    refine RamWriteFrame.memStore (a := q+464) (n := 64) ?_ _ (inside (off := 464) (by decide) (by decide))
    refine RamWriteFrame.memStore (a := q+472) (n := 64) ?_ _ (inside (off := 472) (by decide) (by decide))
    refine RamWriteFrame.memStore (a := q+480) (n := 64) ?_ _ (inside (off := 480) (by decide) (by decide))
    refine RamWriteFrame.memStore (a := q+488) (n := 64) ?_ _ (inside (off := 488) (by decide) (by decide))
    exact RamWriteFrame.refl _ _
  case point =>
    refine ⟨xl,negateY yl,zl,?_,?_,?_,rx,negateY_repr ry,rz⟩
    all_goals
      intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases cases with rfl|rfl|rfl|rfl|rfl <;>
        segment_words [wordAddr,Nat.reduceDiv,Nat.reduceMul,negateY,Sec1.Serialize.Normalize.top,
          Sec1.Serialize.Normalize.mask48,Sec1.Serialize.Normalize.mask52,
          Vector.getElem_mk,List.getElem_toArray,Vector.getElem_ofFn,
          x0,x1,x2,x3,x4,y0,y1,y2,y3,y4,z0,z1,z2,z3,z4]
    all_goals first | assumption | rfl

private theorem firstBaseSignBranch {a b : Registers} {m : Ram} {q src : Word} {p : Projective}
    {r : Int} (args : FirstBranchRegisters a b q) (room : q.toNat+496 ≤ 2^64)
    (df : b[22].get 1 = 0) (ptr : memLoad m (q+0x28) 64 = src)
    (ptrRead : LoadOk m (q+0x28) 8) (read : Readable m src 120)
    (write : Writable Extracted.programImage m (q+0x178) 120)
    (apart : Outside (firstPointWrites q) src 120) (stored : p.Stored m src) (valid : p.valid) :
    ∃ d o, Reaches (firstBranch (decide (r < 0))) b m .l10f69e d o ∧
      FirstJoinRegisters a d q src ∧ RamWriteFrame m o (firstPointWrites q) ∧
      PointValueAt o (q+0x178) (signedBase r p.value) := by
  by_cases neg : r < 0
  · rw [decide_eq_true neg, signedBase, ite_eq_left neg]
    obtain ⟨d,o,step,regs,frame,out⟩ := firstBaseNegate args room ptr ptrRead read write apart stored
    exact ⟨d,o,step,regs,frame,p.neg,p.neg_valid valid,p.neg_value,out⟩
  · rw [decide_eq_false neg,signedBase,ite_eq_right neg]
    obtain ⟨d,o,step,regs,frame,out⟩ := firstBaseCopy args df ptr ptrRead read write apart stored
    exact ⟨d,o,step,regs,frame,p,valid,rfl,out⟩

theorem firstSignedBase {a b : Registers} {m n : Ram} {sp src tables digits : BitVec 64}
    {p : Projective} {k : Nat} (entry : RoutineEntry a m sp 0x558) (valid : p.valid)
    (point : p.Stored m src) (pointRead : Readable m src 120)
    (pointApart : Outside [scratch sp 0x558, ⟨digits.toNat, 544⟩] src 120)
    (digitsWrite : Writable Extracted.programImage m digits 544)
    (digitsApart : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩] digits 544)
    (recoded : Recoded a m sp src tables digits k b n) :
    ∃ c o, Reaches .l10f52c b n .l10f69e c o ∧ FirstBase a m sp tables digits p.value k c o ∧ c[10].get 64 = src := by
  let q := frameSp sp
  let len := BitVec.ofNat 64 (Naf.digits (second k).natAbs).length
  let head := digits + 0x110
  let next := memStore n head len
  let written : List MemoryRegion := [⟨head.toNat,8⟩]
  let wholeRegions : List MemoryRegion := [scratch sp 0x558,⟨digits.toNat,544⟩]
  have digitLow := digitsApart.1
  have headNat : head.toNat = digits.toNat + 0x110 := digitOffsetNat digitLow (by decide)
  have stackApart := digitsApart.2 _ (List.mem_cons_self ..)
  change digits.toNat + 544 ≤ sp.toNat - 1368 ∨ sp.toNat - 1368 + 1368 ≤ digits.toNat at stackApart
  have room := entry.room
  have high := entry.returnSlot.low
  have headFrame : RamWriteFrame n next written :=
    (RamWriteFrame.refl n written).memStore len
      ⟨_,.head _,Nat.le_refl _,Nat.le_refl _,by rw [headNat]; omega⟩
  have whole : RamWriteFrame m next wholeRegions := recoded.frame.trans headFrame (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,.tail _ (.head _),?_⟩
    change digits.toNat ≤ head.toNat ∧ head.toNat+8 ≤ digits.toNat+544
    rw [headNat]
    omega)
  have keepStack (ptr : Word) (w : Nat)
      (lo : sp.toNat - 1368 ≤ ptr.toNat) (hi : ptr.toNat + w/8 ≤ sp.toNat) :
      memLoad next ptr w = memLoad n ptr w := by
    apply headFrame.memLoad_eq
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change ptr.toNat + w/8 ≤ head.toNat ∨ head.toNat + 8 ≤ ptr.toNat
    rw [headNat]
    omega
  have keepDigit {off : Nat} (w : Nat) (ho : off < 544) (hi : off + w/8 ≤ 544)
      (away : off + w/8 ≤ 0x110 ∨ 0x118 ≤ off) :
      memLoad next (digits + BitVec.ofNat 64 off) w = memLoad n (digits + BitVec.ofNat 64 off) w := by
    apply headFrame.memLoad_eq
    have eq := digitOffsetNat digitLow ho
    refine ⟨by rw [eq]; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change (digits+BitVec.ofNat 64 off).toNat + w/8 ≤ head.toNat ∨
      head.toNat+8 ≤ (digits+BitVec.ofNat 64 off).toNat
    rw [eq,headNat]
    omega
  have wHead : Writable Extracted.programImage n head 8 :=
    digitBufferWindow (off := 0x110) digitsWrite recoded.frame (by decide) (by decide)
  have headGuard : StoreOk Extracted.programImage n head 8 0x10f55e 7 :=
    ParseSignature.storeOk_of_codeRange (off := 50) (len := 7) wHead
      (fun v hv => Common.fnCode_subset_programImage v (code_l10f52c v hv)) (by decide)
  have axGet : b[0].get 64 = len := by
    calc
      b[0].get 64 = (Value.mk 64 len).get 64 := congrArg (Value.get 64) recoded.secondLength
      _ = len := by rw [Value.get_mk_setWidth,BitVec.setWidth_eq]
  obtain ⟨c,header,args⟩ := firstBaseHeader (q := q) (digits := digits) (value := len)
    (negative := decide (first k < 0)) recoded.rsp
    (congrArg (Value.get 64) recoded.digitPtr) axGet
    (by simpa only [decide_eq_true_eq] using recoded.signFirst) headGuard
  have keepSaved {off : Word} (lo : 8 ≤ off.toNat) (hi : off.toNat ≤ 48) :
      memLoad next (sp-off) 64 = memLoad n (sp-off) 64 := by
    have eq := digitStackNat room (off := off) (by omega)
    exact keepStack _ 64 (by rw [eq]; omega) (by rw [eq]; omega)
  have headState : SignedFrame a m sp tables digits k c next := by
    refine ⟨⟨args.rsp,(args.keep 3 (by decide)).trans recoded.tableBase,?_,
      fun i hi => (args.keep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans
        (recoded.control i hi),(keepSaved (off := 48) (by decide) (by decide)).trans recoded.rbx,
      (keepSaved (off := 40) (by decide) (by decide)).trans recoded.r12,
      (keepSaved (off := 32) (by decide) (by decide)).trans recoded.r13,
      (keepSaved (off := 24) (by decide) (by decide)).trans recoded.r14,
      (keepSaved (off := 16) (by decide) (by decide)).trans recoded.r15,
      (keepSaved (off := 8) (by decide) (by decide)).trans recoded.rbp⟩,whole,?_,?_,?_,?_⟩
    · rintro ⟨i,hi⟩ hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl
      · exact (congrArg Value.width (args.keep 3 (by decide))).trans (recoded.widths 3 (by decide))
      · exact (congrArg Value.width (args.keep 5 (by decide))).trans (recoded.widths 5 (by decide))
      · exact congrArg Value.width args.negTop
      · exact congrArg Value.width args.negMiddle
      · exact (congrArg Value.width (args.keep 14 (by decide))).trans (recoded.widths 14 (by decide))
      · exact congrArg Value.width args.maskMiddle
    · have eq := keepDigit (off := 0) 64 (by decide) (by decide) (.inl (by decide))
      simp only [BitVec.add_zero] at eq
      exact eq.trans recoded.firstLength
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · intro i
      have hi := i.isLt
      have eq := keepDigit (off := 8+i.val) 8 (by omega) (by omega) (.inl (by omega))
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at eq
      exact eq.trans (recoded.firstBytes i)
    · intro i
      have hi := i.isLt
      have eq := keepDigit (off := 0x118+i.val) 8 (by omega) (by omega) (.inr (by omega))
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at eq
      exact eq.trans (recoded.secondBytes i)
  have ptrNat : (q+0x28).toNat = sp.toNat - 0x2b8 + 0x28 :=
    digitFrameNat room (off := 0x28) (by decide)
  have signNat : (q+7).toNat = sp.toNat - 0x2b8 + 7 :=
    digitFrameNat room (off := 7) (by decide)
  have ptr : memLoad next (q+0x28) 64 = src :=
    (keepStack _ 64 (by rw [ptrNat]; omega) (by rw [ptrNat]; omega)).trans recoded.pointPtr
  have sign : memLoad next (q+7) 8 = signByte (second k) :=
    (keepStack _ 8 (by rw [signNat]; omega) (by rw [signNat]; omega)).trans recoded.signSecond
  have ptrRead : LoadOk next (q+0x28) 8 := by
    have r := (digitScratchWindow entry whole (off := 0x28) (len := 8) (by decide)).readable
    exact ⟨r.low,r.present⟩
  have write : Writable Extracted.programImage next (q+0x178) 120 :=
    digitScratchWindow entry whole (off := 0x178) (len := 120) (by decide)
  have destNat : (q+0x178).toNat = sp.toNat - 0x2b8 + 0x178 := digitFrameNat room (by decide)
  have apart : Outside (firstPointWrites q) src 120 := by
    refine ⟨pointApart.1,fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    have sep := pointApart.2 _ (List.mem_cons_self ..)
    change src.toNat + 120 ≤ sp.toNat - 1368 ∨ sp.toNat - 1368 + 1368 ≤ src.toNat at sep
    change src.toNat + 120 ≤ (q+0x178).toNat ∨ (q+0x178).toNat+120 ≤ src.toNat
    rw [destNat]
    omega
  have read := pointRead.of_frame whole
  have stored := point.of_frame whole pointApart
  have df : c[22].get 1 = 0 := by
    have saved : c[22] = a[22] := (args.keep 22 (by decide)).trans (recoded.control 22 (by decide))
    exact congrArg (Value.get 1) (saved.trans entry.df)
  have baseNat : q.toNat = sp.toNat - 0x2b8 := digitStackNat room (off := 0x2b8) (by decide)
  have baseRoom : q.toNat+496 ≤ 2^64 := by rw [baseNat]; omega
  obtain ⟨d,o,step,regs,frame,out⟩ := firstBaseSignBranch (q := q) (p := p) (r := first k) args baseRoom df
    ptr ptrRead read write apart stored valid
  have widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → d[i].width = 64 := by
    rintro ⟨i,hi⟩ hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl
    · exact (congrArg Value.width (regs.keep 3 (by decide))).trans (recoded.widths 3 (by decide))
    · exact congrArg Value.width regs.fold
    · exact congrArg Value.width regs.negTop
    · exact congrArg Value.width regs.negMiddle
    · exact congrArg Value.width regs.maskTop
    · exact congrArg Value.width regs.maskMiddle
  have final : SignedFrame a m sp tables digits k d o := signedFrameAfter entry headState digitsWrite digitsApart frame
    (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      change sp.toNat - 1368 ≤ (q+0x178).toNat ∧ (q+0x178).toNat+120 ≤ sp.toNat-48
      rw [destNat]
      omega) regs.rsp ((regs.keep 3 (by decide)).trans (args.keep 3 (by decide)).symm) widths
    (fun i hi => by
      have hz : i.val ∈ [3,22,39,50,51] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
        omega
      have hc : i.val ∈ [3,5,14,22,39,50,51] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
        omega
      exact (regs.keep i hz).trans (args.keep i hc).symm)
  have signOutside : Outside (firstPointWrites q) (q+7) 1 := by
    refine ⟨by rw [signNat]; omega,?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    left
    change (q+7).toNat+1 ≤ (q+0x178).toNat
    rw [destNat,signNat]
    omega
  have lastSign : memLoad o (q+7) 8 = signByte (second k) :=
    (frame.memLoad_eq (k := 8) signOutside).trans sign
  refine ⟨d,o,?_,?_,regs.src⟩
  · exact @Semantics.Reaches.trans (program.sem (dialect Extracted.programImage))
      ⟨⟨.l10f52c,b,n⟩,[]⟩ ⟨⟨firstBranch (decide (first k < 0)),c,next⟩,[]⟩
      ⟨⟨.l10f69e,d,o⟩,[]⟩ header step
  · exact ⟨final,out,lastSign,regs.fold,regs.negTop,regs.negMiddle,regs.maskTop,regs.maskMiddle⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
