import K256.Proofs.Verify.Core.Lincomb.GeneratorPath.State
import K256.Proofs.Verify.Core.Lincomb.Phases
import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.Verify.Core.Lincomb.Prepare
import K256.Proofs.Verify.Core.Lincomb.Recode.Memory
import K256.Proofs.Generate.Generator.Multiply.Constants
import K256.Proofs.Generate.Generator.Affine.Select.Setup

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

variable {fr : Activation} {a b c : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s u v : Nat} {m : Ram}

abbrev prepareWrites (fr : Activation) (digits : Nat) : List MemoryRegion :=
  [scratch (workSp fr) 0x560, ⟨(slot fr 0x1568).toNat, 1920⟩, ⟨(slot fr digits).toNat, 544⟩]

theorem preparePushFrame (e : Entry fr a p digest r s) {n : Ram} (retPC : BitVec 64) :
    RamWriteFrame n (memStore n (workSp fr - 8) retPC) [scratch (workSp fr) 8] := by
  have pos := belowWorkNat e (depth := 8) (by decide)
  have base := workNat e
  have room := e.stackRoom
  refine (RamWriteFrame.refl _ _).memStore _ ⟨_, List.mem_singleton_self _, ?_⟩
  change (workSp fr).toNat - 8 ≤ (workSp fr - 8).toNat ∧
    (workSp fr - 8).toNat + 8 ≤ (workSp fr).toNat - 8 + 8 ∧
    (workSp fr - 8).toNat + 8 ≤ 2^64
  have hi := e.low
  change (workSp fr - 8).toNat = _ at pos
  omega

theorem CallerFrame.afterPrepare (e : Entry fr a p digest r s)
    {x y : Registers} {n : Ram} {out : Output Value Ram Reg.count}
    {digits : Nat} {retPC : BitVec 64} (f : CallerFrame fr c x m n)
    (control : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → y[i] = x[i])
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → y[i].width = 64)
    (hlo : 8 ≤ digits) (hhi : digits + 544 ≤ 0x1568)
    (ret : RoutineReturn y (memStore n (workSp fr - 8) retPC) (workSp fr - 8) 0x558
      [⟨(slot fr 0x1568).toNat, 1920⟩, ⟨(slot fr digits).toNat, 544⟩] out) :
    CallerFrame fr c out.values m out.store ∧ RamWriteFrame n out.store (prepareWrites fr digits) := by
  have pos := belowWorkNat e (depth := 8) (by decide)
  change (workSp fr - 8).toNat = _ at pos
  have frame := ((RamWriteFrame.refl n (prepareWrites fr digits)).trans (preparePushFrame e retPC)
    (by
      intro reg hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_cons_self .., ?_⟩
      dsimp only [scratch]
      have room := e.stackRoom
      have base := workNat e
      omega)).trans ret.frame (by
        intro reg hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · refine ⟨_, List.mem_cons_self .., ?_⟩
          dsimp only [scratch]
          omega
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, Nat.le_refl _⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
            Nat.le_refl _, Nat.le_refl _⟩)
  have within : RegionsWithin (prepareWrites fr digits) (writes fr) := by
    intro reg hr
    simp only [prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact workWithin e (off := 0x1568) (len := 1920) (by decide) (by decide) _ (List.mem_cons_self ..)
    · exact workWithin e (depth := 0x560) (by decide) (by decide) _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    · exact workWithin e (depth := 0x560) (by decide) (by omega) _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have same (k : Nat) (hk : k + 8 ≤ 10952) (ht : k + 8 ≤ 0x1568 ∨ 0x1568 + 1920 ≤ k)
      (hd : k + 8 ≤ digits ∨ digits + 544 ≤ k) :
      memLoad out.store (slot fr k) 64 = memLoad n (slot fr k) 64 := by
    have tables := workOutside e (depth := 0x560) (len := 1920) (by decide) hk (by decide) ht
    have ds := workOutside e (depth := 0x560) (by decide) hk (by omega) hd
    refine frame.memLoad_eq ⟨tables.1, ?_⟩
    intro reg hr
    simp only [prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact tables.2 _ (List.mem_cons_self ..)
    · exact tables.2 _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    · exact ds.2 _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, (same 0x28d8 (by decide) (by decide) (Or.inr (by omega))).trans f.ret,
    f.frame.trans frame within⟩, frame⟩
  · rw [ret.rsp, BitVec.sub_add_cancel]
  · intro i hi
    rw [ret.saved i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)]
    exact widths i hi
  · intro i hi
    rw [ret.saved i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega), control i hi]
    exact f.fixedRegs i hi
  · have eq := same 0 (by decide) (by decide) (Or.inl hlo)
    simp only [slot, BitVec.add_zero] at eq
    exact eq.trans f.dest
  · intro i
    have hi := i.isLt
    rw [same _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))]
    exact f.saved i

private theorem generatorCall {x : Registers} {n : Ram}
    (sp : x[4].get 64 = workSp fr) (regs : PreparesGenerator fr x)
    (guard : StoreOk Extracted.programImage n (workSp fr - 8) 8 0x10fba3 5) :
    ∃ y, program.runBlock (dialect Extracted.programImage) ⟨.l10fb8b,x,n⟩ =
      .call ⟨.l10f150,y,memStore n (workSp fr - 8) (0x10fba8 : BitVec 64)⟩
        (callResume .l10fba8 0x10fba8) ∧
      y[4] = ⟨64, workSp fr - 8⟩ ∧ y[7] = ⟨64, 0x202bc8⟩ ∧
      y[6] = ⟨64, localSp fr + 384⟩ ∧ y[2] = ⟨64, slot fr 0x1568⟩ ∧
      y[1] = ⟨64, slot fr 0x228⟩ ∧ y[5] = ⟨64, slot fr 0x1568⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,12,13,14,15,22,39,50,51] → y[i] = x[i]) := by
  obtain ⟨_,_,u,ds,_,_⟩ := regs
  have src := congrArg (Value.get 64) u
  have digits := congrArg (Value.get 64) ds
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [sp, src, digits, guard]
    rfl
  case post =>
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
    intro ⟨i, hi⟩ live
    simp only [List.mem_cons, List.not_mem_nil, or_false] at live
    rcases live with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

set_option maxRecDepth 4096 in
private theorem generatorCode :
    ∀ i < 120, ∃ b, ((0x202bc8 : BitVec 64) + BitVec.ofNat 64 i, b) ∈ Extracted.programImage := by
  let bytes := chunkedRead Extracted.rodataBytes 0x2bc8 120
  let sec : ImageSection := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩
  have hs : sec ∈ Extracted.programSections := List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have count : bytes.length = 120 := by decide +kernel
  intro i hi
  have atByte := mem_codeRange (0x202bc8 : BitVec 64) bytes i (by rw [count]; exact hi)
  exact ⟨_, codeRange_sub_section hs 0x2bc8 120 rfl (by decide +kernel) (by decide +kernel) rfl _ atByte⟩

private theorem prepareBufferApart (e : Entry fr a p digest r s) {digits : Nat}
    (hlo : 8 ≤ digits) (hhi : digits + 544 ≤ 0x1568) :
    Outside [scratch (workSp fr - 8) 0x558, ⟨(workSp fr - 8).toNat, 8⟩,
      ⟨(slot fr digits).toNat, 544⟩] (slot fr 0x1568) 1920 ∧
    Outside [scratch (workSp fr - 8) 0x558, ⟨(workSp fr - 8).toNat, 8⟩] (slot fr digits) 544 := by
  have base := workNat e
  have room := e.stackRoom
  have hi := e.low
  have pos := belowWorkNat e (depth := 8) (by decide)
  change (workSp fr - 8).toNat = _ at pos
  have tables := slotNat e (k := 0x1568) (by decide)
  have ds := slotNat e (k := digits) (by omega)
  constructor
  · refine ⟨by omega, fun reg hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> right <;> dsimp only [scratch] <;> omega
  · refine ⟨by omega, fun reg hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> right <;> dsimp only [scratch] <;> omega

open Generate.Generator.Multiply (generator_valid generator_stored generator_value) in
theorem generatorPrepare (e : Entry fr a p digest r s) (h : Products fr b m u v r)
    (args : Arguments fr b c) (hu : u < domain.n) {x n}
    (f : CallerFrame fr c x m n) (regs : PreparesGenerator fr x)
    (zero : DigitBytes n (slot fr 0x228 + 8) [] ∧ DigitBytes n (slot fr 0x228 + 0x118) []) :
    ∃ d t, Reaches .l10fb8b x n .l10fba8 d t ∧ CallerFrame fr c d m t ∧
      GeneratorPrepared fr d t u := by
  have whole := h.frame.trans f.frame (frameBounds e).1
  have guard : StoreOk Extracted.programImage n (workSp fr - 8) 8 0x10fba3 5 :=
    Recode.storeGuard (off := 24) (belowWrite e whole (depth := 8) (by decide)) code_l10fb8b (by decide)
  obtain ⟨y, call, sp, di, si, dx, cx, bp, keep⟩ :=
    generatorCall (congrArg (Value.get 64) f.sp) regs guard
  have control (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : y[i] = x[i] :=
    keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)
  have fixed (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : y[i] = b[i] := by
    rw [control i hi, f.fixedRegs i hi]
    exact args.keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)
  have widths (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) : y[i].width = 64 := by
    by_cases isBp : i.val = 5
    · have eq : i = 5 := Fin.ext isBp
      subst i
      exact congrArg Value.width bp
    · rw [keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)]
      exact f.widths i hi
  let pushed := memStore n (workSp fr - 8) (0x10fba8 : BitVec 64)
  have pushFrame : RamWriteFrame n pushed [scratch (workSp fr) 8] := preparePushFrame e _
  have pushWithin : RegionsWithin [scratch (workSp fr) 8] (writes fr) := by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    exact workWithin e (off := 0x1568) (len := 1920) (by decide) (by decide) _ (List.mem_cons_self ..)
  have pushedCaller := f.frame.trans pushFrame pushWithin
  have pushedWhole := h.frame.trans pushedCaller (frameBounds e).1
  have word : memLoad pushed (workSp fr - 8) 64 = 0x10fba8 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have entry : RoutineEntry y pushed (workSp fr - 8) 0x558 :=
    routineEntry e pushedWhole (by decide) sp widths
      ((fixed 22 (by decide)).trans h.df)
      (congrArg Value.width ((fixed 39 (by decide)).trans h.mxcsr))
      (congrArg Value.width ((fixed 50 (by decide)).trans h.ftw))
      (congrArg Value.width ((fixed 51 (by decide)).trans h.fcw))
      (by rw [word]; decide)
  have tableWrite : Writable Extracted.programImage pushed (slot fr 0x1568) 1920 :=
    workWrite e pushedWhole (by decide)
  have digitsWrite : Writable Extracted.programImage pushed (slot fr 0x228) 544 :=
    workWrite e pushedWhole (by decide)
  have genSpan {dst : BitVec 64} {len : Nat} (w : Writable Extracted.programImage pushed dst len)
      (positive : 0 < len) :=
    Generate.Generator.Affine.readableCodeSpan generatorCode entry.image (by decide) (by decide) w positive
  have genScratch := genSpan entry.stack (by decide)
  have genTable := genSpan tableWrite (by decide)
  have genDigits := genSpan digitsWrite (by decide)
  have bottom := belowWorkNat e (depth := 0x560) (by decide)
  have pos := belowWorkNat e (depth := 8) (by decide)
  have scratchAddr : workSp fr - 8 - BitVec.ofNat 64 0x558 = workSp fr - BitVec.ofNat 64 0x560 := by bv_omega
  change (workSp fr - 8).toNat = _ at pos
  rw [scratchAddr, bottom] at genScratch
  have work := workNat e
  have room := e.stackRoom
  have high := e.low
  have tables := slotNat e (k := 0x1568) (by decide)
  have ds := slotNat e (k := 0x228) (by decide)
  have scalar := ScalarProduct.slotNat e (off := 384) (by decide)
  have pointApart : Outside [scratch (workSp fr - 8) 0x558, ⟨(slot fr 0x1568).toNat, 1920⟩,
      ⟨(slot fr 0x228).toNat, 544⟩] (0x202bc8 : BitVec 64) 120 := by
    refine ⟨by decide, fun reg hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · dsimp only [scratch]
      rw [pos, Nat.sub_sub]
      exact genScratch.2
    · exact genTable.2
    · exact genDigits.2
  have scalarApart : Outside [scratch (workSp fr - 8) 0x558, ⟨(slot fr 0x1568).toNat, 1920⟩,
      ⟨(slot fr 0x228).toNat, 544⟩] (localSp fr + 384) 32 := by
    have scalarNat : (localSp fr + 384).toNat = fr.rsp.toNat - 488 + 384 := scalar
    refine ⟨by rw [scalarNat]; omega, fun reg hr => ?_⟩
    rw [scalarNat]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · right
      dsimp only [scratch]
      rw [pos]
      omega
    · right
      change (slot fr 0x1568).toNat + 1920 ≤ _
      rw [tables]
      omega
    · right
      change (slot fr 0x228).toNat + 544 ≤ _
      rw [ds]
      omega
  have scalarRead : Readable pushed (localSp fr + 384) 32 :=
    (ScalarProduct.writeSlot e pushedWhole (off := 384) (by decide)).readable
  have words := h.uAt.of_frame pushedCaller (by decide) ((frameBounds e).2 384 32 (by decide) (by decide))
  have zeros {addr : BitVec 64} (hz : DigitBytes n addr [])
      (apart : Outside [scratch (workSp fr) 8] addr 257) :=
    Recode.digitBytes_of_frame pushFrame apart hz
  have digitOutside (k : Nat) (hk : k + 257 ≤ 10952) :
      Outside [scratch (workSp fr) 8] (slot fr k) 257 := by
    have src := slotNat e (k := k) (by omega)
    refine ⟨by omega, fun reg hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    dsimp only [scratch]
    omega
  have addr₁ : slot fr 0x228 + 8 = slot fr 0x230 := by unfold slot; bv_omega
  have addr₂ : slot fr 0x228 + 0x118 = slot fr 0x340 := by unfold slot; bv_omega
  have zeros₁ := zeros zero.1 (by rw [addr₁]; exact digitOutside 0x230 (by decide))
  have zeros₂ := zeros zero.2 (by rw [addr₂]; exact digitOutside 0x340 (by decide))
  obtain ⟨tableApart, digitsApart⟩ := prepareBufferApart e (digits := 0x228) (by decide) (by decide)
  obtain ⟨out, run, ret, prepared⟩ :=
    prepare entry di si dx cx hu generator_valid (generator_stored entry.image) words
      genTable.1 scalarRead pointApart scalarApart tableWrite digitsWrite tableApart digitsApart ⟨zeros₁, zeros₂⟩
  have tag := ret.tag.trans (congrArg (fun x => some (Value.mk 64 x)) word)
  have finalFrame := (CallerFrame.afterPrepare e f control widths (by decide) (by decide) ret).1
  rw [generator_value] at prepared
  refine ⟨_, _, reachesCall call run tag, finalFrame, ⟨prepared, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (ret.saved 3 (by decide)).trans ((keep 3 (by decide)).trans regs.1)
  · exact (ret.saved 5 (by decide)).trans bp
  · exact (ret.saved 13 (by decide)).trans ((keep 13 (by decide)).trans regs.2.2.2.1)
  · exact (ret.saved 14 (by decide)).trans ((keep 14 (by decide)).trans regs.2.2.2.2.1)
  · exact (ret.saved 15 (by decide)).trans ((keep 15 (by decide)).trans regs.2.2.2.2.2)

end K256.Proofs.Verify.Core.Lincomb
