import K256.Proofs.Verify.Core.Lincomb.Recode.Memory

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private theorem offsetNat {base : BitVec 64} {len : Nat} (low : base.toNat + len ≤ 2^32)
    (off : BitVec 64) (within : off.toNat ≤ len) :
    (base + off).toNat = base.toNat + off.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

private theorem loadOffset {m : Ram} {base : BitVec 64} {len : Nat}
    (read : Readable m base len) (off : BitVec 64) (within : off.toNat + 8 ≤ len) :
    LoadOk m (base + off) 8 := by
  have addr := offsetNat read.low off (by omega)
  exact LoadOk.of_region read (by omega) (by omega)

private theorem outsideOffset {base : BitVec 64} {len : Nat} {rs : List MemoryRegion}
    (low : base.toNat + len ≤ 2^32) (apart : Outside rs base len)
    (off : BitVec 64) (within : off.toNat + 8 ≤ len) : Outside rs (base + off) 8 := by
  have addr := offsetNat low off (by omega)
  refine ⟨by omega, fun r hr => ?_⟩
  rcases apart.2 r hr with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

private theorem reachStep {source target finish : Label} {a b c : Registers} {m n p : Ram}
    (step : program.runBlock (dialect Extracted.programImage) ⟨source, a, m⟩ =
      .jump ⟨target, b, n⟩) (rest : Core.Reaches target b n finish c p) :
    Core.Reaches source a m finish c p :=
  .step (by
    change program.step (dialect Extracted.programImage) ⟨⟨source, a, m⟩, []⟩ =
      .next ⟨⟨target, b, n⟩, []⟩
    rw [Program.step, step]
    rfl) rest

private theorem cmpBelowOrEqual (x y : BitVec 64) :
    ((cmpSpec x y).CF || (cmpSpec x y).ZF) = decide (x.toNat ≤ y.toNat) := by
  rw [cmpSpec_CF, cmpSpec_ZF, Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro (lt | rfl)
    · exact Nat.le_of_lt lt
    · exact Nat.le_refl _
  · intro le
    rcases Nat.lt_or_eq_of_le le with lt | eq
    · exact Or.inl lt
    · exact Or.inr (BitVec.eq_of_toNat_eq eq)

private theorem chooseAbove_toNat (x y : BitVec 64) :
    (if (!((cmpSpec x y).CF || (cmpSpec x y).ZF)) = true then x else y).toNat =
      max x.toNat y.toNat := by
  rw [cmpBelowOrEqual]
  by_cases h : x.toNat ≤ y.toNat
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.max_eq_right h]
  · have lt := Nat.lt_of_not_ge h
    simp only [h, decide_false, Bool.not_false, ↓reduceIte, Nat.max_eq_left (Nat.le_of_lt lt)]

private theorem chooseBelowOrEqual_toNat (x y : BitVec 64) :
    (if ((cmpSpec x y).CF || (cmpSpec x y).ZF) = true then y else x).toNat =
      max x.toNat y.toNat := by
  simp only [cmpBelowOrEqual, decide_eq_true_eq]
  by_cases h : x.toNat ≤ y.toNat
  · rw [ite_eq_left h, Nat.max_eq_right h]
  · rw [ite_eq_right h, Nat.max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge h))]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
theorem maximumLength {a : Registers} {m : Ram} {sp it dataPtr : BitVec 64}
    (entry : RoutineEntry a m sp 8) (di : a[7].get 64 = it)
    (si : a[6].get 64 = memLoad m (dataPtr + 0x780) 64)
    (ptr : dataPtr ≠ 0)
    (itRead : Readable m it 112) (dataRead : Readable m dataPtr 0x1340)
    (itApart : Outside [scratch sp 8] it 112) (dataApart : Outside [scratch sp 8] dataPtr 0x1340)
    (first : memLoad m it 64 = dataPtr + 0x9a0)
    (last : memLoad m (it + 8) 64 = dataPtr + 0x1340)
    (front : memLoad m (it + 16) 64 = dataPtr)
    (digits : memLoad m (it + 32) 64 = dataPtr + 0x780)
    (index : memLoad m (it + 48) 64 = 1) (limit : memLoad m (it + 56) 64 = 2)
    (back : memLoad m (it + 64) 64 = 0) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l11c0b0, a, m⟩, []⟩ out ∧
      RoutineReturn a m sp 8 [] out ∧
      (out.values[0].get 64).toNat = max (max (max (memLoad m (dataPtr + 0x780) 64).toNat
          (memLoad m (dataPtr + 0x890) 64).toNat) (memLoad m (dataPtr + 0x1120) 64).toNat)
          (memLoad m (dataPtr + 0x1230) 64).toNat := by
  let n := memStore m (sp - 8) (a[3].get 64)
  have pushMem : memStore m (sp - 8) (a[3].get 64) = n := rfl
  have frame : RamWriteFrame m n [scratch sp 8] :=
    (RamWriteFrame.refl m _).memStore _ ⟨_, List.mem_singleton_self _,
      Recode.inScratch entry.room (by decide) (by decide)⟩
  have rsp : a[4].get 64 = sp := congrArg (Value.get 64) entry.rsp
  have pushOK : StoreOk Extracted.programImage m (sp - 8) 8 0x11c0b0 1 :=
    Recode.storeGuard (off := 0) (len := 1) entry.stack code_l11c0b0 (by decide)
  have itMem (off : BitVec 64) (within : off.toNat + 8 ≤ 112) :
      memLoad n (it + off) 64 = memLoad m (it + off) 64 :=
    frame.memLoad_eq (outsideOffset itRead.low itApart off within)
  have itLoad (off : BitVec 64) (within : off.toNat + 8 ≤ 112) : LoadOk n (it + off) 8 :=
    loadOffset (itRead.of_frame frame) off within
  have dataMem (off : BitVec 64) (within : off.toNat + 8 ≤ 0x1340) :
      memLoad n (dataPtr + off) 64 = memLoad m (dataPtr + off) 64 :=
    frame.memLoad_eq (outsideOffset dataRead.low dataApart off within)
  have dataLoad (off : BitVec 64) (within : off.toNat + 8 ≤ 0x1340) :
      LoadOk n (dataPtr + off) 8 :=
    loadOffset (dataRead.of_frame frame) off within
  have readFirst : LoadOk n it 8 := by
    rw [← BitVec.add_zero it]
    exact itLoad 0 (by decide)
  have first' : memLoad n it 64 = dataPtr + 0x9a0 := by
    have h := itMem 0 (by decide)
    rw [show it + (0 : BitVec 64) = it from BitVec.add_zero it] at h
    exact h.trans first
  have front' := (itMem 16 (by decide)).trans front
  have index' := (itMem 48 (by decide)).trans index
  have limit' := (itMem 56 (by decide)).trans limit
  have digits' := (itMem 32 (by decide)).trans digits
  have back' := (itMem 64 (by decide)).trans back
  have last' := (itMem 8 (by decide)).trans last
  have nonzeroFirst : dataPtr + 0x9a0 ≠ 0 := by
    have addr := offsetNat dataRead.low 0x9a0 (by decide)
    intro h
    rw [h] at addr
    simp only [BitVec.reduceToNat] at addr
    omega
  have firstNeLast : dataPtr + 0x9a0 ≠ dataPtr + 0x1340 := by bv_omega
  have span : (dataPtr + 0x1340) - (dataPtr + 0x9a0) = 0x9a0 := by bv_omega
  have popOK : LoadOk n (sp - 8) 8 :=
    ⟨(entry.stack.readable.of_frame frame).low, (entry.stack.readable.of_frame frame).present⟩
  have retOK : LoadOk n sp 8 := ⟨entry.returnSlot.low, (entry.returnSlot.of_frame frame).present⟩
  have returned : memLoad n sp 64 = memLoad m sp 64 := by
    apply frame.memLoad_eq
    refine ⟨by have := entry.returnSlot.low; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (by have := entry.room; simp only [scratch]; omega)
  have saved : memLoad n (sp - 8) 64 = a[3].get 64 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have restore : (⟨64, a[3].get 64⟩ : Value) = a[3] := by
    suffices ∀ v : Value, v.width = 64 → (⟨64, v.get 64⟩ : Value) = v from
      this a[3] (entry.saved 3 (by decide))
    rintro ⟨width, bits⟩ h
    change width = 64 at h
    subst width
    rfl
  refine ⟨?out, ?exec, ?post⟩
  case exec =>
    apply Program.Exec.of_sem
    refine Semantics.Reaches.exec (L := program.sem (dialect Extracted.programImage))
      (t := (⟨⟨.l11c3ba, ?_, n⟩, []⟩ : CFG.State Value Ram Label signature Reg.count)) ?route ?finish
    case route =>
      change Core.Reaches .l11c0b0 a m .l11c3ba _ n
      refine reachStep (target := .l11c0c2) (n := n) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [rsp, di, si, pushOK, pushMem,
          readFirst, first', itLoad 16 (by decide), front', ptr, cmpSpec_ZF, beq_eq_false_iff_ne.mpr ptr]
        rfl
      refine reachStep (target := .l11c0d6) (n := n) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [pushMem, di, itLoad 48 (by decide), itLoad 56 (by decide), index', limit', subSpec_ZF]
        rfl
      refine reachStep (target := .l11c0f1) (n := n) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [pushMem, di, itLoad 32 (by decide), digits',
          show (cmpSpec (-1 : BitVec 64) (-4)).CF = false by decide,
          show (cmpSpec (-1 : BitVec 64) (-4)).ZF = false by decide]
        rfl
      refine reachStep (target := .l11c187) (n := n) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval
        rfl
      refine reachStep (target := .l11c1a0) (n := n) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [BitVec.add_assoc, BitVec.reduceAdd]
        rfl
      refine reachStep (target := .l11c1ba) (n := n) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [pushMem, dataLoad 0x890 (by decide), dataMem 0x890 (by decide),
          cmpSpec_ZF, beq_self_eq_true]
        rfl
      refine reachStep (target := .l11c1c7) (n := n) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [pushMem, di, itLoad 64 (by decide), back', BitVec.and_self, testFlags,
          beq_eq_false_iff_ne.mpr nonzeroFirst]
        rfl
      refine reachStep (target := .l11c1d4) (n := n) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [pushMem, di, itLoad 8 (by decide), last', cmpSpec_ZF,
          beq_eq_false_iff_ne.mpr firstNeLast]
        rfl
      refine reachStep (target := .l11c1e0) (n := n) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [span, cmpSpec_ZF, beq_self_eq_true]
        rfl
      refine reachStep (target := .l11c294) (n := n) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval
        rfl
      refine reachStep (target := .l11c2bc) (n := n) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [BitVec.add_assoc, BitVec.reduceAdd, pushMem, dataLoad 0x1120 (by decide),
          dataLoad 0x1230 (by decide), dataMem 0x1120 (by decide), dataMem 0x1230 (by decide)]
        rfl
      refine reachStep (target := .l11c3ba) (n := n) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [testFlags, beq_self_eq_true]
        rfl
      exact .refl _
    case finish =>
      apply Program.Exec.sem
      apply Recode.done
      cfg_eval [pushMem, popOK, retOK, BitVec.sub_add_cancel, returned, saved, entry.returnLow]
      rfl
  case post =>
    refine ⟨⟨rfl, rfl, ?_, frame⟩, ?_⟩
    · rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | rfl | exact restore
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, Value.get_mk,
        ← cmpSpec_ZF,
        chooseAbove_toNat, chooseBelowOrEqual_toNat]

end K256.Proofs.Verify.Core.Lincomb.Loop
