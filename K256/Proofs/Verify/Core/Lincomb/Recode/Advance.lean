import K256.Proofs.Verify.Core.Lincomb.Recode.Memory

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private theorem iteratorAfterPush {m pushed : Ram} {sp ptr next lo hi : BitVec 64} {block : Nat}
    (frame : RamWriteFrame m pushed [scratch sp 24])
    (apart : Outside [scratch sp 24] ptr 40)
    (iterator : IteratorAt m ptr next block lo hi) :
    IteratorAt pushed ptr next block lo hi := by
  intro i hi
  rw [← iterator i hi]
  apply frame.memLoad_eq
  have low := apart.1
  have offset : (wordAddr ptr 64 i).toNat = ptr.toNat + 8 * i := by
    simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 8 * i) (by omega), Nat.mod_eq_of_lt (by omega)]
  have separate := apart.2 (scratch sp 24) (List.mem_singleton_self _)
  refine ⟨by rw [offset]; omega, fun r hr => ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  rw [offset]
  omega

private theorem savedValue {v : Value} (h : v.width = 64) : (⟨64, v.get 64⟩ : Value) = v := by
  obtain ⟨width, bits⟩ := v
  change width = 64 at h
  subst width
  rfl

theorem advanceIterator {a : Registers} {m : Ram} {sp ptr next lo hi : BitVec 64}
    {previous index : Nat}
    (entry : RoutineEntry a m sp 24) (di : a[7].get 64 = ptr)
    (si : a[6].get 64 = BitVec.ofNat 64 index)
    (previousLE : previous ≤ index) (near : index ≤ previous + 1) (limit : index ≤ 1)
    (iterator : IteratorAt m ptr next previous (if previous = 0 then lo else hi)
      (if previous = 0 then hi else 0))
    (writable : Writable Extracted.programImage m ptr 40)
    (separate : Outside [scratch sp 24, ⟨sp.toNat, 8⟩] ptr 40) :
    ∃ out, program.Exec machine ⟨⟨.l124100, a, m⟩, []⟩ out ∧
      RoutineReturn a m sp 24 [⟨ptr.toNat, 40⟩] out ∧
      out.values[0].get 64 = (if index = 0 then lo else hi) ∧
      out.values[2].get 64 = (if index = 0 then hi else 0) ∧
      IteratorAt out.store ptr next index (if index = 0 then lo else hi)
        (if index = 0 then hi else 0) := by
  let save14 := memStore m (sp - 8) (a[14].get 64)
  let save3 := memStore save14 (sp - 16) (a[3].get 64)
  let pushed := memStore save3 (sp - 24) (a[0].get 64)
  let buffer : MemoryRegion := ⟨ptr.toNat, 40⟩
  have pushFrame : RamWriteFrame m pushed [scratch sp 24] := by
    dsimp only [pushed, save3, save14]
    repeat apply RamWriteFrame.memStore
    · exact RamWriteFrame.refl _ _
    all_goals exact ⟨_, List.mem_singleton_self _, inScratch entry.room (by decide) (by decide)⟩
  have pushWhole : RamWriteFrame m pushed [scratch sp 24, buffer] :=
    (RamWriteFrame.refl m _).trans pushFrame (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩)
  have pushedWords := iteratorAfterPush pushFrame
    ⟨separate.1, fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact separate.2 _ List.mem_cons_self⟩ iterator
  have rsp : a[4].get 64 = sp := congrArg (Value.get 64) entry.rsp
  have push14 : StoreOk Extracted.programImage m (sp-8) 8 0x124100 2 :=
    storeGuard (off := 0) (stackSlot entry (off := 8) (by decide) (by decide)) code_l124100 (by decide)
  have push3 : StoreOk Extracted.programImage save14 (sp-16) 8 0x124102 1 :=
    storeGuard (off := 2) ((stackSlot entry (off := 16) (by decide) (by decide)).memStore
      (sp-8) (a[14].get 64)) code_l124100 (by decide)
  have push0 : StoreOk Extracted.programImage save3 (sp-24) 8 0x124103 1 :=
    storeGuard (off := 3) (((stackSlot entry (off := 24) (by decide) (by decide)).memStore
      (sp-8) (a[14].get 64)).memStore (sp-16) (a[3].get 64)) code_l124100 (by decide)
  have mem14 : memStore m (sp-8) (a[14].get 64) = save14 := rfl
  have mem3 : memStore save14 (sp-16) (a[3].get 64) = save3 := rfl
  have mem0 : memStore save3 (sp-24) (a[0].get 64) = pushed := rfl
  have bounds := writable.readable.low
  have addr (off : BitVec 64) (within : off.toNat + 8 ≤ 40) :
      (ptr + off).toNat = ptr.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have field {mem : Ram} (readable : Readable mem ptr 40) (off : BitVec 64)
      (within : off.toNat + 8 ≤ 40) : LoadOk mem (ptr + off) 8 := by
    have h := addr off within
    exact LoadOk.of_region readable (by omega) (by omega)
  have inBuffer (off : BitVec 64) (within : off.toNat + 8 ≤ 40) :
      InRegions [buffer] (ptr+off) 8 := by
    refine ⟨buffer, List.mem_singleton_self _, ?_⟩
    simp only [InRegion, buffer, addr off within]
    omega
  have bufWrite {mem : Ram} (w : Writable Extracted.programImage mem ptr 40) (off : BitVec 64)
      (within : off.toNat + 8 ≤ 40) : Writable Extracted.programImage mem (ptr+off) 8 := by
    have h := addr off within
    exact w.sub (by omega) (by omega)
  have pushedRead := writable.readable.of_frame pushFrame
  have cursor : memLoad pushed (ptr+16) 64 = BitVec.ofNat 64 previous := pushedWords 2 (by decide)
  have cachedLow : memLoad pushed (ptr+24) 64 = (if previous = 0 then lo else hi) :=
    pushedWords 3 (by decide)
  have cachedHigh : memLoad pushed (ptr+32) 64 = (if previous = 0 then hi else 0) :=
    pushedWords 4 (by decide)
  have saved₃ : memLoad pushed (sp-16) 64 = a[3].get 64 := by
    simp (disch := store_disch) only [pushed, save3, memLoad_memStore_same, memLoad_memStore_of_rangeApart]
  have saved₁₄ : memLoad pushed (sp-8) 64 = a[14].get 64 := by
    simp (disch := store_disch) only [pushed, save3, save14, memLoad_memStore_same, memLoad_memStore_of_rangeApart]
  have sub16 : sp - 24 + 8 = sp - 16 := by bv_omega
  have sub8 : sp - 16 + 8 = sp - 8 := by bv_omega
  have sub0 : sp - 8 + 8 = sp := by bv_omega
  have spLow := entry.returnSlot.low
  have retApart : Outside [scratch sp 24, buffer] sp 8 := by
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inr (by have := entry.room; simp only [scratch]; omega)
    · have h := separate.2 ⟨sp.toNat, 8⟩ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      exact h.symm
  have stackLoad {mem : Ram} (frame : RamWriteFrame m mem [scratch sp 24, buffer])
      (off : BitVec 64) (lower : off.toNat ≤ 24) (upper : 8 ≤ off.toNat) :
      LoadOk mem (sp-off) 8 :=
    let readable := ((stackSlot entry lower upper).of_frame frame).readable
    ⟨readable.low, readable.present⟩
  have retLoad {mem : Ram} (frame : RamWriteFrame m mem [scratch sp 24, buffer]) :
      LoadOk mem sp 8 := ⟨spLow, (entry.returnSlot.of_frame frame).present⟩
  have restore3 := savedValue (entry.saved 3 (by decide))
  have restore14 := savedValue (entry.saved 14 (by decide))
  by_cases same : previous = index
  · subst previous
    have zf : (cmpSpec (BitVec.ofNat 64 index) (BitVec.ofNat 64 index)).ZF = true := by
      rw [cmpSpec_ZF, beq_self_eq_true]
    have cf : (cmpSpec (BitVec.ofNat 64 index) (BitVec.ofNat 64 index)).CF = false := by
      simp only [cmpSpec_CF, Nat.lt_irrefl, decide_false]
    refine ⟨?out, ?exec, ?post, ?lo, ?hi, ?words⟩
    case exec =>
      refine jump (target := .l12411a) (n := pushed) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [rsp, di, si, push14, push3, push0, mem14, mem3, mem0,
          field pushedRead 16 (by decide), cursor, zf]
        rfl
      refine jump (target := .l12417c) (n := pushed) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [si, cf, zf]
        rfl
      apply done
      have retWord := pushWhole.memLoad_eq (k := 64) retApart
      cfg_eval [di, sub16, sub8, sub0]
      simp only [mem0, field pushedRead 24 (by decide), field pushedRead 32 (by decide),
        cachedLow, cachedHigh, stackLoad pushWhole 16 (by decide) (by decide),
        stackLoad pushWhole 8 (by decide) (by decide), retLoad pushWhole, saved₃, saved₁₄,
        retWord, entry.returnLow, and_self, ite_true]
      <;> rfl
    case words => exact pushedWords
    case lo => rfl
    case hi => rfl
    case post =>
      refine ⟨rfl, rfl, ?_, pushWhole⟩
      rintro ⟨i, bound⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | rfl | exact restore3 | exact restore14
  · have hprev : previous = 0 := by omega
    have hindex : index = 1 := by omega
    subst previous index
    simp only [ite_eq_right Nat.one_ne_zero]
    let cursorSet := memStore pushed (ptr+16) (1 : BitVec 64)
    let lowSet := memStore cursorSet (ptr+24) hi
    let highSet := memStore lowSet (ptr+32) (0 : BitVec 64)
    have cursorMem : memStore pushed (ptr+16) (1 : BitVec 64) = cursorSet := rfl
    have lowMem : memStore cursorSet (ptr+24) hi = lowSet := rfl
    have highMem : memStore lowSet (ptr+32) (0 : BitVec 64) = highSet := rfl
    have cursorWrite : StoreOk Extracted.programImage pushed (ptr+16) 8 0x12411f 4 :=
      storeGuard (off := 0) (bufWrite (writable.of_frame pushFrame) 16 (by decide))
        code_l12411f (by decide)
    have lowWrite : StoreOk Extracted.programImage cursorSet (ptr+24) 8 0x12412b 4 :=
      storeGuard (off := 12) (bufWrite ((writable.of_frame pushFrame).memStore (ptr+16) (1 : BitVec 64)) 24
        (by decide)) code_l12411f (by decide)
    have highWrite : StoreOk Extracted.programImage lowSet (ptr+32) 8 0x12418c 8 :=
      storeGuard (off := 0) (bufWrite (((writable.of_frame pushFrame).memStore (ptr+16)
        (1 : BitVec 64)).memStore (ptr+24) hi) 32 (by decide)) code_l12418c (by decide)
    have readCursor : Readable cursorSet ptr 40 := pushedRead.memStore (ptr+16) (1 : BitVec 64)
    have fit : ptr.toNat + 8 * 5 ≤ 2^64 := by omega
    have cursorWords : WordsAt cursorSet ptr 64 (#v[next, 0, 1, lo, hi] : Vector (BitVec 64) 5) :=
      pushedWords.write_set (j := 2) (by decide) 1 (by decide) (by decide) (by decide) fit
    have left : memLoad cursorSet (ptr+8) 64 = 0 := cursorWords 1 (by decide)
    have high : memLoad cursorSet (ptr+32) 64 = hi := cursorWords 4 (by decide)
    have lowWords : WordsAt lowSet ptr 64 (#v[next, 0, 1, hi, hi] : Vector (BitVec 64) 5) :=
      cursorWords.write_set (j := 3) (by decide) hi (by decide) (by decide) (by decide) fit
    have highWords : IteratorAt highSet ptr next 1 hi 0 :=
      lowWords.write_set (j := 4) (by decide) 0 (by decide) (by decide) (by decide) fit
    have storesFrame : RamWriteFrame pushed highSet [buffer] :=
      let cursorFrame := (RamWriteFrame.refl pushed [buffer]).memStore
        (1 : BitVec 64) (inBuffer 16 (by decide))
      let lowFrame := cursorFrame.memStore hi (inBuffer 24 (by decide))
      lowFrame.memStore (0 : BitVec 64) (inBuffer 32 (by decide))
    have frame := pushWhole.trans storesFrame (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩)
    have saved (off : BitVec 64) (lower : off.toNat ≤ 24) (upper : 8 ≤ off.toNat) :
        memLoad highSet (sp-off) 64 = memLoad pushed (sp-off) 64 := by
      apply storesFrame.memLoad_eq
      have ⟨h₁, h₂, h₃⟩ := inScratch entry.room lower upper
      refine ⟨h₃, fun r hr => ?_⟩
      obtain rfl := List.mem_singleton.mp hr
      have apart := separate.2 (scratch sp 24) List.mem_cons_self
      change ptr.toNat + 40 ≤ (scratch sp 24).start ∨ _ at apart
      change (sp-off).toNat + 8 ≤ ptr.toNat ∨ ptr.toNat + 40 ≤ (sp-off).toNat
      omega
    have idx0 : (BitVec.ofNat 64 0) = 0 := rfl
    have idx1 : (BitVec.ofNat 64 1) = 1 := rfl
    have entryZF : (cmpSpec (0 : BitVec 64) 1).ZF = false := by decide
    have diffZF : (cmpSpec (1 : BitVec 64) 1).ZF = true := by decide
    have advanceZF : (cmpSpec (1 : BitVec 64) 0).ZF = false := by decide
    have advanceCF : (cmpSpec (1 : BitVec 64) 0).CF = false := by decide
    refine ⟨?advancedOut, ?exec, ?post, ?lo, ?hi, ?words⟩
    case exec =>
      refine jump (target := .l124111) (n := pushed) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [rsp, di, si, push14, push3, push0, mem14, mem3, mem0,
          field pushedRead 16 (by decide), cursor, idx0, idx1, entryZF]
        rfl
      refine jump (target := .l12411a) (n := pushed) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [si, idx1, diffZF]
        rfl
      refine jump (target := .l12411f) (n := pushed) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [si, idx1, advanceZF, advanceCF]
        rfl
      refine jump (target := .l12418c) (n := lowSet) (b := ?_) ?edge ?_
      case edge =>
        cfg_eval [di, testFlags]
        simp only [mem0, cursorWrite, cursorMem, field readCursor 8 (by decide),
          field readCursor 32 (by decide), left, high, lowWrite, lowMem,
          BitVec.and_self, beq_self_eq_true, ite_true]
        <;> rfl
      apply done
      have retWord := frame.memLoad_eq (k := 64) retApart
      cfg_eval [di, BitVec.xor_self, sub16, sub8, sub0]
      simp only [lowMem, highWrite, highMem, stackLoad frame 16 (by decide) (by decide),
        stackLoad frame 8 (by decide) (by decide), retLoad frame, saved 16 (by decide) (by decide),
        saved 8 (by decide) (by decide), saved₃, saved₁₄, retWord, entry.returnLow, and_self, ite_true]
      <;> rfl
    case words => exact highWords
    case lo => rfl
    case hi => rfl
    case post =>
      refine ⟨rfl, rfl, ?_, frame⟩
      rintro ⟨i, bound⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | rfl | exact restore3 | exact restore14

end K256.Proofs.Verify.Core.Lincomb.Recode
