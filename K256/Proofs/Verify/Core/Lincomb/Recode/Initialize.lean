import K256.Proofs.Verify.Core.Lincomb.Recode.Memory

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private abbrev push (a : Registers) (m : Ram) (sp : BitVec 64) : Ram :=
  memStore (memStore (memStore m (sp-8) (a[14].get 64)) (sp-16) (a[3].get 64))
    (sp-24) (a[0].get 64)

private abbrev setup (m : Ram) (ptr next lo hi : BitVec 64) : Ram :=
  memStore (memStore (memStore (memStore (memStore m ptr next) (ptr+8) (0 : BitVec 64))
    (ptr+16) (0 : BitVec 64)) (ptr+24) lo) (ptr+32) hi

private theorem setup_words (m : Ram) (ptr next lo hi : BitVec 64) :
    IteratorAt (setup m ptr next lo hi) ptr next 0 lo hi := by
  intro i h
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := store_disch) only [setup, wordAddr, Nat.reduceDiv, Nat.reduceMul,
      BitVec.add_zero, memLoad_memStore_same, memLoad_memStore_of_rangeApart]
    <;> first | rfl | exact memLoad_memStore_same _ _ _ (by decide) (by decide)

theorem initializeIterator {a : Registers} {m : Ram} {sp ptr src : BitVec 64}
    (entry : RoutineEntry a m sp 24) (di : a[7].get 64 = ptr)
    (si : a[6].get 64 = src) (dx : a[2].get 64 = 16)
    (readable : Readable m src 16) (writable : Writable Extracted.programImage m ptr 40)
    (source : Outside [scratch sp 24] src 16)
    (dest : Outside [scratch sp 24, ⟨sp.toNat, 8⟩] ptr 40) :
    ∃ out, program.Exec machine ⟨⟨.l1241e0, a, m⟩, []⟩ out ∧
      RoutineReturn a m sp 24 [⟨ptr.toNat, 40⟩] out ∧
      IteratorAt out.store ptr (src+16) 0 (memLoad m src 64) (memLoad m (src+8) 64) := by
  let pushed := push a m sp
  let low := memLoad m src 64
  let high := memLoad m (src+8) 64
  let setNext := memStore pushed ptr (src+16)
  let setLen := memStore setNext (ptr+8) (0 : BitVec 64)
  let setIndex := memStore setLen (ptr+16) (0 : BitVec 64)
  let setLow := memStore setIndex (ptr+24) low
  let built := memStore setLow (ptr+32) high
  have toNext : memStore pushed ptr (src+16) = setNext := rfl
  have toLen : memStore setNext (ptr+8) (0 : BitVec 64) = setLen := rfl
  have toIndex : memStore setLen (ptr+16) (0 : BitVec 64) = setIndex := rfl
  have toLow : memStore setIndex (ptr+24) low = setLow := rfl
  have toBuilt : memStore setLow (ptr+32) high = built := rfl
  have rsp : a[4].get 64 = sp := congrArg (Value.get 64) entry.rsp
  have push₁ : StoreOk Extracted.programImage m (sp-8) 8 0x1241e0 2 := storeGuard (off := 0) (stackSlot entry (off := 8) (by decide) (by decide : 8 ≤ (8 : BitVec 64).toNat))
    code_l1241e0 (len := 2) (by decide)
  have push₂ : StoreOk Extracted.programImage (memStore m (sp-8) (a[14].get 64))
      (sp-16) 8 0x1241e2 1 := storeGuard (off := 2) ((stackSlot entry (off := 16) (by decide)
    (by decide : 8 ≤ (16 : BitVec 64).toNat)).memStore (sp-8) (a[14].get 64))
    code_l1241e0 (len := 1) (by decide)
  have push₃ : StoreOk Extracted.programImage
      (memStore (memStore m (sp-8) (a[14].get 64)) (sp-16) (a[3].get 64))
      (sp-24) 8 0x1241e3 1 := storeGuard (off := 3) (((stackSlot entry (off := 24) (by decide)
    (by decide : 8 ≤ (24 : BitVec 64).toNat)).memStore (sp-8) (a[14].get 64)).memStore
    (sp-16) (a[3].get 64)) code_l1241e0 (len := 1) (by decide)
  have pushFrame : RamWriteFrame m pushed [scratch sp 24] := by
    dsimp only [pushed, push]
    repeat apply RamWriteFrame.memStore
    · exact RamWriteFrame.refl _ _
    all_goals exact ⟨_, List.mem_singleton_self _, inScratch entry.room (by decide) (by decide)⟩
  have readLow : LoadOk pushed src 8 :=
    LoadOk.of_offsets (readable.of_frame pushFrame) (addr_self _) (addr_self _) (by decide)
  have readHigh : LoadOk pushed (src+8) 8 :=
    LoadOk.of_offsets (readable.of_frame pushFrame) rfl (addr_self _) (by decide)
  have srcLow := readable.low
  have hiNat : (src+8).toNat = src.toNat+8 :=
    toNat_of_offsets (n := 8) rfl (addr_self _) srcLow (by decide)
  have lowWord : memLoad pushed src 64 = low := by
    apply pushFrame.memLoad_eq
    refine ⟨by omega, fun r hr => ?_⟩
    rcases source.2 r hr with h | h <;> omega
  have highWord : memLoad pushed (src+8) 64 = high := by
    apply pushFrame.memLoad_eq
    refine ⟨by rw [hiNat]; omega, fun r hr => ?_⟩
    rw [hiNat]
    rcases source.2 r hr with h | h <;> omega
  have ptrWrite := writable.of_frame pushFrame
  have bufWord (off : BitVec 64) (within : off.toNat + 8 ≤ 40) :
      Writable Extracted.programImage pushed (ptr+off) 8 :=
    ptrWrite.of_offsets rfl (addr_self _) (by
      have hz : off - 0 = off := by bv_omega
      rwa [hz])
  have w₀ : StoreOk Extracted.programImage pushed ptr 8 0x124215 3 := storeGuard (off := 0) (ptrWrite.of_offsets (addr_self _) (addr_self _) (by decide : (0-0 : BitVec 64).toNat + 8 ≤ 40))
    code_l124215 (len := 3) (by decide)
  have w₁ : StoreOk Extracted.programImage setNext (ptr+8) 8 0x124218 4 := storeGuard (off := 3) ((bufWord 8 (by decide)).memStore ptr (src+16))
    code_l124215 (len := 4) (by decide)
  have w₂ : StoreOk Extracted.programImage setLen (ptr+16) 8 0x12421c 8 := storeGuard (off := 7) (((bufWord 16 (by decide)).memStore ptr (src+16)).memStore (ptr+8) (0 : BitVec 64))
    code_l124215 (len := 8) (by decide)
  have w₃ : StoreOk Extracted.programImage setIndex (ptr+24) 8 0x124224 4 := storeGuard (off := 15) ((((bufWord 24 (by decide)).memStore ptr (src+16)).memStore (ptr+8) (0 : BitVec 64)).memStore (ptr+16) (0 : BitVec 64))
    code_l124215 (len := 4) (by decide)
  have w₄ : StoreOk Extracted.programImage setLow (ptr+32) 8 0x124228 4 := storeGuard (off := 19) (((((bufWord 32 (by decide)).memStore ptr (src+16)).memStore (ptr+8) (0 : BitVec 64)).memStore (ptr+16) (0 : BitVec 64)).memStore (ptr+24) low)
    code_l124215 (len := 4) (by decide)
  have bp := writable.readable.low
  let r : MemoryRegion := ⟨ptr.toNat, 40⟩
  have written (off : BitVec 64) (within : off.toNat + 8 ≤ 40) :
      InRegions [r] (ptr+off) 8 := by
    refine ⟨r, List.mem_singleton_self _, ?_⟩
    have addr : (ptr+off).toNat = ptr.toNat + off.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    simp only [InRegion, r, addr]
    omega
  have ptrFrame : RamWriteFrame pushed built [r] := by
    have first : InRegions [r] ptr 8 := by
      simpa only [show ptr + (0 : BitVec 64) = ptr from BitVec.add_zero _] using written 0 (by decide)
    dsimp only [built, setLow, setIndex, setLen, setNext]
    have one := (RamWriteFrame.refl pushed [r]).memStore (src+16) first
    have two := one.memStore (0 : BitVec 64) (written 8 (by decide))
    have three := two.memStore (0 : BitVec 64) (written 16 (by decide))
    exact (three.memStore low (written 24 (by decide))).memStore high (written 32 (by decide))
  have stackIn : RegionsWithin [scratch sp 24] [scratch sp 24, r] := by
    intro x hx
    obtain rfl := List.mem_singleton.mp hx
    exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  have bufIn : RegionsWithin [r] [scratch sp 24, r] := by
    intro x hx
    obtain rfl := List.mem_singleton.mp hx
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩
  have widened : RamWriteFrame m pushed [scratch sp 24, r] :=
    (RamWriteFrame.refl m _).trans pushFrame stackIn
  have wholeFrame := widened.trans ptrFrame bufIn
  have savedLoad (k : BitVec 64) (hk : k = 8 ∨ k = 16) :
      memLoad built (sp-k) 64 = memLoad pushed (sp-k) 64 := by
    apply ptrFrame.memLoad_eq
    have room := entry.room
    have endLow := entry.returnSlot.low
    have below := dest.2 (scratch sp 24) List.mem_cons_self
    rcases hk with rfl | rfl <;>
      refine ⟨by bv_omega, fun x hx => ?_⟩ <;>
      obtain rfl := List.mem_singleton.mp hx <;>
      change (sp-_).toNat+8 ≤ ptr.toNat ∨ ptr.toNat+40 ≤ (sp-_).toNat <;>
      dsimp only [scratch] at below <;> bv_omega
  have saved₃ : memLoad built (sp-16) 64 = a[3].get 64 := by
    rw [savedLoad 16 (Or.inr rfl)]
    simp (disch := store_disch) only [pushed, push, memLoad_memStore_same, memLoad_memStore_of_rangeApart]
  have saved₁₄ : memLoad built (sp-8) 64 = a[14].get 64 := by
    rw [savedLoad 8 (Or.inl rfl)]
    simp (disch := store_disch) only [pushed, push, memLoad_memStore_same, memLoad_memStore_of_rangeApart]
  have retRead : LoadOk built sp 8 :=
    ⟨entry.returnSlot.low, (entry.returnSlot.of_frame wholeFrame).present⟩
  have retWord : memLoad built sp 64 = memLoad m sp 64 := by
    apply wholeFrame.memLoad_eq
    have top := entry.returnSlot.low
    refine ⟨by omega, fun x hx => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · right
      dsimp only [scratch]
      have room := entry.room
      omega
    · rcases dest.2 ⟨sp.toNat, 8⟩ (by simp) with h | h
      · right
        exact h
      · exact Or.inl h
  have popLoad (k : BitVec 64) (hk₁ : k.toNat ≤ 24) (hk₂ : 8 ≤ k.toNat) :
      LoadOk built (sp-k) 8 :=
    let r := (stackSlot entry hk₁ hk₂).readable.of_frame wholeFrame
    ⟨r.low, r.present⟩
  have pop₃ := popLoad 16 (by decide) (by decide)
  have pop₁₄ := popLoad 8 (by decide) (by decide)
  have sub16 : sp - 24 + 8 = sp - 16 := by bv_omega
  have sub8 : sp - 16 + 8 = sp - 8 := by bv_omega
  have sub0 : sp - 8 + 8 = sp := by bv_omega
  have restore (i : Fin Reg.count) (h : i.val ∈ [3,5,12,13,14,15]) :
      (⟨64, a[i].get 64⟩ : Value) = a[i] := by
    have wid := entry.saved i h
    cases av : a[i] with
    | mk w bits =>
      rw [av] at wid
      cases wid
      rfl
  have fromPush : memStore
      (memStore (memStore m (sp-8) (a[14].get 64)) (sp-16) (a[3].get 64))
      (sp-24) (a[0].get 64) = pushed := rfl
  refine ⟨?out, ?exec, ?post, ?words⟩
  case exec =>
    refine jump (b := ?_) (n := pushed) (target := .l1241ec) ?edge ?_
    case edge =>
      cfg_eval [rsp, di, dx, push₁, push₂, push₃, testFlags, show ((16 : BitVec 64) == 0) = false by decide]
      rw [ite_eq_left push₃]
    refine jump (b := ?_) (n := pushed) (target := .l124237) ?edge ?_
    case edge =>
      cfg_eval [dx]
      rfl
    refine jump (b := ?_) (n := pushed) (target := .l124247) ?edge ?_
    case edge =>
      dsimp only [pushed, push] at readLow lowWord
      have z : (addSpec (16 : BitVec 64) 0xfffffffffffffff8).snd.ZF = false := by decide
      cfg_eval [dx, si, readLow, lowWord, z]
      first | rfl | rw [ite_eq_left readLow, lowWord]
    refine jump (b := ?_) (n := pushed) (target := .l124278) ?edge ?_
    case edge =>
      cfg_eval [dx]
      rfl
    refine jump (b := ?_) (n := pushed) (target := .l124215) ?edge ?_
    case edge =>
      dsimp only [pushed, push] at readHigh highWord
      cfg_eval [dx, si, readHigh, highWord]
      simp only [readHigh, highWord, ite_true]
      <;> rfl
    refine done ?_
    cfg_eval [sub16, sub8, sub0, fromPush, toNext, toLen, toIndex, toLow, toBuilt]
    simp only [fromPush, w₀, toNext, w₁, toLen, w₂, toIndex, w₃, toLow, w₄, toBuilt, pop₃,
      pop₁₄, retRead, retWord, entry.returnLow, saved₃, saved₁₄, and_self, ite_true]
    <;> exact Eq.refl _
  case post =>
    refine ⟨rfl, rfl, ?_, wholeFrame⟩
    intro ⟨i, bound⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | exact restore 3 (by decide) | exact restore 14 (by decide)
  case words => exact setup_words pushed ptr (src+16) low high

end K256.Proofs.Verify.Core.Lincomb.Recode
