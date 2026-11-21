import AesGcm.Proofs.AES16.KeySchedule.Generation.State

namespace AesGcm.Proofs.Machine.AES16.KeySchedule.Generation

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem stack_sub_toNat {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (h : MemoryReady use256 code mem sp) : (sp - 248).toNat = sp.toNat - 248 := by
  have := h.hroom
  bv_omega

theorem stack_limit {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (h : MemoryReady use256 code mem sp) :
    sp.toNat + (if use256 then 360 else 264) ≤ 2 ^ 32 := by
  have hl := h.hstack.readable.low
  rw [stack_sub_toNat h] at hl
  have := h.hroom
  cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega

theorem address_toNat {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (h : MemoryReady use256 code mem sp) (off : Nat)
    (hoff : off ≤ (if use256 then 240 else 176)) :
    (base use256 sp + BitVec.ofNat 64 off).toNat =
      sp.toNat + (if use256 then 12 else 8) + off := by
  have hl := stack_limit h
  cases use256 <;>
    simp only [base, Bool.false_eq_true, ↓reduceIte] at * <;>
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat] <;>
    rw [Nat.mod_eq_of_lt (a := sp.toNat + _) (by omega),
      Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem base_toNat {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (h : MemoryReady use256 code mem sp) :
    (base use256 sp).toNat = sp.toNat + (if use256 then 12 else 8) := by
  simpa only [BitVec.reduceOfNat, BitVec.add_zero, Nat.add_zero] using
    address_toNat h 0 (by cases use256 <;> decide)

theorem roundRegions_within {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (h : MemoryReady use256 code mem sp) (round : Nat) (hr : round ≤ (variant use256).Nr) :
    RegionsWithin (roundRegions use256 sp round) (regions use256 sp) := by
  have hbound : 16 * round + 16 ≤ (if use256 then 240 else 176) := by
    cases use256 <;> simp only [variant, Variant.Nr, Bool.false_eq_true, ↓reduceIte] at * <;>
      omega
  intro region hregion
  simp only [roundRegions, List.mem_cons, List.not_mem_nil, or_false] at hregion
  rcases hregion with rfl | rfl
  · exact ⟨span (sp - 248) 248, List.Mem.head _, Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨span (base use256 sp) (if use256 then 240 else 176),
      List.Mem.tail _ (List.Mem.head _), ?_, ?_⟩
    all_goals simp only [span, address_toNat h (16 * round) (by omega), base_toNat h]
    all_goals omega

theorem regions_within_stack {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (h : MemoryReady use256 code mem sp) :
    RegionsWithin (regions use256 sp)
      [span (sp - 248) (if use256 then 608 else 512)] := by
  intro region hregion
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hregion
  rcases hregion with rfl | rfl
  · refine ⟨span (sp - 248) (if use256 then 608 else 512), List.Mem.head _,
      Nat.le_refl _, ?_⟩
    cases use256 <;> simp only [span, Bool.false_eq_true, ↓reduceIte] <;> omega
  · refine ⟨span (sp - 248) (if use256 then 608 else 512), List.Mem.head _, ?_, ?_⟩
    all_goals simp only [span, stack_sub_toNat h, base_toNat h]
    all_goals have := h.hroom
    all_goals cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem memoryReady_of_frame {use256 : Bool} {code : CodeMap} {before after : Ram}
    {sp : BitVec 64} {footprint : List MemoryRegion}
    (h : MemoryReady use256 code before sp)
    (hf : RamWriteFrame before after footprint)
    (hwithin : RegionsWithin footprint
      [span (sp - 248) (if use256 then 608 else 512)]) :
    MemoryReady use256 code after sp := by
  have hfull : RamWriteFrame before after
      [span (sp - 248) (if use256 then 608 else 512)] :=
    (RamWriteFrame.refl before _).trans hf hwithin
  have outside (slot : BitVec 64) (hs : slot = 0x201210 ∨ slot = 0x201230) :
      Outside [span (sp - 248) (if use256 then 608 else 512)] slot 8 := by
    refine ⟨by rcases hs with rfl | rfl <;> decide, ?_⟩
    intro region hregion
    simp only [List.mem_singleton] at hregion
    subst region
    have hap := h.hslotsApart
    have hlo := h.hroom
    simp only [span, stack_sub_toNat h]
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;>
      rcases hs with rfl | rfl <;> simp only [BitVec.reduceToNat] <;> omega
  exact ⟨h.hstack.of_frame hfull, h.hroom, h.hAlign, h.hreadPanic.of_frame hfull,
    (hfull.memLoad_eq (outside _ (Or.inl rfl))).trans h.hpanic,
    h.hreadBounds.of_frame hfull, (hfull.memLoad_eq (outside _ (Or.inr rfl))).trans h.hbounds,
    h.hslotsApart⟩

theorem prefix_of_round {use256 : Bool} {code : CodeMap} {before after : Ram}
    {sp : BitVec 64} (h : MemoryReady use256 code before sp)
    (key : Vector UInt8 (variant use256).keyBytes) (round : Nat)
    (hr : round ≤ (variant use256).Nr)
    (hp : RawSchedulePrefix (variant use256) key round (base use256 sp) before)
    (hf : RamWriteFrame before after (roundRegions use256 sp round))
    (hnew : ∀ p : Fin 8,
      memLoad after (base use256 sp + BitVec.ofNat 64 (16 * round + 2 * p.val)) 16 =
        Fixslice16.encodeStandard (Machine.KeySchedule.roundKeyBlock (variant use256) key
          ⟨round, by omega⟩) p) :
    RawSchedulePrefix (variant use256) key (round + 1) (base use256 sp) after := by
  intro r hround p
  by_cases he : r.val = round
  · have heq : r = ⟨round, by omega⟩ := Fin.ext he
    rw [heq]
    exact hnew p
  · have hlt : r.val < round := by omega
    have hbound : 16 * round + 16 ≤ (if use256 then 240 else 176) := by
      cases use256
      · change round ≤ 10 at hr
        change 16 * round + 16 ≤ 176
        omega
      · change round ≤ 14 at hr
        change 16 * round + 16 ≤ 240
        omega
    have haddr := address_toNat h (16 * r.val + 2 * p.val) (by have := p.isLt; omega)
    have hnext := address_toNat h (16 * round) (by omega)
    rw [hf.memLoad_eq]
    · exact hp r hlt p
    · refine ⟨?_, ?_⟩
      · rw [haddr]
        have := stack_limit h
        have := p.isLt
        cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
      · intro region hregion
        simp only [roundRegions, List.mem_cons, List.not_mem_nil, or_false] at hregion
        rcases hregion with rfl | rfl
        · simp only [span, haddr, stack_sub_toNat h]
          have := h.hroom
          omega
        · simp only [span, haddr, hnext]
          have := p.isLt
          omega

end AesGcm.Proofs.Machine.AES16.KeySchedule.Generation
