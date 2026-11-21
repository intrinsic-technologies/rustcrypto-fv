import K256.Proofs.Verify.Core.Lincomb.Recode.Setup

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

theorem writesScratch {sp dst : BitVec 64} :
    RegionsWithin [scratch sp 0x110] (writes sp dst) := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩

theorem writesDigits {sp dst : BitVec 64} :
    RegionsWithin [⟨dst.toNat,257⟩] (writes sp dst) := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩

theorem subNatConst {sp : BitVec 64} {k : Nat} (h : k ≤ sp.toNat) :
    (sp - BitVec.ofNat 64 k).toNat = sp.toNat-k := by
  have bound := sp.isLt
  have off : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
  rw [subNat (by rw [off]; exact h), off]

theorem childInside {sp : BitVec 64} (room : 0x110 ≤ sp.toNat) :
    RegionsWithin [scratch (sp-144) 24, ⟨(sp-88).toNat,40⟩] [scratch sp 0x110] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  refine ⟨scratch sp 0x110, List.mem_singleton_self _, ?_⟩
  have lo : (sp-144).toNat = sp.toNat-144 := subNatConst (k := 144) (by omega)
  have hi : (sp-88).toNat = sp.toNat-88 := subNatConst (k := 88) (by omega)
  rcases hr with rfl | rfl
  · change sp.toNat-0x110 ≤ (sp-144).toNat-24 ∧ (sp-144).toNat-24+24 ≤ sp.toNat-0x110+0x110
    rw [lo]
    omega
  · change sp.toNat-0x110 ≤ (sp-88).toNat ∧ (sp-88).toNat+40 ≤ sp.toNat-0x110+0x110
    rw [hi]
    omega

theorem childWrites {sp dst : BitVec 64} (room : 0x110 ≤ sp.toNat) :
    RegionsWithin [scratch (sp-144) 24, ⟨(sp-88).toNat,40⟩] (writes sp dst) := by
  intro r hr
  obtain ⟨big, hb, lb, ub⟩ := childInside room r hr
  obtain rfl := List.mem_singleton.mp hb
  exact ⟨_, List.mem_cons_self, lb, ub⟩

theorem slotOutsideDigits {sp dst : BitVec 64} {off : BitVec 64} {len : Nat}
    (room : 0x110 ≤ sp.toNat) (low : sp.toNat + 8 ≤ 2^32)
    (lower : off.toNat ≤ 0x110) (upper : len ≤ off.toNat)
    (apart : Outside [scratch sp 0x110, ⟨sp.toNat,8⟩] dst 257) :
    Outside [⟨dst.toNat,257⟩] (sp-off) len := by
  refine ⟨by rw [subNat (by omega)]; omega, fun r hr => ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  have h := apart.2 (scratch sp 0x110) List.mem_cons_self
  simp only [scratch] at h
  change (sp-off).toNat+len ≤ dst.toNat ∨ dst.toNat+257 ≤ (sp-off).toNat
  rw [subNat (by omega)]
  rcases h with h | h
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

theorem skipChildWrites {sp : BitVec 64} {off : BitVec 64} {len : Nat}
    (room : 0x110 ≤ sp.toNat) (low : sp.toNat+8 ≤ 2^32)
    (lower : off.toNat ≤ 136) (upper : len ≤ off.toNat)
    (away : 88 + len ≤ off.toNat ∨ off.toNat ≤ 48) :
    Outside [scratch (sp-144) 24, ⟨(sp-88).toNat,40⟩] (sp-off) len := by
  have s : (sp-off).toNat = sp.toNat - off.toNat := subNat (by omega)
  have first : (sp-144).toNat = sp.toNat-144 := subNatConst (k := 144) (by omega)
  have second : (sp-88).toNat = sp.toNat-88 := subNatConst (k := 88) (by omega)
  refine ⟨by rw [s]; omega, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp only [scratch, s, first]
    exact Or.inr (by omega)
  · simp only [s, second]
    rcases away with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

theorem SavedAt.of_frame {a : Registers} {sp : BitVec 64} {m m' : Ram} {rs : List MemoryRegion}
    (saved : SavedAt a sp m) (frame : RamWriteFrame m m' rs)
    (slot : ∀ k : BitVec 64, 8 ≤ k.toNat → k.toNat ≤ 48 → Outside rs (sp-k) 8) :
    SavedAt a sp m' := by
  intro j
  have off : (BitVec.ofNat 64 (8*(j.val+1))).toNat = 8*(j.val+1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := j.isLt; omega)]
  have outside := slot (BitVec.ofNat 64 (8*(j.val+1)))
    (by rw [off]; omega) (by rw [off]; have := j.isLt; omega)
  exact (frame.memLoad_eq outside).trans (saved j)

theorem LoopMemory.of_frame {m m' : Ram} {sp dst : BitVec 64} {rs : List MemoryRegion}
    (fields : LoopMemory m sp dst) (frame : RamWriteFrame m m' rs)
    (slot : ∀ k : BitVec 64, ∀ l : Nat, (l = 4 ∨ l = 8) →
      88 + l ≤ k.toNat → k.toNat ≤ 136 → Outside rs (sp-k) l) :
    LoopMemory m' sp dst :=
  ⟨(frame.memLoad_eq (slot 136 8 (Or.inr rfl) (by decide) (by decide))).trans fields.limit,
    (frame.memLoad_eq (slot 124 4 (Or.inl rfl) (by decide) (by decide))).trans fields.radix,
    (frame.memLoad_eq (slot 120 8 (Or.inr rfl) (by decide) (by decide))).trans fields.buffer,
    (frame.memLoad_eq (slot 112 8 (Or.inr rfl) (by decide) (by decide))).trans fields.bits,
    (frame.memLoad_eq (slot 104 8 (Or.inr rfl) (by decide) (by decide))).trans fields.half,
    (frame.memLoad_eq (slot 96 8 (Or.inr rfl) (by decide) (by decide))).trans fields.mask⟩

theorem bufferSeparate {sp : BitVec 64} (room : 0x110 ≤ sp.toNat) (low : sp.toNat+8 ≤ 2^32) :
    Outside [scratch (sp-144) 24, ⟨(sp-144).toNat,8⟩] (sp-88) 40 := by
  have base : (sp-88).toNat = sp.toNat-88 := subNatConst (k := 88) (by omega)
  have child : (sp-144).toNat = sp.toNat-144 := subNatConst (k := 144) (by omega)
  refine ⟨by rw [base]; omega, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> right <;> simp only [scratch, base, child] <;> omega

theorem writableOutsideCode {m : Ram} {a : BitVec 64} {n : Nat}
    (w : Writable Extracted.programImage m a n) (v : BitVec 64 × UInt8)
    (hv : v ∈ Extracted.programImage) :
    v.1.toNat + 1 ≤ a.toNat ∨ a.toNat+n ≤ v.1.toNat := by
  by_cases lower : v.1.toNat < a.toNat
  · exact Or.inl (by omega)
  by_cases upper : a.toNat+n ≤ v.1.toNat
  · exact Or.inr upper
  exfalso
  have off : v.1.toNat-a.toNat < n := by omega
  apply w.notCode v hv _ off
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := v.1.isLt; omega),
    Nat.mod_eq_of_lt (by have := v.1.isLt; omega)]
  omega

theorem iteratorEntry {a b : Registers} {m m' : Ram} {sp dst ret : BitVec 64}
    (entry : RoutineEntry a m sp 0x110) (writable : Writable Extracted.programImage m dst 257)
    (frame : RamWriteFrame m m' (writes sp dst))
    (rsp : b[4] = ⟨64, sp-144⟩) (saved : ∀ i : Fin Reg.count,
      i.val ∈ [3,5,12,13,14,15] → b[i].width = 64)
    (control : ControlSaved a b)
    (retAt : memLoad m' (sp-144) 64 = ret) (low : ret.toNat < 2^32) :
    RoutineEntry b m' (sp-144) 24 := by
  have origRoom := entry.room
  have spNat : (sp-144).toNat = sp.toNat-144 := subNatConst (k := 144) (by omega)
  have aligned := entry.aligned
  have sub : sp-144 - 24 = sp-168 := by bv_omega
  have stack : Writable Extracted.programImage m' (sp-144 - 24) 24 := by
    rw [sub]
    exact (stackSlot entry (off := 168) (by decide) (by decide)).of_frame frame
  have r := ((stackSlot entry (off := 144) (by decide) (by decide : 8 ≤ (144 : BitVec 64).toNat)).of_frame frame).readable
  refine ⟨rsp,saved,(control 22 (by decide)).trans entry.df, ?_, ?_, ?_,
    by rw [spNat]; omega, by rw [spNat]; omega, stack,r,by rw [retAt]; exact low,?_⟩
  · exact (congrArg Value.width (control 39 (by decide))).trans entry.mxcsr
  · exact (congrArg Value.width (control 50 (by decide))).trans entry.ftw
  · exact (congrArg Value.width (control 51 (by decide))).trans entry.fcw
  intro v hv
  rw [frame.outside _ ?_, entry.image v hv]
  have base : (sp - 0x110).toNat = sp.toNat - 0x110 := subNatConst (k := 0x110) (by omega)
  refine ⟨by have := v.1.isLt; omega, fun reg hr => ?_⟩
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have bounds := writableOutsideCode entry.stack v hv
    change v.1.toNat + 1 ≤ (sp - 0x110).toNat ∨ (sp - 0x110).toNat + 0x110 ≤ v.1.toNat at bounds
    rw [base] at bounds
    exact bounds
  · exact writableOutsideCode writable v hv

end K256.Proofs.Verify.Core.Lincomb.Recode
