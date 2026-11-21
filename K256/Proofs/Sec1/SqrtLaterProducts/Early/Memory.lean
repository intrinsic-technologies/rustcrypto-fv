import K256.Proofs.Sec1.SqrtLaterProducts.Early.Call

namespace K256.Proofs.Sec1.SqrtLaterProducts.Early

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field

def scratchRegion (sp : Word) : MemoryRegion := ⟨(sp - 8).toNat, 392⟩

theorem offsetNat {sp off : Word} (hlow : sp.toNat + 432 ≤ 2^32) (hoff : off.toNat ≤ 440) :
    (sp + off).toNat = sp.toNat + off.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

theorem pushedFrame {m scratch : Ram} {sp ret : Word} {offsets : List Word}
    (writes : Final.ScratchWrites m scratch sp offsets)
    (hbase : 8 ≤ sp.toNat) (hlow : sp.toNat + 432 ≤ 2^32)
    (bounded : ∀ off ∈ offsets, off.toNat ≤ 376) :
    RamWriteFrame m (memStore scratch (sp - 8) ret) [scratchRegion sp] := by
  have ha := BitVec.toNat_sub_of_le (x := sp) (y := 8) (by change 8 ≤ sp.toNat; exact hbase)
  change (sp - 8).toNat = sp.toNat - 8 at ha
  apply RamWriteFrame.memStore
  · apply writes
    intro off ho
    have hb := bounded off ho
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change (sp - 8).toNat ≤ _ ∧ _ + 8 ≤ (sp - 8).toNat + 392 ∧ _ + 8 ≤ 2^64
    rw [ha, offsetNat hlow (by omega : off.toNat ≤ 440)]
    omega
  · refine ⟨_, List.mem_singleton_self _, Nat.le_refl _, ?_, ?_⟩ <;>
      change (sp - 8).toNat + 8 ≤ _ <;> dsimp [scratchRegion] <;> omega

theorem retained {m scratch : Ram} {sp ret k : Word} {offsets : List Word}
    (writes : Final.ScratchWrites m scratch sp offsets)
    (hbase : 8 ≤ sp.toNat) (hlow : sp.toNat + 432 ≤ 2^32) (hk : k.toNat ≤ 440)
    (apart : ∀ off ∈ offsets, off.toNat ≤ 440 ∧
      (k.toNat + 8 ≤ off.toNat ∨ off.toNat + 8 ≤ k.toNat)) :
    memLoad (memStore scratch (sp - 8) ret) (sp + k) 64 = memLoad m (sp + k) 64 := by
  let regions := offsets.map fun off => (⟨(sp + off).toNat, 8⟩ : MemoryRegion)
  have frame : RamWriteFrame m (memStore scratch (sp - 8) ret)
      (⟨(sp - 8).toNat, 8⟩ :: regions) := by
    apply RamWriteFrame.memStore
    · apply writes
      intro off ho
      have hb := (apart off ho).1
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨off, ho, rfl⟩),
        Nat.le_refl _, Nat.le_refl _, by rw [offsetNat hlow hb]; omega⟩
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _,
        by have := BitVec.toNat_sub_of_le (x := sp) (y := 8) (by change 8 ≤ sp.toNat; exact hbase)
           change (sp - 8).toNat + 8 ≤ 2^64
           omega⟩
  apply frame.memLoad_eq
  refine ⟨by rw [offsetNat hlow hk]; change sp.toNat + k.toNat + 8 ≤ _; omega, ?_⟩
  intro r hr
  rcases List.mem_cons.mp hr with hr | hr
  · subst r
    right
    change (sp - 8).toNat + 8 ≤ (sp + k).toNat
    rw [BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; exact hbase), offsetNat hlow hk]
    change sp.toNat - 8 + 8 ≤ _
    omega
  · obtain ⟨off, ho, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hb, hd⟩ := apart off ho
    change (sp + k).toNat + 8 ≤ (sp + off).toNat ∨ (sp + off).toNat + 8 ≤ (sp + k).toNat
    rw [offsetNat hlow hk, offsetNat hlow hb]
    omega

end K256.Proofs.Sec1.SqrtLaterProducts.Early
