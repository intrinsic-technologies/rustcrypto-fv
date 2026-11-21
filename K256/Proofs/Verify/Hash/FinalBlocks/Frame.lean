import K256.Proofs.Verify.Hash.FinalBlocks.CallSetup
import K256.Proofs.Verify.Hash.Compression.Interface

namespace K256.Proofs.Verify.Hash.FinalBlocks

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def footprint (sp : Word) : List MemoryRegion :=
  [⟨sp.toNat - 344,344⟩, ⟨sp.toNat + 8,96⟩, ⟨sp.toNat + 160,64⟩]

abbrev Window (m : Ram) (sp : Word) := Writable Extracted.programImage m (sp - 344) 568

theorem window_low {m : Ram} {sp : Word} (win : Window m sp) (depth : 344 ≤ sp.toNat) :
    sp.toNat + 224 ≤ 2^32 := by
  have h := win.readable.low
  rw [BitVec.toNat_sub_of_le (show (344 : Word) ≤ sp from depth)] at h
  change sp.toNat - 344 + 568 ≤ 2^32 at h
  omega

theorem clearWithin (sp : Word) (low : sp.toNat + 224 ≤ 2^32) :
    RegionsWithin [⟨(sp+8).toNat,56⟩] (footprint sp) := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
  change sp.toNat + 8 ≤ (sp+8).toNat ∧ (sp+8).toNat + 56 ≤ sp.toNat + 8 + 96
  simp only [BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow]
  omega

theorem calleeWithin (sp : Word) (depth : 344 ≤ sp.toNat) (low : sp.toNat + 224 ≤ 2^32) :
    RegionsWithin (Compression.footprint (sp-8) (sp+72)) (footprint sp) := by
  intro r hr
  simp only [Compression.footprint, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨_, List.mem_cons_self, ?_⟩
    change sp.toNat - 344 ≤ (sp-8).toNat - 336 ∧ (sp-8).toNat - 336 + 336 ≤ sp.toNat - 344 +344
    rw [BitVec.toNat_sub_of_le (show (8 : Word) ≤ sp from (show 8 ≤ sp.toNat by omega))]
    change _ ≤ sp.toNat - 8 - 336 ∧ sp.toNat - 8 - 336 + 336 ≤ _
    omega
  · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    change sp.toNat + 8 ≤ (sp+72).toNat ∧ (sp+72).toNat +32 ≤ sp.toNat + 8 +96
    simp only [BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow]
    omega

theorem preparedWrites (last : Bool) (m : Ram) (sp length : Word)
    (depth : 344 ≤ sp.toNat) (low : sp.toNat +224 ≤ 2^32) :
    RamWriteFrame m (callMemory last m sp length) (footprint sp) := by
  have sub : RegionsWithin (stageRegions sp) (footprint sp) := by
    intro r hr
    simp only [stageRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨_, List.mem_cons_self, ?_⟩
      change sp.toNat - 344 ≤ (sp-8).toNat ∧ (sp-8).toNat + 8 ≤ sp.toNat - 344 +344
      rw [BitVec.toNat_sub_of_le (show (8 : Word) ≤ sp from (show 8 ≤ sp.toNat by omega))]
      change _ ≤ sp.toNat - 8 ∧ sp.toNat - 8 +8 ≤ _
      omega
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
      change sp.toNat +160 ≤ (sp+160).toNat ∧ (sp+160).toNat +64 ≤ sp.toNat +160+64
      simp only [BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow]
      omega
  have dep : 8 ≤ sp.toNat := by omega
  have room : sp.toNat + 224 ≤ 2^64 := by omega
  have base := RamWriteFrame.refl m (footprint sp)
  cases last <;> simp only [callMemory, Bool.false_eq_true, ite_false, ite_true]
  · exact base.trans (stage_frame m sp (memLoad m (sp+64) 64) (returnAddress false) dep room) sub
  · have slot : InRegions (footprint sp) (sp+64) 8 := by
      refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      change sp.toNat+8 ≤ (sp+64).toNat ∧ (sp+64).toNat + 8 ≤ sp.toNat+8+96 ∧ _
      simp only [BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow]
      omega
    exact (base.memStore length slot).trans
      (stage_frame (memStore m (sp+64) length) sp length (returnAddress true) dep room) sub

theorem preparedReturn (last : Bool) (m : Ram) (sp length : Word) :
    memLoad (callMemory last m sp length) (sp-8) 64 = returnAddress last := by
  cases last <;> simp only [callMemory, Bool.false_eq_true, ite_false, ite_true]
  · exact stage_return m sp (memLoad m (sp+64) 64) (returnAddress false)
  · exact stage_return (memStore m (sp+64) length) sp length (returnAddress true)

theorem stateOutside {m t : Ram} {sp : Word} {hash : Array UInt32} {rs : List MemoryRegion}
    (state : Compression.StateAt m (sp+72) hash)
    (f : RamWriteFrame m t rs) (low : sp.toNat + 224 ≤ 2^32)
    (dis : ∀ r ∈ rs, r.start + r.size ≤ sp.toNat + 72 ∨ sp.toNat + 104 ≤ r.start) :
    Compression.StateAt t (sp+72) hash := by
  refine ⟨state.1, fun i hi => (f.memLoad_eq ?_).trans (state.2 i hi)⟩
  have ha : (wordAddr (sp+72) 32 i).toNat = sp.toNat + 72 + 4*i := by
    change ((sp+72) + BitVec.ofNat 64 (4*i)).toNat = _
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]
    omega
  refine ⟨by rw [ha]; omega, fun r hr => ?_⟩
  rw [ha]
  rcases dis r hr with h | h <;> omega

theorem preparedState (last : Bool) (m : Ram) (sp length : Word) {hash : Array UInt32}
    (state : Compression.StateAt m (sp+72) hash) (depth : 344 ≤ sp.toNat)
    (low : sp.toNat + 224 ≤ 2^32) :
    Compression.StateAt (callMemory last m sp length) (sp+72) hash := by
  have dis : ∀ r ∈ stageRegions sp, r.start + r.size ≤ sp.toNat + 72 ∨ sp.toNat + 104 ≤ r.start := by
    intro r hr
    simp only [stageRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · apply Or.inl
      change (sp-8).toNat+8 ≤ _
      rw [BitVec.toNat_sub_of_le (show (8 : Word) ≤ sp from (show 8 ≤ sp.toNat by omega))]
      change sp.toNat-8+8 ≤ _
      omega
    · apply Or.inr
      change _ ≤ (sp+160).toNat
      simp only [BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow]
      omega
  have dep : 8 ≤ sp.toNat := by omega
  have room : sp.toNat + 224 ≤ 2^64 := by omega
  cases last <;> simp only [callMemory, Bool.false_eq_true, ite_false, ite_true]
  · exact stateOutside state (stage_frame m sp (memLoad m (sp+64) 64) (returnAddress false) dep room) low dis
  · have apart : RangeApart (sp+64) 8 (sp+72) 32 := RangeApart.of_offsets rfl rfl (by decide)
    have written : Compression.StateAt (memStore m (sp+64) length) (sp+72) hash :=
      ⟨state.1, state.2.write_apart _ _ apart⟩
    exact stateOutside written (stage_frame (memStore m (sp+64) length) sp length (returnAddress true) dep room) low dis

end K256.Proofs.Verify.Hash.FinalBlocks
