import K256.Proofs.Signing.Hash.Finish.CallSetup
import K256.Proofs.Verify.Hash.FinalBlocks.Frame

namespace K256.Proofs.Signing.Hash.Finish

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash

theorem clearWithin (sp : Word) (depth : 512 ≤ sp.toNat) (limit : sp.toNat + 1160 < 2^32) :
    RegionsWithin [⟨(sp+8).toNat,56⟩] (regions sp) := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨_,List.mem_cons_self,?_⟩
  change sp.toNat-512 ≤ (sp+8).toNat ∧ (sp+8).toNat+56 ≤ sp.toNat-512+624
  simp only [BitVec.toNat_add,BitVec.reduceToNat,Nat.reducePow]
  omega

theorem calleeWithin (sp : Word) (depth : 512 ≤ sp.toNat) (limit : sp.toNat + 1160 < 2^32) :
    RegionsWithin (Compression.footprint (sp-8) (sp+72)) (regions sp) := by
  intro r hr
  refine ⟨_, List.mem_cons_self, ?_⟩
  simp only [Compression.footprint,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;>
    simp only [BitVec.toNat_sub,BitVec.toNat_add,BitVec.reduceToNat,Nat.reducePow] <;> omega

theorem preparedWrites (last : Bool) (m : Ram) (sp length : Word)
    (depth : 512 ≤ sp.toNat) (limit : sp.toNat + 1160 < 2^32) :
    RamWriteFrame m (callMemory last m sp length) (regions sp) := by
  have sub : RegionsWithin (stageRegions sp) (regions sp) := by
    intro r hr
    simp only [stageRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨_,List.mem_cons_self,?_⟩
      change sp.toNat-512 ≤ (sp-8).toNat ∧ (sp-8).toNat+8 ≤ sp.toNat-512+624
      simp only [BitVec.toNat_sub,BitVec.reduceToNat,Nat.reducePow]; omega
    · refine ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,?_⟩
      change sp.toNat+256 ≤ (sp+256).toNat ∧ (sp+256).toNat+64 ≤ sp.toNat+256+64
      simp only [BitVec.toNat_add,BitVec.reduceToNat,Nat.reducePow]; omega
  have dep : 8 ≤ sp.toNat := by omega
  have room : sp.toNat + 320 ≤ 2^64 := by omega
  have base := RamWriteFrame.refl m (regions sp)
  cases last <;> simp only [callMemory,Bool.false_eq_true,ite_false,ite_true]
  · exact base.trans (stage_frame _ _ _ _ dep room) sub
  · have slot : InRegions (regions sp) (sp+64) 8 := by
      refine ⟨_,List.mem_cons_self,?_⟩
      change sp.toNat-512 ≤ (sp+64).toNat ∧ (sp+64).toNat+8 ≤ sp.toNat-512+624 ∧ _
      simp only [BitVec.toNat_add,BitVec.reduceToNat,Nat.reducePow]; omega
    exact (base.memStore length slot).trans (stage_frame _ _ _ _ dep room) sub

theorem preparedReturn (last : Bool) (m : Ram) (sp length : Word) :
    memLoad (callMemory last m sp length) (sp-8) 64 = returnAddress last := by
  cases last <;> simp only [callMemory, Bool.false_eq_true, ite_false, ite_true]
  · exact stage_return m sp (memLoad m (sp+64) 64) (returnAddress false)
  · exact stage_return (memStore m (sp+64) length) sp length (returnAddress true)

theorem preparedState (last : Bool) (m : Ram) (sp length : Word) {hash : Array UInt32}
    (state : Compression.StateAt m (sp+72) hash) (depth : 344 ≤ sp.toNat)
    (low : sp.toNat + 320 ≤ 2^32) :
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
      change _ ≤ (sp+256).toNat
      simp only [BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow]
      omega
  have dep : 8 ≤ sp.toNat := by omega
  have room : sp.toNat + 320 ≤ 2^64 := by omega
  cases last <;> simp only [callMemory, Bool.false_eq_true, ite_false, ite_true]
  · exact FinalBlocks.stateOutside state (stage_frame m sp (memLoad m (sp+64) 64) (returnAddress false) dep room) (by omega) dis
  · have apart : RangeApart (sp+64) 8 (sp+72) 32 := RangeApart.of_offsets rfl rfl (by decide)
    have written : Compression.StateAt (memStore m (sp+64) length) (sp+72) hash :=
      ⟨state.1, state.2.write_apart _ _ apart⟩
    exact FinalBlocks.stateOutside written (stage_frame (memStore m (sp+64) length) sp length (returnAddress true) dep room) (by omega) dis

end K256.Proofs.Signing.Hash.Finish
