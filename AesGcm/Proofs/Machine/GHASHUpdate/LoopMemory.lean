import AesGcm.Proofs.Machine.GHASHUpdate.Blocks
import AesGcm.Proofs.Machine.GHASHUpdate.Memory

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASHInterface

theorem updateBlocks_of_frame {mem out : Ram} {regions : List MemoryRegion}
    (hf : RamWriteFrame mem out regions) (src : BitVec 64) (n : Nat)
    (hs : Outside regions src (16*n)) (y0 y1 : BitVec 64) (initial : BitVec 64 × BitVec 64) :
    updateBlocks out src n y0 y1 initial = updateBlocks mem src n y0 y1 initial := by
  apply updateBlocks_congr
  · intro j hj
    exact hf.memLoad_eq (outside_add_offset hs (by decide) (by omega))
  · intro j hj
    exact hf.memLoad_eq (outside_add_offset hs (by decide) (by omega))

theorem stateKey_outside (r : MemoryRegion) (dst : BitVec 64)
    (hr : 0 < r.size) (hd : dst.toNat + 32 ≤ 2^32)
    (hsep : r.Disjoint (span dst 32)) :
    Outside [r, span (dst + 16) 16] dst 16 := by
  have ha := disjoint_bounds r.start r.size dst.toNat 32 hr (by decide) hsep
  have hd16 : (dst + 16).toNat = dst.toNat + 16 := by
    simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.reduceToNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨by omega, ?_⟩
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · omega
  · simp only [span, hd16]
    omega

theorem input_outside (r : MemoryRegion) (dst src : BitVec 64) (n : Nat)
    (hr : 0 < r.size) (hn : 0 < n) (hd : dst.toNat + 32 ≤ 2^32)
    (hs : src.toNat + n ≤ 2^32) (hstack : r.Disjoint (span src n))
    (hstate : (span dst 32).Disjoint (span src n)) :
    Outside [r, span (dst + 16) 16] src n := by
  have ha := disjoint_bounds r.start r.size src.toNat n hr hn hstack
  have hb := disjoint_bounds dst.toNat 32 src.toNat n (by decide) hn hstate
  have hd16 : (dst + 16).toNat = dst.toNat + 16 := by
    simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.reduceToNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨by omega, ?_⟩
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · omega
  · simp only [span, hd16]
    omega

end AesGcm.Proofs.Machine.GHASHUpdate
