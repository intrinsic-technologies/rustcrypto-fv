import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.Runtime.Guards

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem inRegions_add_offset {regions : List MemoryRegion} {base : BitVec 64}
    {len off n : Nat} (h : InRegions regions base len) (hn0 : 0 < n)
    (hn : off + n ≤ len) : InRegions regions (base + BitVec.ofNat 64 off) n := by
  obtain ⟨r, hr, hstart, hend, hbound⟩ := h
  have ho : off < 2^64 := by omega
  have hsum : base.toNat + off < 2^64 := by omega
  refine ⟨r, hr, ?_⟩
  simp only [InRegion, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho, Nat.mod_eq_of_lt hsum]
  omega

theorem outside_add_offset {regions : List MemoryRegion} {base : BitVec 64}
    {len off n : Nat} (h : Outside regions base len) (hn0 : 0 < n)
    (hn : off + n ≤ len) : Outside regions (base + BitVec.ofNat 64 off) n := by
  have ho : off < 2^64 := by have := h.1; omega
  have hsum : base.toNat + off < 2^64 := by have := h.1; omega
  have he : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho, Nat.mod_eq_of_lt hsum]
  constructor
  · rw [he]
    have := h.1
    omega
  · intro r hr
    have := h.2 r hr
    rw [he]
    omega

theorem memLoad_store_word4 (mem : Ram) (base : BitVec 64) (i j : Fin 4) (v : BitVec 64) :
    memLoad (memStore mem (base + BitVec.ofNat 64 (8*i.val)) v)
      (base + BitVec.ofNat 64 (8*j.val)) 64 =
      if i = j then v else memLoad mem (base + BitVec.ofNat 64 (8*j.val)) 64 := by
  by_cases h : i = j
  · subst j
    simp only [ite_true]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · simp only [h, ite_false]
    apply memLoad_memStore_of_rangeApart
    apply RangeApart.of_offsets rfl rfl
    have hp : ∀ i j : Fin 4, i ≠ j →
        8 ≤ (BitVec.ofNat 64 (8*j.val) - BitVec.ofNat 64 (8*i.val)).toNat ∧
        8 ≤ (BitVec.ofNat 64 (8*i.val) - BitVec.ofNat 64 (8*j.val)).toNat := by decide +kernel
    exact hp i j h

end AesGcm.Proofs.Machine.GHASHUpdate
