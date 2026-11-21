import AesGcm.Proofs.Machine.Runtime.Guards
import AesGcm.Proofs.Machine.Runtime.Contracts

namespace AesGcm.Proofs.Machine.Runtime

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Refine

theorem outside_subregion {regions : List MemoryRegion} {base : BitVec 64}
    {size offset count : Nat} (h : Outside regions base size)
    (ho : offset < size) (hc : offset + count ≤ size) :
    Outside regions (base + BitVec.ofNat 64 offset) count := by
  have ha : (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
    have hb := h.1
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_⟩
  · rw [ha]
    have := h.1
    omega
  · intro r hr
    rw [ha]
    have := h.2 r hr
    omega

theorem outside_disjoint_span {regions : List MemoryRegion} {base : BitVec 64}
    {size : Nat} (h : Outside regions base size) (region : MemoryRegion)
    (hr : region ∈ regions) : (span base size).Disjoint region := by
  intro address ha hb
  have hs := h.2 region hr
  change base.toNat ≤ address ∧ address < base.toNat + size at ha
  change region.start ≤ address ∧ address < region.start + region.size at hb
  omega

theorem span_disjoint_activationRegion {fr : Activation} {ptr : BitVec 64} {n : Nat}
    (h : (callStack fr).Disjoint (span ptr n)) :
    (span ptr n).Disjoint fr.region := by
  intro addr hp hr
  apply h addr ?_ hp
  change fr.low.toNat ≤ addr ∧ addr < fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) at hr
  change fr.low.toNat ≤ addr ∧ addr < fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat)
  omega

theorem outside_activationRegion {mem : Ram} {fr : Activation} {ptr : BitVec 64} {n : Nat}
    (hr : Readable mem ptr n) (hn : 0 < n) (hlow : fr.low.toNat ≤ fr.rsp.toNat)
    (h : (callStack fr).Disjoint (span ptr n)) : Outside [fr.region] ptr n := by
  have hsep := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    ptr.toNat n (by omega) hn h
  refine ⟨Nat.le_trans hr.low (by decide), ?_⟩
  intro region hregion
  simp only [List.mem_singleton] at hregion
  subst region
  change ptr.toNat + n ≤ fr.low.toNat ∨
    fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ ptr.toNat
  omega

end AesGcm.Proofs.Machine.Runtime

