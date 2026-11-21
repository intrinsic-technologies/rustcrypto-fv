import K256.Proofs.Verify.Core.Lincomb.Interface

namespace K256.Proofs.Verify.Core.Lincomb.Double

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine

abbrev bottom (sp : BitVec 64) := sp - 0x298

abbrev below (sp : BitVec 64) (k : Nat) := bottom sp + BitVec.ofNat 64 k

def windows (sp : BitVec 64) (ranges : List (Nat × Nat)) : List MemoryRegion :=
  ranges.map fun (offset, len) => ⟨(below sp offset).toNat,len⟩

theorem edgeNat {lo : BitVec 64} (high : lo.toNat + 0x298 ≤ 2^32) {k : Nat}
    (hk : k ≤ 0x298) : (lo + BitVec.ofNat 64 k).toNat = lo.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem outsideWindows {sp : BitVec 64} {ranges : List (Nat × Nat)} {k n : Nat}
    (bound : (bottom sp).toNat + 0x298 ≤ 2^32) (fit : k + n ≤ 0x298)
    (areas : ∀ r ∈ ranges, r.1 + r.2 ≤ 0x298)
    (apart : ∀ r ∈ ranges, k + n ≤ r.1 ∨ r.1 + r.2 ≤ k) :
    Outside (windows sp ranges) (below sp k) n := by
  refine ⟨?_,?_⟩
  · change (below sp k).toNat + n ≤ 2^64
    rw [edgeNat bound (by omega)]
    omega
  · intro r hr
    obtain ⟨⟨off,len⟩, mem, rfl⟩ := List.mem_map.mp hr
    have fit' := areas (off,len) mem
    have disjoint := apart (off,len) mem
    change (below sp k).toNat + n ≤ (below sp off).toNat ∨
      (below sp off).toNat + len ≤ (below sp k).toNat
    rw [edgeNat bound (by omega), edgeNat bound (by omega : off ≤ 0x298)]
    rcases disjoint with h|h <;> (first | left; omega | right; omega)

theorem windowsWithin {sp : BitVec 64} {ranges : List (Nat × Nat)}
    (room : 0x298 ≤ sp.toNat) (bound : (bottom sp).toNat + 0x298 ≤ 2^32)
    (areas : ∀ r ∈ ranges, r.1 + r.2 ≤ 0x298) :
    RegionsWithin (windows sp ranges) [scratch sp 0x298] := by
  intro r hr
  obtain ⟨⟨off,len⟩, mem, rfl⟩ := List.mem_map.mp hr
  have fit := areas (off,len) mem
  refine ⟨_,List.mem_cons_self,?_⟩
  change sp.toNat - 0x298 ≤ (below sp off).toNat ∧
    (below sp off).toNat + len ≤ sp.toNat - 0x298 + 0x298
  rw [edgeNat bound (by omega), show (bottom sp).toNat = sp.toNat - 0x298
    from BitVec.toNat_sub_of_le (by exact room)]
  omega

end K256.Proofs.Verify.Core.Lincomb.Double
