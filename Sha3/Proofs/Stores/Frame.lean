import Sha3.Proofs.Permutation.LoadStore.Memory
import Sha3.Proofs.Outcome

namespace X86Proofs

open X86 X86.Machine Prelude Sha3.Spec.Program

theorem StorePreReadable.of_region {s : RamState} {p : BitVec 64}
    {address : RamState → BitVec 64} {count : Nat} {region : MemoryRegion}
    (hrip : s.RIP = p) (hbounded : region.Bounded)
    (hallocated : region.Allocated s.external)
    (hstart : region.start ≤ (address s).toNat)
    (hend : (address s).toNat + count ≤ region.start + region.size)
    (havoid : region.Avoids InPageTables) : StorePreReadable p address count s := by
  have hread := Sha3.Proofs.memReadable_of_region hbounded hallocated hstart hend
  refine ⟨⟨hrip, hread⟩, ?_⟩
  intro i hi
  apply havoid
  have hlow := hread.low
  have hi64 : i < 2 ^ 64 := by omega
  have hsum64 : (address s).toNat + i < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64,
    Nat.mod_eq_of_lt hsum64]
  exact ⟨by omega, by omega⟩

theorem Effect.avoids_program_of_writesWithin {e : Effect} {regions : Vector MemoryRegion n}
    (hw : WritesWithin e.components regions)
    (ha : ∀ region ∈ regions, region.Avoids InProgram) :
    e.Avoids Sha3.Spec.Program.Extracted.programImage := by
  intro x hx c hc hcover
  obtain ⟨region, hregion, hcontains⟩ := hw c hc x.1 hcover
  exact ha region hregion x.1 hcontains ⟨x.2, hx⟩

theorem AgreesExcept.allocated {region : MemoryRegion}
    {s t : RamState} {cs : List Component} (h : AgreesExcept cs s t)
    (ha : region.Allocated s.external) : region.Allocated t.external := by
  intro address hcontains
  apply Option.isSome_iff_exists.mp
  exact h.grow address (Option.isSome_iff_exists.mpr (ha address hcontains))

theorem MemReadable.of_agreesExcept {s t : RamState} {cs : List Component}
    {address : BitVec 64} {count : Nat} (h : AgreesExcept cs s t)
    (hr : MemReadable s address count) : MemReadable t address count :=
  ⟨hr.low, fun i hi => h.grow _ (hr.mem i hi)⟩

end X86Proofs
