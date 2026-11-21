import Sha2.Proofs.Common.SHA256.Absorb.Table
import Sha2.Proofs.Common.Memory.Readable

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Table

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem execution_of_frame [Bindings] {initial s t : RamState}
    {n k fuel : Nat} {regions : Vector MemoryRegion n} {localRegions : Vector MemoryRegion k}
    {components : List Component}
    (state : ExecutionState initial s regions)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t) (df : .df ∉ components)
    (frame : MemoryWriteFrame s t localRegions)
    (avoids : ∀ region ∈ localRegions, region.Avoids InProgram)
    (within : ∀ region ∈ localRegions, ∀ a, region.Contains a →
      ∃ outer ∈ regions, outer.Contains a) : ExecutionState initial t regions := by
  obtain ⟨prior, execution⟩ := state.execution
  refine ⟨⟨prior + fuel, execution.trans run⟩,
    supportedMachine_of_ready_agrees state.machine ready agrees, ?_,
    fun a ha => agrees.grow a (state.allocated a ha),
    agrees.directionFlagClear df state.directionFlag, ?_⟩
  · intro address byte fetch
    rw [frame address]
    · exact state.loaded address byte fetch
    · intro region member contains
      exact avoids region member address contains ⟨byte, fetch⟩
  · apply memoryWriteFrame_trans state.frame
    intro address outside
    apply frame address
    intro region member contains
    obtain ⟨outer, ho, ha⟩ := within region member address.toNat contains
    exact outside outer ho ha

theorem readable_contains {s : RamState} {a : BitVec 64} {len i : Nat}
    (readable : MemReadable s a len) (bound : i < len) :
    (⟨a.toNat, len⟩ : MemoryRegion).Contains (a + BitVec.ofNat 64 i).toNat := by
  have low := readable.low
  have small : i < 2^64 := by omega
  have sum : a.toNat + i < 2^64 := by omega
  change a.toNat ≤ (a + BitVec.ofNat 64 i).toNat ∧
    (a + BitVec.ofNat 64 i).toNat < a.toNat + len
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt sum]
  omega

theorem frame_byte {s t : RamState} {n len i : Nat}
    {regions : Vector MemoryRegion n} {a : BitVec 64}
    (frame : MemoryWriteFrame s t regions) (readable : MemReadable s a len)
    (apart : ∀ region ∈ regions, (⟨a.toNat, len⟩ : MemoryRegion).Disjoint region)
    (bound : i < len) :
    t.external[a + BitVec.ofNat 64 i]? = s.external[a + BitVec.ofNat 64 i]? := by
  apply frame
  intro region member contains
  exact apart region member _ (readable_contains readable bound) contains

theorem readable_of_frame {s t : RamState} {n len : Nat}
    {regions : Vector MemoryRegion n} {a : BitVec 64}
    (frame : MemoryWriteFrame s t regions) (readable : MemReadable s a len)
    (apart : ∀ region ∈ regions, (⟨a.toNat, len⟩ : MemoryRegion).Disjoint region) :
    MemReadable t a len := by
  refine ⟨readable.low, fun i hi => ?_⟩
  rw [frame_byte frame readable apart hi]
  exact readable.mem i hi

theorem memLoad_of_frame {s t : RamState} {n width : Nat}
    {regions : Vector MemoryRegion n} {a : BitVec 64}
    (frame : MemoryWriteFrame s t regions) (readable : MemReadable s a (width / 8))
    (apart : ∀ region ∈ regions, (⟨a.toNat, width / 8⟩ : MemoryRegion).Disjoint region) :
    memLoad t.external a width = memLoad s.external a width := by
  apply memLoad_congr
  intro i hi
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [frame_byte frame readable apart hi]

theorem prefixMessage_size_le (inputs : Array Input) {i j : Nat}
    (ordered : i ≤ j) (bound : j ≤ inputs.size) :
    (Wrapper.prefixMessage inputs i).size ≤ (Wrapper.prefixMessage inputs j).size := by
  induction j with
  | zero =>
    have eq : i = 0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases last : i = j + 1
    · rw [last]
      exact Nat.le_refl _
    · have before := ih (by omega) (by omega)
      rw [Wrapper.prefixMessage_succ inputs j (by omega), ByteArray.size_append]
      omega

end Sha2.Proofs.Common.SHA256.Absorb.Table
