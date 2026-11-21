import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.State
import Sha2.Proofs.Common.Memory.Bytes

set_option autoImplicit false

namespace Sha2.Proofs.Common.Memory

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem hasBytes_of_frame {s t : RamState} {n : Nat} {regions : Vector MemoryRegion n}
    {region : MemoryRegion} {bytes : ByteArray} (input : region.HasBytes s.external bytes)
    (bounded : region.Bounded) (frame : MemoryWriteFrame s t regions)
    (apart : ∀ written ∈ regions, region.Disjoint written) :
    region.HasBytes t.external bytes := by
  refine ⟨input.1, ?_⟩
  intro i
  have size : bytes.size = region.size := input.1
  have hi := i.isLt
  have bound : region.start + region.size < 2^32 := bounded
  rw [frame]
  · exact input.2 i
  · intro written member contains
    apply apart written member _ ?_ contains
    change region.start ≤ (BitVec.ofNat 64 (region.start + i.val)).toNat ∧
      (BitVec.ofNat 64 (region.start + i.val)).toNat < region.start + region.size
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    constructor <;> omega

theorem hasBytes_extract {m : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (input : region.HasBytes m bytes) {offset count : Nat}
    (bound : offset + count ≤ region.size) :
    (⟨region.start + offset, count⟩ : MemoryRegion).HasBytes m
      (bytes.extract offset (offset + count)) := by
  have size : bytes.size = region.size := input.1
  have slice : (bytes.extract offset (offset + count)).size = count := by
    rw [ByteArray.size_extract]
    omega
  refine ⟨slice, ?_⟩
  intro i
  have hi := i.isLt
  have original := input.2 ⟨offset + i.val, by omega⟩
  simpa only [Nat.add_assoc, ByteArray.getElem_extract] using original


end Sha2.Proofs.Common.Memory
