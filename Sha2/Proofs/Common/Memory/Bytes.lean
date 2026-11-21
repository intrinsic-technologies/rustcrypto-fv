import Prelude.Memory.Region
import Init.Data.ByteArray.Lemmas

set_option autoImplicit false

namespace Sha2.Proofs.Common.Memory

open Prelude X86 X86.Machine

theorem hasBytes_prefix {memory : Ram} {region : MemoryRegion} {bytes : ByteArray}
    {count : Nat} (input : region.HasBytes memory bytes) (bound : count ≤ region.size) :
    (⟨region.start, count⟩ : MemoryRegion).HasBytes memory (bytes.extract 0 count) := by
  have size : (bytes.extract 0 count).size = count := by
    rw [ByteArray.size_extract, Nat.sub_zero]
    have hsize : bytes.size = region.size := input.1
    omega
  refine ⟨size, ?_⟩
  intro i
  have hi : i.val < bytes.size := by
    have := i.isLt
    have hsize : bytes.size = region.size := input.1
    omega
  simpa only [ByteArray.getElem_extract, Nat.zero_add] using input.2 ⟨i.val, hi⟩

theorem hasBytes_allocated {m : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (input : region.HasBytes m bytes) : region.Allocated m := by
  intro address member
  have size : bytes.size = region.size := input.1
  have index : address.toNat - region.start < bytes.size := by
    have := member.1
    have := member.2
    omega
  refine ⟨bytes[address.toNat - region.start], ?_⟩
  have original := input.2 ⟨address.toNat - region.start, index⟩
  have offset : region.start + (address.toNat - region.start) = address.toNat := by
    have := member.1
    omega
  simpa only [offset, BitVec.ofNat_toNat, BitVec.setWidth_eq] using original

end Sha2.Proofs.Common.Memory
