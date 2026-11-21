import Sha2.Proofs.Wrapper512.Absorb.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb

open Prelude X86 X86.Machine

theorem hasBytes_of_bytes {before after : Ram} {address : BitVec 64} {bytes : ByteArray}
    (input : (⟨address.toNat, bytes.size⟩ : MemoryRegion).HasBytes before bytes)
    (same : ∀ j < bytes.size, after[address + BitVec.ofNat 64 j]? = before[address + BitVec.ofNat 64 j]?) :
    (⟨address.toNat, bytes.size⟩ : MemoryRegion).HasBytes after bytes := by
  refine ⟨input.1, fun j => ?_⟩
  have old := input.2 j
  change before[BitVec.ofNat 64 (address.toNat + j.val)]? = _ at old
  change after[BitVec.ofNat 64 (address.toNat + j.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at old ⊢
  exact (same j.val j.isLt).trans old

end Sha2.Proofs.Wrapper512.Absorb
