import Base16ct.Proofs.Copied.Md5.Proofs.Block.Entry
import X86Proofs.Program.ReadWrite.Registers

namespace Base16ct.Proofs.Copied.Md5.Proofs.Block

open Base16ct.Proofs.Copied.Md5.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem contains_of_mem_covers {region : MemoryRegion} (hBounded : region.Bounded)
    {address : BitVec 64}
    (hCovers : Component.Covers (.mem (BitVec.ofNat 64 region.start) region.size) address) :
    region.Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hCovers
  have hStart : region.start < 2^64 := by
    unfold MemoryRegion.Bounded userAddressLimit at hBounded
    omega
  have hIndex : i < 2^64 := by
    unfold MemoryRegion.Bounded userAddressLimit at hBounded
    omega
  have hSum : region.start + i < 2^64 := by
    unfold MemoryRegion.Bounded userAddressLimit at hBounded
    omega
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hStart, Nat.mod_eq_of_lt hIndex, Nat.mod_eq_of_lt hSum]
  omega

end Base16ct.Proofs.Copied.Md5.Proofs.Block
