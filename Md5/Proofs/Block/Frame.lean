import Md5.Proofs.Block.Entry
import X86Proofs.Program.ReadWrite.Registers

namespace Md5.Proofs.Block

open Md5.Spec.Program Prelude X86 X86.Machine X86Proofs

def compressionComponents (initial : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
   .flags, .rip, .mem (initial.regValue .rdi) 16,
   .mem (BitVec.ofNat 64 (Stack.region initial Compress.minStackBytes).start)
     (Stack.region initial Compress.minStackBytes).size]

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

theorem compression_memoryWriteFrame {s t : RamState}
    (h : AgreesExcept (compressionComponents s) s t)
    (hBuffer : (Compress.outputRegion s).Bounded)
    (hStack : (Stack.region s Compress.minStackBytes).Bounded) :
    MemoryWriteFrame s t #v[Compress.outputRegion s, Stack.region s Compress.minStackBytes] := by
  apply h.memoryWriteFrame
  intro c hc address hCovers
  simp only [compressionComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> try exact False.elim hCovers
  · refine ⟨Compress.outputRegion s, by simp, ?_⟩
    apply contains_of_mem_covers hBuffer
    simpa only [Compress.outputRegion, registerRegion, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using hCovers
  · exact ⟨Stack.region s Compress.minStackBytes, by simp, contains_of_mem_covers hStack hCovers⟩

theorem compression_calleeSaved {s t : RamState}
    (h : AgreesExcept (compressionComponents s) s t) : CalleeSavedRegistersUnchanged s t := by
  intro register hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.read (n := 64) (r := 3) (by simp [compressionComponents])
  · exact h.read (n := 64) (r := 5) (by simp [compressionComponents])
  · exact h.read (n := 64) (r := 12) (by simp [compressionComponents])
  · exact h.read (n := 64) (r := 13) (by simp [compressionComponents])
  · exact h.read (n := 64) (r := 14) (by simp [compressionComponents])
  · exact h.read (n := 64) (r := 15) (by simp [compressionComponents])

end Md5.Proofs.Block
