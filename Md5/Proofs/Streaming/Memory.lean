import Md5.Proofs.Machine
import Md5.Proofs.Streaming.Slices

namespace Md5.Proofs.Streaming

open Md5.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem region_contains_offset {region : MemoryRegion} {address : BitVec 64}
    {len i : Nat} (hb : region.Bounded) (hs : region.start ≤ address.toNat)
    (he : address.toNat + len ≤ region.start + region.size) (hi : i < len) :
    region.Contains (address + BitVec.ofNat 64 i).toNat := by
  change region.start + region.size < 2^32 at hb
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2^64 by omega),
    Nat.mod_eq_of_lt (show address.toNat + i < 2^64 by omega)]
  exact ⟨by omega, by omega⟩

theorem memoryRead_of_memoryWriteFrame {s t : RamState} {regions : Vector MemoryRegion n}
    {region : MemoryRegion} {address : BitVec 64} {bits : Nat}
    (h : MemoryWriteFrame s t regions) (hb : region.Bounded)
    (hs : region.start ≤ address.toNat)
    (he : address.toNat + bits / 8 ≤ region.start + region.size)
    (hsep : ∀ r ∈ regions, region.Disjoint r) :
    (Operand.mem address : Operand bits).read t =
      (Operand.mem address : Operand bits).read s := by
  apply memLoad_congr
  intro i hi
  have hbyte := h (address + BitVec.ofNat 64 i) (fun r hr ↦
    hsep r hr _ (region_contains_offset hb hs he hi))
  exact congrArg (fun byte : Option UInt8 ↦ byte.getD 0) hbyte

theorem memoryReadable_of_memoryWriteFrame {s t : RamState} {regions : Vector MemoryRegion n}
    {region : MemoryRegion} {address : BitVec 64} {len : Nat}
    (h : MemoryWriteFrame s t regions) (hb : region.Bounded)
    (hs : region.start ≤ address.toNat)
    (he : address.toNat + len ≤ region.start + region.size)
    (hsep : ∀ r ∈ regions, region.Disjoint r)
    (hread : MemReadable s address len) : MemReadable t address len := by
  refine ⟨hread.1, ?_⟩
  intro i hi
  rw [h _ (fun r hr ↦ hsep r hr _ (region_contains_offset hb hs he hi))]
  exact hread.2 i hi

theorem tableEntry_address_toNat {table : MemoryRegion} {i : Nat}
    (hb : table.Bounded) (hi : 8 * (i + 1) ≤ table.size) :
    (BitVec.ofNat 64 (table.start + 8 * i)).toNat = table.start + 8 * i := by
  change table.start + table.size < 2^32 at hb
  exact Nat.mod_eq_of_lt (by omega)

theorem validInputs_pointer_preserved {initial s : RamState}
    {inputs : Array Slices.Input} {regions : Vector MemoryRegion n}
    (h : Slices.ValidInputs initial inputs) (hf : MemoryWriteFrame initial s regions)
    (hsep : ∀ r ∈ regions, (Slices.pointerTable initial inputs.size).Disjoint r)
    (i : Fin inputs.size) :
    (Operand.mem (initial.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) : Operand 64).read s =
      inputs[i].address ∧
    MemReadable s (initial.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) 8 := by
  have hi : 8 * (i.val + 1) ≤ (Slices.pointerTable initial inputs.size).size := by
    change 8 * (i.val + 1) ≤ 8 * inputs.size
    omega
  have hnat := tableEntry_address_toNat h.pointerTableValid.2 hi
  simp only [Slices.pointerTable, registerRegion, BitVec.ofNat_add,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] at hnat
  have hs : (Slices.pointerTable initial inputs.size).start ≤
      (initial.regValue .rdi + BitVec.ofNat 64 (8 * i.val)).toNat := by
    rw [hnat]
    exact Nat.le_add_right ..
  have he : (initial.regValue .rdi + BitVec.ofNat 64 (8 * i.val)).toNat + 8 ≤
      (Slices.pointerTable initial inputs.size).start +
        (Slices.pointerTable initial inputs.size).size := by
    rw [hnat]
    change (initial.regValue .rdi).toNat + 8 * i.val + 8 ≤
      (initial.regValue .rdi).toNat + 8 * inputs.size
    omega
  exact ⟨(memoryRead_of_memoryWriteFrame hf h.pointerTableValid.2 hs he hsep).trans
      (validInputs_pointer_read h i),
    memoryReadable_of_memoryWriteFrame hf h.pointerTableValid.2 hs he hsep
      (validInputs_pointer_readable h i)⟩

theorem validInputs_length_preserved {initial s : RamState}
    {inputs : Array Slices.Input} {regions : Vector MemoryRegion n}
    (h : Slices.ValidInputs initial inputs) (hf : MemoryWriteFrame initial s regions)
    (hsep : ∀ r ∈ regions, (Slices.lengthTable initial inputs.size).Disjoint r)
    (i : Fin inputs.size) :
    (Operand.mem (initial.regValue .rdx + BitVec.ofNat 64 (8 * i.val)) : Operand 64).read s =
      BitVec.ofNat 64 inputs[i].bytes.size ∧
    MemReadable s (initial.regValue .rdx + BitVec.ofNat 64 (8 * i.val)) 8 := by
  have hi : 8 * (i.val + 1) ≤ (Slices.lengthTable initial inputs.size).size := by
    change 8 * (i.val + 1) ≤ 8 * inputs.size
    omega
  have hnat := tableEntry_address_toNat h.lengthTableValid.2 hi
  simp only [Slices.lengthTable, registerRegion, BitVec.ofNat_add,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] at hnat
  have hs : (Slices.lengthTable initial inputs.size).start ≤
      (initial.regValue .rdx + BitVec.ofNat 64 (8 * i.val)).toNat := by
    rw [hnat]
    exact Nat.le_add_right ..
  have he : (initial.regValue .rdx + BitVec.ofNat 64 (8 * i.val)).toNat + 8 ≤
      (Slices.lengthTable initial inputs.size).start +
        (Slices.lengthTable initial inputs.size).size := by
    rw [hnat]
    change (initial.regValue .rdx).toNat + 8 * i.val + 8 ≤
      (initial.regValue .rdx).toNat + 8 * inputs.size
    omega
  exact ⟨(memoryRead_of_memoryWriteFrame hf h.lengthTableValid.2 hs he hsep).trans
      (validInputs_length_read h i),
    memoryReadable_of_memoryWriteFrame hf h.lengthTableValid.2 hs he hsep
      (validInputs_length_readable h i)⟩

theorem validInputs_bytes_preserved {initial s : RamState}
    {inputs : Array Slices.Input} {regions : Vector MemoryRegion n}
    (h : Slices.ValidInputs initial inputs) (hf : MemoryWriteFrame initial s regions)
    (hsep : ∀ r ∈ regions, ∀ read ∈ Slices.readRegions initial inputs, read.Disjoint r)
    (i : Fin inputs.size) : inputs[i].region.HasBytes s.external inputs[i].bytes := by
  apply hasBytes_of_memoryWriteFrame hf (h.slicesValid i).2.2.2.2
    (h.slicesValid i).2.2.2.1
  intro r hr
  apply hsep r hr
  simp only [Slices.readRegions, List.mem_cons, Array.mem_toList_iff, Array.mem_map]
  exact .inr (.inr ⟨inputs[i], Array.getElem_mem i.isLt, rfl⟩)

end Md5.Proofs.Streaming
