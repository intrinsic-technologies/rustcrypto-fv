import Sha3.Proofs.Memory
import X86Proofs.Program.ReadWrite.Bytes

namespace Sha3.Proofs

open X86 X86.Machine X86Proofs Prelude Sha3.Spec.Program

theorem tableEntry_contains {table : MemoryRegion} {count i address : Nat}
    (hsize : table.size = 8 * count) (hi : i < count)
    (h : (tableEntry table i).Contains address) : table.Contains address := by
  simp only [tableEntry, MemoryRegion.Contains] at h ⊢
  constructor <;> omega

theorem tableEntry_bounded {table : MemoryRegion} {count i : Nat}
    (h : table.Bounded) (hsize : table.size = 8 * count) (hi : i < count) :
    (tableEntry table i).Bounded := by
  simp only [tableEntry, MemoryRegion.Bounded] at h ⊢
  omega

private theorem loadBytes_loop_congr {memory memory' : Ram} {address : BitVec 64}
    (remaining current shift accumulator : Nat)
    (h : ∀ i < remaining,
      memory[addAddress address (current + i)]? =
        memory'[addAddress address (current + i)]?) :
    loadBytes.loop memory address remaining current shift accumulator =
      loadBytes.loop memory' address remaining current shift accumulator := by
  induction remaining generalizing current shift accumulator with
  | zero => rfl
  | succ remaining ih =>
    have hzero := h 0 (by omega)
    simp only [Nat.add_zero] at hzero
    simp only [loadBytes.loop, hzero]
    cases hb : memory'[addAddress address current]? with
    | none => rfl
    | some byte =>
      apply ih
      intro i hi
      have hnext := h (i + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext

theorem loadBytes_congr {memory memory' : Ram} {address : BitVec 64} {count : Nat}
    (h : ∀ i < count, memory[address + BitVec.ofNat 64 i]? =
      memory'[address + BitVec.ofNat 64 i]?) :
    loadBytes memory address count = loadBytes memory' address count := by
  apply loadBytes_loop_congr count 0 0 0
  simpa only [Nat.zero_add, addAddress, fromNat] using h

private theorem loadBytes_loop_isSome {memory : Ram} {address : BitVec 64}
    (remaining current shift accumulator : Nat) {value : BitVec 64}
    (h : loadBytes.loop memory address remaining current shift accumulator = .ok value) :
    ∀ i < remaining, (memory[addAddress address (current + i)]?).isSome := by
  induction remaining generalizing current shift accumulator with
  | zero => intro i hi; omega
  | succ remaining ih =>
    cases hb : memory[addAddress address current]? with
    | none => simp only [loadBytes.loop, hb] at h; cases h
    | some byte =>
      simp only [loadBytes.loop, hb] at h
      intro i hi
      cases i with
      | zero => simp only [Nat.add_zero, hb, Option.isSome_some]
      | succ i =>
        have hnext := ih (current + 1) (shift + 8)
          (accumulator + byte.toNat * 2 ^ shift) h i (by omega)
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hnext

theorem loadBytes_isSome {memory : Ram} {address : BitVec 64} {count : Nat}
    {value : BitVec 64} (h : loadBytes memory address count = .ok value) :
    ∀ i < count, (memory[address + BitVec.ofNat 64 i]?).isSome := by
  simpa only [Nat.zero_add, addAddress, fromNat] using loadBytes_loop_isSome count 0 0 0 h

theorem memReadable_of_loadBytes {s : RamState} {address : BitVec 64} {count : Nat}
    {value : BitVec 64} (h : loadBytes s.external address count = .ok value)
    (hlow : address.toNat + count ≤ 2 ^ 32) : MemReadable s address count :=
  ⟨hlow, loadBytes_isSome h⟩

theorem memLoad64_of_loadBytes {memory : Ram} {address value : BitVec 64}
    (h : loadBytes memory address 8 = .ok value) : memLoad memory address 64 = value := by
  have hbytes := Bytes.of_memLoad (n := 64) (loadBytes_isSome h)
  exact Except.ok.inj (hbytes.loadBytes64.symm.trans h)

theorem word64At_of_memoryWriteFrame {initial final : RamState}
    {writable : Vector MemoryRegion n} {region : MemoryRegion} {value : BitVec 64}
    (hframe : MemoryWriteFrame initial final writable)
    (hword : region.Word64At initial.external value)
    (hrange : region.start + region.size ≤ 2 ^ 64)
    (hdisjoint : ∀ target ∈ writable, region.Disjoint target) :
    region.Word64At final.external value := by
  refine ⟨hword.1, ?_⟩
  have he : loadBytes final.external (BitVec.ofNat 64 region.start) 8 =
      loadBytes initial.external (BitVec.ofNat 64 region.start) 8 := by
    apply loadBytes_congr
    intro i hi
    apply hframe
    intro target ht
    apply hdisjoint target ht
    have hsize : 8 = region.size := hword.1
    rw [← BitVec.ofNat_add, MemoryRegion.Contains, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    exact ⟨by omega, by omega⟩
  exact he.trans hword.2

theorem tableEntry_word64At_of_memoryWriteFrame {initial final : RamState}
    {writable : Vector MemoryRegion n} {table : MemoryRegion} {count i : Nat}
    {value : BitVec 64} (htable : table.Bounded) (hsize : table.size = 8 * count)
    (hi : i < count) (hword : (tableEntry table i).Word64At initial.external value)
    (hframe : MemoryWriteFrame initial final writable)
    (hdisjoint : ∀ target ∈ writable, table.Disjoint target) :
    (tableEntry table i).Word64At final.external value := by
  apply word64At_of_memoryWriteFrame hframe hword
  · have hbound := tableEntry_bounded htable hsize hi
    change (tableEntry table i).start + (tableEntry table i).size < 2 ^ 32 at hbound
    omega
  · intro target ht address ha
    exact hdisjoint target ht address (tableEntry_contains hsize hi ha)

theorem pointerTable_word64At_of_memoryWriteFrame {initial final : RamState}
    {inputs : Array Input} {i : Fin inputs.size} {writable : Vector MemoryRegion n}
    (htable : ValidTable (pointerTable initial inputs.size))
    (hinput : ValidInputSlice initial inputs i) (hsep : MemorySeparation (readRegions initial inputs) writable)
    (hframe : MemoryWriteFrame initial final writable) :
    (tableEntry (pointerTable initial inputs.size) i).Word64At final.external
      inputs[i].address := by
  apply tableEntry_word64At_of_memoryWriteFrame htable.2 rfl i.isLt hinput.2.1 hframe
  intro target ht
  exact (hsep.2 target ht).1 _ (List.mem_cons_self)

theorem lengthTable_word64At_of_memoryWriteFrame {initial final : RamState}
    {inputs : Array Input} {i : Fin inputs.size} {writable : Vector MemoryRegion n}
    (htable : ValidTable (lengthTable initial inputs.size))
    (hinput : ValidInputSlice initial inputs i) (hsep : MemorySeparation (readRegions initial inputs) writable)
    (hframe : MemoryWriteFrame initial final writable) :
    (tableEntry (lengthTable initial inputs.size) i).Word64At final.external
      (BitVec.ofNat 64 inputs[i].bytes.size) := by
  apply tableEntry_word64At_of_memoryWriteFrame htable.2 rfl i.isLt hinput.2.2.1 hframe
  intro target ht
  exact (hsep.2 target ht).1 _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem memReadable_of_word64At {s : RamState} {region : MemoryRegion} {value : BitVec 64}
    (hword : region.Word64At s.external value) (hbounded : region.Bounded) :
    MemReadable s (BitVec.ofNat 64 region.start) 8 := by
  apply memReadable_of_loadBytes hword.2
  have hsize : 8 = region.size := hword.1
  change region.start + region.size < 2 ^ 32 at hbounded
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem memLoad64_of_word64At {memory : Ram} {region : MemoryRegion} {value : BitVec 64}
    (hword : region.Word64At memory value) :
    memLoad memory (BitVec.ofNat 64 region.start) 64 = value :=
  memLoad64_of_loadBytes hword.2

theorem pointerTable_load_of_memoryWriteFrame {initial final : RamState}
    {inputs : Array Input} {i : Fin inputs.size} {writable : Vector MemoryRegion n}
    (hslices : ValidInputSlices initial inputs)
    (hsep : MemorySeparation (readRegions initial inputs) writable)
    (hframe : MemoryWriteFrame initial final writable) :
    MemReadable final (initial.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) 8 ∧
      memLoad final.external (initial.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) 64 =
        inputs[i].address := by
  have hword := pointerTable_word64At_of_memoryWriteFrame hslices.pointerTableValid
    (hslices.inputsInMemory i) hsep hframe
  have hbound := tableEntry_bounded hslices.pointerTableValid.2 rfl i.isLt
  simpa only [tableEntry, pointerTable, registerRegion, BitVec.ofNat_add,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    And.intro (memReadable_of_word64At hword hbound) (memLoad64_of_word64At hword)

theorem lengthTable_load_of_memoryWriteFrame {initial final : RamState}
    {inputs : Array Input} {i : Fin inputs.size} {writable : Vector MemoryRegion n}
    (hslices : ValidInputSlices initial inputs)
    (hsep : MemorySeparation (readRegions initial inputs) writable)
    (hframe : MemoryWriteFrame initial final writable) :
    MemReadable final (initial.regValue .rdx + BitVec.ofNat 64 (8 * i.val)) 8 ∧
      memLoad final.external (initial.regValue .rdx + BitVec.ofNat 64 (8 * i.val)) 64 =
        BitVec.ofNat 64 inputs[i].bytes.size := by
  have hword := lengthTable_word64At_of_memoryWriteFrame hslices.lengthTableValid
    (hslices.inputsInMemory i) hsep hframe
  have hbound := tableEntry_bounded hslices.lengthTableValid.2 rfl i.isLt
  simpa only [tableEntry, lengthTable, registerRegion, BitVec.ofNat_add,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    And.intro (memReadable_of_word64At hword hbound) (memLoad64_of_word64At hword)

end Sha3.Proofs
