import Hkdf.Spec.Program
import Hkdf.Proofs.Common.Memory.LoadBytes

namespace Hkdf.Proofs.Common

open Hkdf.Spec.Program Prelude X86

def prefixConcatenation (inputs : Array Input) (count : Nat) : ByteArray :=
  concatenation (inputs.extract 0 count)

theorem prefixConcatenation_zero (inputs : Array Input) :
    prefixConcatenation inputs 0 = ByteArray.empty := by
  simp [prefixConcatenation, concatenation]

theorem prefixConcatenation_succ (inputs : Array Input) (i : Nat) (hi : i < inputs.size) :
    prefixConcatenation inputs (i + 1) = prefixConcatenation inputs i ++ inputs[i].bytes := by
  simp only [prefixConcatenation, Array.extract_succ_right (i := 0) (by omega) hi,
    concatenation, Array.foldl_push]

theorem prefixConcatenation_size (inputs : Array Input) :
    prefixConcatenation inputs inputs.size = concatenation inputs := by
  simp [prefixConcatenation]

theorem prefixConcatenation_bound (inputs : Array Input) (bound : Nat)
    (bounded : ∀ i : Fin inputs.size, inputs[i].bytes.size ≤ bound)
    {count : Nat} (within : count ≤ inputs.size) :
    (prefixConcatenation inputs count).size ≤ count * bound := by
  induction count with
  | zero => simp only [prefixConcatenation_zero, ByteArray.size_empty, Nat.zero_mul, Nat.le_refl]
  | succ count ih =>
    rw [prefixConcatenation_succ inputs count (by omega), ByteArray.size_append, Nat.succ_mul]
    have prefixBound := ih (by omega)
    have current : inputs[count].bytes.size ≤ bound := bounded ⟨count, by omega⟩
    omega

theorem concatenation_bound (inputs : Array Input) (bound : Nat)
    (bounded : ∀ i : Fin inputs.size, inputs[i].bytes.size ≤ bound) :
    (concatenation inputs).size ≤ inputs.size * bound := by
  simpa only [prefixConcatenation_size] using
    prefixConcatenation_bound inputs bound bounded (Nat.le_refl inputs.size)

theorem input_count_bound {s : Machine.RamState} {inputs : Array Input}
    (valid : 0 < inputs.size → ValidTable (pointerTable s inputs.size)) :
    inputs.size < 2^29 := by
  by_cases empty : inputs.size = 0
  · omega
  · have h := valid (by omega)
    change (s.regValue .rdi).toNat + 8 * inputs.size < 2^32 at h
    omega

theorem extract_input_bound {routine : Routine} {s : Machine.RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (call : ValidExtractCall routine s salt inputs) (i : Fin inputs.size) :
    inputs[i].bytes.size < 2^32 := by
  have bound := (call.ikmInMemory i).2.2.1
  change inputs[i].address.toNat + inputs[i].bytes.size < 2^32 at bound
  omega

theorem extract_message_bound {routine : Routine} {s : Machine.RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (call : ValidExtractCall routine s salt inputs) :
    64 + (concatenation inputs).size < 2^61 := by
  have count := input_count_bound call.pointerTableValid
  have size := concatenation_bound inputs (2^32 - 1) (fun i ↦ by
    have current := extract_input_bound call i
    omega)
  omega

theorem byte_unchanged_of_separation
    {initial current : Machine.RamState} {n : Nat}
    {writable : Vector MemoryRegion n} {reads : List MemoryRegion}
    (separation : MemorySeparation writable reads)
    (frame : MemoryWriteFrame initial current writable)
    {read : MemoryRegion} (member : read ∈ reads)
    {address : BitVec 64} (within : read.Contains address.toNat) :
    current.external[address]? = initial.external[address]? := by
  apply frame address
  intro region hr
  exact (separation.2 region hr).1 read member address.toNat within

theorem validInput_of_frame
    {initial current : Machine.RamState} {n : Nat}
    {writable : Vector MemoryRegion n} {reads : List MemoryRegion}
    (separation : MemorySeparation writable reads)
    (frame : MemoryWriteFrame initial current writable)
    {read : MemoryRegion} (member : read ∈ reads) {bytes : ByteArray}
    (valid : ValidInput initial.external read bytes) :
    ValidInput current.external read bytes := by
  refine ⟨valid.1, valid.2.1, ?_⟩
  intro i
  rw [byte_unchanged_of_separation separation frame member ?_]
  · exact valid.2.2 i
  · have bound : read.start + read.size < 2^32 := valid.1
    have size : bytes.size = read.size := valid.2.1
    have index := i.isLt
    change read.start ≤ (BitVec.ofNat 64 (read.start + i.val)).toNat ∧
      (BitVec.ofNat 64 (read.start + i.val)).toNat < read.start + read.size
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨by omega, by omega⟩

theorem extract_input_inMemory {routine : Routine} {initial current : Machine.RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (call : ValidExtractCall routine initial salt inputs)
    (frame : MemoryWriteFrame initial current #v[Stack.region initial routine.minStackBytes])
    (i : Fin inputs.size) : ValidInput current.external inputs[i].region inputs[i].bytes := by
  apply validInput_of_frame call.stackSeparation frame ?_ (call.ikmInMemory i).2.2
  simp only [List.mem_cons, List.mem_append]
  left
  right
  right
  apply List.mem_iff_getElem.mpr
  exact ⟨i.val, by simp, by simp⟩

theorem extract_input_byte_unchanged
    {routine : Routine} {initial current : Machine.RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (call : ValidExtractCall routine initial salt inputs)
    (frame : MemoryWriteFrame initial current #v[Stack.region initial routine.minStackBytes])
    (i : Fin inputs.size) (j : Fin inputs[i].bytes.size) :
    current.external[inputs[i].address + BitVec.ofNat 64 j.val]? = some inputs[i].bytes[j.val] := by
  simpa only [Input.region, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    (extract_input_inMemory call frame i).2.2 j

theorem extract_table_word_unchanged
    {routine : Routine} {initial current : Machine.RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (call : ValidExtractCall routine initial salt inputs)
    (frame : MemoryWriteFrame initial current #v[Stack.region initial routine.minStackBytes])
    {table : MemoryRegion}
    (member : table ∈ (pointerTable initial inputs.size :: lengthTable initial inputs.size ::
      (inputs.map Input.region).toList ++ salt.toList.map (extractSaltRegion initial)))
    (bounded : table.Bounded) (size : table.size = 8 * inputs.size)
    (i : Fin inputs.size) {value : BitVec 64}
    (word : (tableEntry table i).Word64At initial.external value) :
    Machine.loadBytes current.external (BitVec.ofNat 64 (table.start + 8 * i.val)) 8 = .ok value := by
  rw [Hkdf.Proofs.Common.Memory.loadBytes_congr (before := initial.external) ?_]
  · exact word.2
  · intro j hj
    apply byte_unchanged_of_separation call.stackSeparation frame member
    have bound : table.start + table.size < 2^32 := bounded
    have index := i.isLt
    change table.start ≤ _ ∧ _ < table.start + table.size
    have address : (BitVec.ofNat 64 (table.start + 8 * i.val) + BitVec.ofNat 64 j).toNat =
        table.start + 8 * i.val + j := by
      rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      rw [size] at bound
      omega
    rw [address, size]
    omega

theorem extract_input_pointer
    {routine : Routine} {initial current : Machine.RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (call : ValidExtractCall routine initial salt inputs)
    (frame : MemoryWriteFrame initial current #v[Stack.region initial routine.minStackBytes])
    (i : Fin inputs.size) :
    X86Proofs.memLoad current.external (initial.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) 64 =
      inputs[i].address := by
  apply Hkdf.Proofs.Common.Memory.memLoad_of_loadBytes64
  have word := extract_table_word_unchanged call frame
    (table := pointerTable initial inputs.size) (by simp)
    (call.pointerTableValid (by have h := i.isLt; omega)) rfl i (call.ikmInMemory i).1
  simpa only [pointerTable, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
    BitVec.setWidth_eq] using word

theorem extract_input_length
    {routine : Routine} {initial current : Machine.RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (call : ValidExtractCall routine initial salt inputs)
    (frame : MemoryWriteFrame initial current #v[Stack.region initial routine.minStackBytes])
    (i : Fin inputs.size) :
    X86Proofs.memLoad current.external (initial.regValue .rdx + BitVec.ofNat 64 (8 * i.val)) 64 =
      BitVec.ofNat 64 inputs[i].bytes.size := by
  apply Hkdf.Proofs.Common.Memory.memLoad_of_loadBytes64
  have word := extract_table_word_unchanged call frame
    (table := lengthTable initial inputs.size) (by simp)
    (call.lengthTableValid (by have h := i.isLt; omega)) rfl i (call.ikmInMemory i).2.1
  simpa only [lengthTable, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
    BitVec.setWidth_eq] using word

theorem extract_input_slice {routine : Routine} {initial current : Machine.RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (call : ValidExtractCall routine initial salt inputs)
    (frame : MemoryWriteFrame initial current #v[Stack.region initial routine.minStackBytes])
    (i : Fin inputs.size) {offset count : Nat} (bound : offset + count ≤ inputs[i].bytes.size) :
    let source := inputs[i].address + BitVec.ofNat 64 offset
    ValidInput current.external (⟨source.toNat, count⟩ : MemoryRegion)
        (inputs[i].bytes.extract offset (offset + count)) ∧
      (⟨source.toNat, count⟩ : MemoryRegion).Disjoint
        (Stack.region initial routine.minStackBytes) := by
  dsimp only
  have valid := extract_input_inMemory call frame i
  have bounded : inputs[i].address.toNat + inputs[i].bytes.size < 2^32 := valid.1
  have address : (inputs[i].address + BitVec.ofNat 64 offset).toNat =
      inputs[i].address.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have subset : ∀ a, (⟨(inputs[i].address + BitVec.ofNat 64 offset).toNat, count⟩ :
      MemoryRegion).Contains a → inputs[i].region.Contains a := by
    intro a ha
    change (inputs[i].address + BitVec.ofNat 64 offset).toNat ≤ a ∧
      a < (inputs[i].address + BitVec.ofNat 64 offset).toNat + count at ha
    rw [address] at ha
    change inputs[i].address.toNat ≤ a ∧ a < inputs[i].address.toNat + inputs[i].bytes.size
    omega
  have size : (inputs[i].bytes.extract offset (offset + count)).size = count := by
    rw [ByteArray.size_extract]
    omega
  refine ⟨⟨?_, size, ?_⟩, ?_⟩
  · change (inputs[i].address + BitVec.ofNat 64 offset).toNat + count < 2^32
    rw [address]
    omega
  · intro j
    have hj : j.val < count := by have := j.isLt; omega
    have byte := extract_input_byte_unchanged call frame i ⟨offset + j.val, by omega⟩
    rw [address]
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_assoc, ByteArray.getElem_extract] using byte
  · intro a ha
    apply (call.stackSeparation.2 (Stack.region initial routine.minStackBytes)
      (by simp)).1 inputs[i].region ?_ a (subset a ha)
    simp only [List.mem_cons, List.mem_append]
    left
    right
    right
    apply List.mem_iff_getElem.mpr
    exact ⟨i.val, by simp, by simp⟩

end Hkdf.Proofs.Common
