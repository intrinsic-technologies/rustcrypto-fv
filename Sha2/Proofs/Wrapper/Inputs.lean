import Sha2.Spec.Program
import Sha2.Proofs.Common.Memory.LoadBytes
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Program.ReadWrite.WriteFrame

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prefixMessage (inputs : Array Input) (count : Nat) : ByteArray :=
  message (inputs.extract 0 count)

theorem prefixMessage_zero (inputs : Array Input) :
    prefixMessage inputs 0 = ByteArray.empty := by
  simp [prefixMessage, message]

theorem prefixMessage_succ (inputs : Array Input) (i : Nat) (hi : i < inputs.size) :
    prefixMessage inputs (i + 1) = prefixMessage inputs i ++ inputs[i].bytes := by
  simp only [prefixMessage, Array.extract_succ_right (i := 0) (by omega) hi, message,
    Array.foldl_push]

theorem prefixMessage_size (inputs : Array Input) :
    prefixMessage inputs inputs.size = message inputs := by
  simp [prefixMessage]

theorem validCall_input_bounded {routine : Routine} {initial : RamState}
    {inputs : Array Input} (call : ValidCall routine initial inputs) (i : Fin inputs.size) :
    inputs[i].address.toNat + inputs[i].bytes.size < 2^32 :=
  (call.inputsInMemory i).2.2.2.1

theorem validCall_count_bound {routine : Routine} {initial : RamState}
    {inputs : Array Input} (call : ValidCall routine initial inputs) : inputs.size < 2^29 := by
  have h := call.pointerTableValid.2
  change (initial.regValue .rdi).toNat + 8 * inputs.size < 2^32 at h
  omega

theorem tableEntry_contains {table : MemoryRegion} {count i address : Nat}
    (size : table.size = 8 * count) (hi : i < count)
    (ha : (tableEntry table i).Contains address) : table.Contains address := by
  rcases ha with ⟨low, high⟩
  change table.start + 8 * i ≤ address at low
  change address < table.start + 8 * i + 8 at high
  change table.start ≤ address ∧ address < table.start + table.size
  rw [size]
  omega

theorem validCall_read_unchanged {routine : Routine} {initial current : RamState}
    {inputs : Array Input} (call : ValidCall routine initial inputs)
    (frame : MemoryWriteFrame initial current
      #v[outputRegion routine initial, Stack.region initial routine.minStackBytes])
    {region : MemoryRegion} (hr : region ∈ readRegions initial inputs)
    {address : BitVec 64} (ha : region.Contains address.toNat) :
    current.external[address]? = initial.external[address]? := by
  apply frame address
  intro writable hw
  exact (call.separation.2 writable (by simpa using hw)).1 region hr address.toNat ha

theorem validCall_input_byte_unchanged_of_read_unchanged {routine : Routine} {initial current : RamState}
    {inputs : Array Input} (call : ValidCall routine initial inputs)
    (unchanged : ∀ region ∈ readRegions initial inputs, ∀ address : BitVec 64,
      region.Contains address.toNat → current.external[address]? = initial.external[address]?)
    (i : Fin inputs.size) (j : Fin inputs[i].bytes.size) :
    current.external[inputs[i].address + BitVec.ofNat 64 j.val]? =
      some inputs[i].bytes[j.val] := by
  have bound := validCall_input_bounded call i
  have address : (inputs[i].address + BitVec.ofNat 64 j.val).toNat =
      inputs[i].address.toNat + j.val := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [unchanged inputs[i].region ?_ (inputs[i].address + BitVec.ofNat 64 j.val) ?_]
  · have bytes := (call.inputsInMemory i).2.2.2.2.2 j
    simpa only [Input.region, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using bytes
  · simp only [readRegions, List.mem_cons]
    right
    right
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val, by simp, ?_⟩
    simp
  · change inputs[i].address.toNat ≤ _ ∧ _ < inputs[i].address.toNat + inputs[i].bytes.size
    rw [address]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left j.isLt _⟩


theorem validCall_input_byte_unchanged {routine : Routine} {initial current : RamState}
    {inputs : Array Input} (call : ValidCall routine initial inputs)
    (frame : MemoryWriteFrame initial current
      #v[outputRegion routine initial, Stack.region initial routine.minStackBytes])
    (i : Fin inputs.size) (j : Fin inputs[i].bytes.size) :
    current.external[inputs[i].address + BitVec.ofNat 64 j.val]? =
      some inputs[i].bytes[j.val] := by
  exact validCall_input_byte_unchanged_of_read_unchanged call
    (fun region hr address ha => validCall_read_unchanged call frame hr ha) i j

theorem validCall_input_readable_of_read_unchanged {routine : Routine} {initial current : RamState}
    {inputs : Array Input} (call : ValidCall routine initial inputs)
    (unchanged : ∀ region ∈ readRegions initial inputs, ∀ address : BitVec 64,
      region.Contains address.toNat → current.external[address]? = initial.external[address]?)
    (i : Fin inputs.size) : MemReadable current inputs[i].address inputs[i].bytes.size := by
  refine ⟨Nat.le_of_lt (validCall_input_bounded call i), ?_⟩
  intro j hj
  rw [validCall_input_byte_unchanged_of_read_unchanged call unchanged i ⟨j, hj⟩]
  rfl


theorem validCall_input_readable {routine : Routine} {initial current : RamState}
    {inputs : Array Input} (call : ValidCall routine initial inputs)
    (frame : MemoryWriteFrame initial current
      #v[outputRegion routine initial, Stack.region initial routine.minStackBytes])
    (i : Fin inputs.size) : MemReadable current inputs[i].address inputs[i].bytes.size := by
  exact validCall_input_readable_of_read_unchanged call
    (fun region hr address ha => validCall_read_unchanged call frame hr ha) i

theorem table_word_of_read_unchanged {initial current : RamState}
    {inputs : Array Input}
    (unchanged : ∀ region ∈ readRegions initial inputs, ∀ address : BitVec 64,
      region.Contains address.toNat → current.external[address]? = initial.external[address]?)
    {table : MemoryRegion} (read : table ∈ readRegions initial inputs)
    (bounded : table.Bounded) (size : table.size = 8 * inputs.size)
    (i : Fin inputs.size) {value : BitVec 64}
    (word : (tableEntry table i).Word64At initial.external value) :
    loadBytes current.external (BitVec.ofNat 64 (table.start + 8 * i.val)) 8 = .ok value := by
  rw [Common.Memory.loadBytes_congr (before := initial.external) ?_]
  · exact word.2
  · intro j hj
    apply unchanged table read _
    have bound : table.start + table.size < 2^32 := bounded
    change table.start ≤ _ ∧ _ < table.start + table.size
    have hnat : (BitVec.ofNat 64 (table.start + 8 * i.val) + BitVec.ofNat 64 j).toNat =
        table.start + 8 * i.val + j := by
      rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      rw [size] at bound
      omega
    rw [hnat, size]
    omega


theorem validCall_table_word_unchanged {routine : Routine} {initial current : RamState}
    {inputs : Array Input} (call : ValidCall routine initial inputs)
    (frame : MemoryWriteFrame initial current
      #v[outputRegion routine initial, Stack.region initial routine.minStackBytes])
    {table : MemoryRegion} (read : table ∈ readRegions initial inputs)
    (bounded : table.Bounded) (size : table.size = 8 * inputs.size)
    (i : Fin inputs.size) {value : BitVec 64}
    (word : (tableEntry table i).Word64At initial.external value) :
    loadBytes current.external (BitVec.ofNat 64 (table.start + 8 * i.val)) 8 = .ok value := by
  exact table_word_of_read_unchanged
    (fun region hr address ha => validCall_read_unchanged call frame hr ha) read bounded size i word

theorem validCall_input_pointer_of_read_unchanged {routine : Routine} {initial current : RamState}
    {inputs : Array Input} (call : ValidCall routine initial inputs)
    (unchanged : ∀ region ∈ readRegions initial inputs, ∀ address : BitVec 64,
      region.Contains address.toNat → current.external[address]? = initial.external[address]?)
    (i : Fin inputs.size) :
    memLoad current.external (initial.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) 64 =
      inputs[i].address := by
  apply Common.Memory.memLoad_of_loadBytes64
  have word := table_word_of_read_unchanged unchanged
    (table := pointerTable initial inputs.size) (by simp [readRegions])
    call.pointerTableValid.2 rfl i (call.inputsInMemory i).2.1
  simpa only [pointerTable, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
    BitVec.setWidth_eq] using word


theorem validCall_input_pointer {routine : Routine} {initial current : RamState}
    {inputs : Array Input} (call : ValidCall routine initial inputs)
    (frame : MemoryWriteFrame initial current
      #v[outputRegion routine initial, Stack.region initial routine.minStackBytes])
    (i : Fin inputs.size) :
    memLoad current.external (initial.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) 64 =
      inputs[i].address := by
  exact validCall_input_pointer_of_read_unchanged call
    (fun region hr address ha => validCall_read_unchanged call frame hr ha) i

theorem validCall_input_length_of_read_unchanged {routine : Routine} {initial current : RamState}
    {inputs : Array Input} (call : ValidCall routine initial inputs)
    (unchanged : ∀ region ∈ readRegions initial inputs, ∀ address : BitVec 64,
      region.Contains address.toNat → current.external[address]? = initial.external[address]?)
    (i : Fin inputs.size) :
    memLoad current.external (initial.regValue .rdx + BitVec.ofNat 64 (8 * i.val)) 64 =
      BitVec.ofNat 64 inputs[i].bytes.size := by
  apply Common.Memory.memLoad_of_loadBytes64
  have word := table_word_of_read_unchanged unchanged
    (table := lengthTable initial inputs.size) (by simp [readRegions])
    call.lengthTableValid.2 rfl i (call.inputsInMemory i).2.2.1
  simpa only [lengthTable, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
    BitVec.setWidth_eq] using word


theorem validCall_input_length {routine : Routine} {initial current : RamState}
    {inputs : Array Input} (call : ValidCall routine initial inputs)
    (frame : MemoryWriteFrame initial current
      #v[outputRegion routine initial, Stack.region initial routine.minStackBytes])
    (i : Fin inputs.size) :
    memLoad current.external (initial.regValue .rdx + BitVec.ofNat 64 (8 * i.val)) 64 =
      BitVec.ofNat 64 inputs[i].bytes.size := by
  exact validCall_input_length_of_read_unchanged call
    (fun region hr address ha => validCall_read_unchanged call frame hr ha) i

theorem validCall_prefixMessage_bound {routine : Routine} {initial : RamState}
    {inputs : Array Input} (call : ValidCall routine initial inputs)
    {count : Nat} (within : count ≤ inputs.size) :
    (prefixMessage inputs count).size ≤ count * (2^32 - 1) := by
  induction count with
  | zero => simp [prefixMessage_zero]
  | succ count ih =>
    rw [prefixMessage_succ inputs count (by omega), ByteArray.size_append, Nat.succ_mul]
    have prefixBound := ih (by omega)
    have current := validCall_input_bounded call ⟨count, by omega⟩
    change inputs[count].address.toNat + inputs[count].bytes.size < 2^32 at current
    omega

theorem validCall_message_bound {routine : Routine} {initial : RamState}
    {inputs : Array Input} (call : ValidCall routine initial inputs) :
    (message inputs).size < 2^61 := by
  have prefixBound := validCall_prefixMessage_bound call (Nat.le_refl inputs.size)
  rw [prefixMessage_size] at prefixBound
  have count := validCall_count_bound call
  omega

end Sha2.Proofs.Wrapper
