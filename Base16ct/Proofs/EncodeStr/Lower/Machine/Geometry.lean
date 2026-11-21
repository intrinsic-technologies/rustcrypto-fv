import Base16ct.Proofs.EncodeStr.Lower.Machine.Interface
import Base16ct.Proofs.Copied.Md5.Proofs.Machine
import Base16ct.Proofs.Copied.Md5.Proofs.Memory.Basic
namespace Base16ct.Proofs.EncodeStr.Lower

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable {initial s t : RamState} {input : List UInt8} {capacity written : Nat}

theorem address_add_toNat {address : BitVec 64} {offset : Nat}
    (bound : address.toNat + offset < 2 ^ 64) :
    (address + BitVec.ofNat 64 offset).toNat = address.toNat + offset := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show offset < 2 ^ 64 by omega), Nat.mod_eq_of_lt bound]

theorem region_contains_offset {region : MemoryRegion} {address : BitVec 64}
    {len index : Nat} (bound : region.Bounded) (low : region.start ≤ address.toNat)
    (high : address.toNat + len ≤ region.start + region.size) (inside : index < len) :
    region.Contains (address + BitVec.ofNat 64 index).toNat := by
  change region.start + region.size < 2 ^ 32 at bound
  rw [address_add_toNat (by omega)]
  exact ⟨by omega, by omega⟩

theorem validCall_stack_bounds (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity)) :
    32 ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2 ^ 32 := by
  refine ⟨by have h := call.stack.2.2.1; change 160 ≤ (stackPtr initial).toNat at h; omega, ?_⟩
  have bound := call.stack.1
  change (initial.regValue .rsp).toNat - 160 +
    ((initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - 160)) <
      2 ^ 32 at bound
  change (initial.regValue .rsp).toNat + 8 < 2 ^ 32
  omega

theorem validCall_stack_sub_toNat (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset : Nat} (low : offset ≤ 32) :
    (stackPtr initial - BitVec.ofNat 64 offset).toNat =
      (stackPtr initial).toNat - offset := by
  have bounds := validCall_stack_bounds call
  rw [BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem stack_memory_contains (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len : Nat} (low : offset ≤ 32) (high : len ≤ offset + 8)
    {address : BitVec 64}
    (inside : (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Covers address) :
    (Stack.region initial base16ctLowerEncodeStr.minStackBytes).Contains address.toNat := by
  obtain ⟨index, index_lt, rfl⟩ := inside
  have bounds := validCall_stack_bounds call
  apply region_contains_offset call.stack.1 (len := len) (index := index) _ _ index_lt
  · rw [validCall_stack_sub_toNat call low]
    change (stackPtr initial).toNat - 160 ≤ (stackPtr initial).toNat - offset
    omega
  · rw [validCall_stack_sub_toNat call low]
    change (stackPtr initial).toNat - offset + len ≤
      (stackPtr initial).toNat - 160 +
        ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 160))
    omega

theorem validCall_stack_sub_readable
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len : Nat} (low : offset ≤ 32) (high : len ≤ offset + 8) :
    MemReadable initial (stackPtr initial - BitVec.ofNat 64 offset) len := by
  have bounds := validCall_stack_bounds call
  apply Base16ct.Proofs.Copied.Md5.Proofs.memReadable_of_allocated call.stack.2.1
  · rw [validCall_stack_sub_toNat call low]
    change (stackPtr initial).toNat - offset + len ≤ 2 ^ 32
    omega
  · rw [validCall_stack_sub_toNat call low]
    change (stackPtr initial).toNat - 160 ≤ (stackPtr initial).toNat - offset
    omega
  · rw [validCall_stack_sub_toNat call low]
    change (stackPtr initial).toNat - offset + len ≤
      (stackPtr initial).toNat - 160 +
        ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 160))
    omega

theorem stack_avoids_program (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len : Nat} (low : offset ≤ 32) (high : len ≤ offset + 8) :
    ∀ index < len, ¬ InProgram
      (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 index) := by
  intro index inside program
  exact call.separation.2.1 _ (by simp) _
    (stack_memory_contains call low high ⟨index, inside, rfl⟩) (.inl program)

theorem validCall_stack_sub_writable
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len : Nat} (low : offset ≤ 32) (high : len ≤ offset + 8)
    (positive : 0 < len)
    (_page : (stackPtr initial - BitVec.ofNat 64 offset).toNat % 4096 + len ≤ 4096) :
    MemWritable initial (stackPtr initial - BitVec.ofNat 64 offset) len := by
  have readable := validCall_stack_sub_readable call low high
  refine MemWritable.of_not_reserved positive readable.low readable.mem ?_
  intro index inside reserved
  exact call.separation.2.1 _ (by simp) _
    (stack_memory_contains call low high ⟨index, inside, rfl⟩) (.inr reserved)

theorem validCall_stack_sub_writable8
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset : Nat} (low : offset ≤ 32) (align : offset % 8 = 0) :
    MemWritable initial (stackPtr initial - BitVec.ofNat 64 offset) 8 := by
  apply validCall_stack_sub_writable call low (by omega) (by decide)
  rw [validCall_stack_sub_toNat call low]
  have bounds := validCall_stack_bounds call
  have stackalign : (stackPtr initial).toNat % 16 = 8 := call.stack.2.2.2
  have modulus := Nat.mod_mod_of_dvd ((stackPtr initial).toNat - offset)
    (show 8 ∣ 4096 by decide)
  omega

theorem validCall_stack_sub_writable4
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset : Nat} (low : offset ≤ 32) (align : offset % 4 = 0) :
    MemWritable initial (stackPtr initial - BitVec.ofNat 64 offset) 4 := by
  apply validCall_stack_sub_writable call low (by omega) (by decide)
  rw [validCall_stack_sub_toNat call low]
  have bounds := validCall_stack_bounds call
  have stackalign : (stackPtr initial).toNat % 16 = 8 := call.stack.2.2.2
  have modulus := Nat.mod_mod_of_dvd ((stackPtr initial).toNat - offset)
    (show 4 ∣ 4096 by decide)
  omega

theorem validCall_stack_sub_writable1
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset : Nat} (low : offset ≤ 32) :
    MemWritable initial (stackPtr initial - BitVec.ofNat 64 offset) 1 := by
  apply validCall_stack_sub_writable call low (by omega) (by decide)
  have bound := Nat.mod_lt (stackPtr initial - BitVec.ofNat 64 offset).toNat
    (by decide : 0 < 4096)
  omega

theorem stack_readable [Bindings]
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s)
    {offset len : Nat} (low : offset ≤ 32) (high : len ≤ offset + 8) :
    MemReadable s (stackPtr initial - BitVec.ofNat 64 offset) len := by
  have readable := validCall_stack_sub_readable call low high
  exact ⟨readable.low, fun index inside ↦ state.grows _ (readable.mem index inside)⟩

theorem stack_writable [Bindings]
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s)
    {offset len : Nat} (low : offset ≤ 32) (high : len ≤ offset + 8)
    (positive : 0 < len)
    (page : (stackPtr initial - BitVec.ofNat 64 offset).toNat % 4096 + len ≤ 4096) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) len := by
  have writable := validCall_stack_sub_writable call low high positive page
  exact ⟨writable.low,
    fun index inside ↦ state.grows _ (writable.mem index inside), writable.tables⟩

theorem stack_writable8 [Bindings]
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s)
    {offset : Nat} (low : offset ≤ 32) (align : offset % 8 = 0) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 8 := by
  have writable := validCall_stack_sub_writable8 call low align
  exact ⟨writable.low,
    fun index inside ↦ state.grows _ (writable.mem index inside), writable.tables⟩

theorem stack_writable4 [Bindings]
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s)
    {offset : Nat} (low : offset ≤ 32) (align : offset % 4 = 0) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 4 := by
  have writable := validCall_stack_sub_writable4 call low align
  exact ⟨writable.low,
    fun index inside ↦ state.grows _ (writable.mem index inside), writable.tables⟩

theorem stack_writable1 [Bindings]
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s)
    {offset : Nat} (low : offset ≤ 32) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 1 := by
  have writable := validCall_stack_sub_writable1 call low
  exact ⟨writable.low,
    fun index inside ↦ state.grows _ (writable.mem index inside), writable.tables⟩

theorem MachineInvariant.widen [Bindings] {small large : Nat}
    (state : MachineInvariant initial small s) (bound : small ≤ large) :
    MachineInvariant initial large s := by
  refine { state with memoryFrame := ?_ }
  intro address outside
  apply state.memoryFrame address
  intro region member contains
  have cases : region = outputRegion initial small ∨
      region = Stack.region initial base16ctLowerEncodeStr.minStackBytes := by
    simpa [writableRegions] using member
  rcases cases with rfl | rfl
  · apply outside (outputRegion initial large) (by simp [writableRegions])
    exact ⟨contains.1, Nat.lt_of_lt_of_le contains.2 (Nat.add_le_add_left bound _)⟩
  · exact outside _ (by simp [writableRegions]) contains

theorem input_disjoint_writable
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity)) :
    ∀ region ∈ writableRegions initial capacity,
      (inputRegion initial input.toByteArray).Disjoint region := by
  intro region member
  have cases : region = outputRegion initial capacity ∨
      region = Stack.region initial base16ctLowerEncodeStr.minStackBytes := by
    simpa [writableRegions] using member
  rcases cases with rfl | rfl
  · exact call.separation.1 0 1 (by decide)
  · exact call.separation.1 0 2 (by decide)

theorem input_hasBytes [Bindings]
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial capacity s) :
    (inputRegion initial input.toByteArray).HasBytes s.external input.toByteArray :=
  Base16ct.Proofs.Copied.Md5.Proofs.hasBytes_of_memoryWriteFrame state.memoryFrame call.inputInMemory.2.2
    call.inputInMemory.2.1 (input_disjoint_writable call)

theorem input_byte_memory [Bindings]
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial capacity s) {index : Nat} (inside : index < input.length) :
    s.external[initial.regValue .rdi + BitVec.ofNat 64 index]? = some input[index] := by
  have byte := (input_hasBytes call state).2
    ⟨index, by simpa only [List.size_toByteArray] using inside⟩
  simpa only [inputRegion, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, List.getElem_toByteArray] using byte

theorem input_byte_read [Bindings]
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s) {index : Nat} (inside : index < input.length)
    (written_le : written ≤ capacity := by split <;> omega) :
    MemReadable s (initial.regValue .rdi + BitVec.ofNat 64 index) 1 ∧
      (Operand.mem (initial.regValue .rdi + BitVec.ofNat 64 index) : Operand 8).read s =
        input[index].toBitVec := by
  have bound : (initial.regValue .rdi).toNat + input.length < 2 ^ 32 := by simpa only [inputRegion, registerRegion, MemoryRegion.Bounded, userAddressLimit, List.size_toByteArray] using call.inputInMemory.2.1
  have address := address_add_toNat (address := initial.regValue .rdi)
    (offset := index) (by omega)
  have byte := input_byte_memory call (state.widen written_le) inside
  constructor
  · refine ⟨?_, ?_⟩
    · rw [address]
      change (initial.regValue .rdi).toNat + index + 1 ≤ 2 ^ 32
      omega
    · intro offset low
      have zero : offset = 0 := by omega
      subst offset
      simp only [BitVec.add_zero, byte, Option.isSome_some]
  · simp only [Operand.read, memLoad_8, memByte, PhysicalMemory.read, byte, Option.getD_some]

theorem output_address_toNat (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len : Nat} (high : offset + len ≤ capacity) :
    (initial.regValue .rcx + BitVec.ofNat 64 offset).toNat =
      (initial.regValue .rcx).toNat + offset := by
  have bound : (initial.regValue .rcx).toNat + capacity < 2 ^ 32 := call.outputInMemory.2.1
  exact address_add_toNat (by omega)

theorem output_memory_contains (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len : Nat} (high : offset + len ≤ capacity) {address : BitVec 64}
    (inside : (Component.mem (initial.regValue .rcx + BitVec.ofNat 64 offset) len).Covers
      address) : (outputRegion initial capacity).Contains address.toNat := by
  obtain ⟨index, index_lt, rfl⟩ := inside
  apply region_contains_offset call.outputInMemory.2.1 (len := len) (index := index) _ _ index_lt
  · rw [output_address_toNat call high]
    change (initial.regValue .rcx).toNat ≤ (initial.regValue .rcx).toNat + offset
    omega
  · rw [output_address_toNat call high]
    change (initial.regValue .rcx).toNat + offset + len ≤
      (initial.regValue .rcx).toNat + capacity
    omega

theorem output_memory_contains_written
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len : Nat} (bound : written ≤ capacity) (high : offset + len ≤ written)
    {address : BitVec 64}
    (inside : (Component.mem (initial.regValue .rcx + BitVec.ofNat 64 offset) len).Covers address) :
    (outputRegion initial written).Contains address.toNat := by
  obtain ⟨index, index_lt, rfl⟩ := inside
  have hcap : offset + len ≤ capacity := Nat.le_trans high bound
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, output_address_toNat call (len := 0) (by omega)]
  change (initial.regValue .rcx).toNat ≤ (initial.regValue .rcx).toNat + (offset + index) ∧
    (initial.regValue .rcx).toNat + (offset + index) < (initial.regValue .rcx).toNat + written
  omega

theorem output_avoids_program (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len : Nat} (high : offset + len ≤ capacity) :
    ∀ index < len, ¬ InProgram
      (initial.regValue .rcx + BitVec.ofNat 64 offset + BitVec.ofNat 64 index) := by
  intro index inside program
  exact call.separation.2.1 _ (by simp) _
    (output_memory_contains call high ⟨index, inside, rfl⟩) (.inl program)

theorem output_byte_writable [Bindings]
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s) {index : Nat} (inside : index < capacity) :
    MemWritable s (initial.regValue .rcx + BitVec.ofNat 64 index) 1 := by
  have high : index + 1 ≤ capacity := by omega
  have initialRead : MemReadable initial (initial.regValue .rcx + BitVec.ofNat 64 index) 1 := by
    apply Base16ct.Proofs.Copied.Md5.Proofs.memReadable_of_allocated call.outputInMemory.2.2
    · rw [output_address_toNat call high]
      have bound : (initial.regValue .rcx).toNat + capacity < 2 ^ 32 := call.outputInMemory.2.1
      change (initial.regValue .rcx).toNat + index + 1 ≤ 2 ^ 32
      omega
    · rw [output_address_toNat call high]
      change (initial.regValue .rcx).toNat ≤ (initial.regValue .rcx).toNat + index
      omega
    · rw [output_address_toNat call high]
      change (initial.regValue .rcx).toNat + index + 1 ≤
        (initial.regValue .rcx).toNat + capacity
      omega
  refine MemWritable.of_not_reserved (by decide) initialRead.low
    (fun offset low ↦ state.grows _ (initialRead.mem offset low)) ?_
  intro offset low reserved
  exact call.separation.2.1 _ (by simp) _
    (output_memory_contains call high ⟨offset, low, rfl⟩) (.inr reserved)

theorem stack_store_within (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len : Nat} (low : offset ≤ 32) (high : len ≤ offset + 8) :
    WritesWithin [.mem (stackPtr initial - BitVec.ofNat 64 offset) len, .rip]
      (writableRegions initial written) := by
  intro component member address covers
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨_, by simp [writableRegions], stack_memory_contains call low high covers⟩
  · exact covers.elim

theorem output_store_within (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len : Nat} (high : offset + len ≤ capacity) :
    WritesWithin [.mem (initial.regValue .rcx + BitVec.ofNat 64 offset) len, .rip]
      (writableRegions initial capacity) := by
  intro component member address covers
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨_, by simp [writableRegions], output_memory_contains call high covers⟩
  · exact covers.elim

theorem stack_codeApart (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len codeOffset codeLen : Nat} (low : offset ≤ 32) (high : len ≤ offset + 8)
    (code : codeOffset + codeLen ≤ Extracted.textBytes.size) :
    RangeApart (stackPtr initial - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro index inside codeIndex codeInside equal
  apply stack_avoids_program call low high index inside
  rw [equal, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact text_address_in_program (codeOffset + codeIndex) (by omega)

theorem output_codeApart (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len codeOffset codeLen : Nat} (high : offset + len ≤ capacity)
    (code : codeOffset + codeLen ≤ Extracted.textBytes.size) :
    RangeApart (initial.regValue .rcx + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro index inside codeIndex codeInside equal
  apply output_avoids_program call high index inside
  rw [equal, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact text_address_in_program (codeOffset + codeIndex) (by omega)

theorem output_stack_apart (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len stackOffset stackLen : Nat} (high : offset + len ≤ capacity)
    (stackLow : stackOffset ≤ 32) (stackHigh : stackLen ≤ stackOffset + 8) :
    RangeApart (initial.regValue .rcx + BitVec.ofNat 64 offset) len
      (stackPtr initial - BitVec.ofNat 64 stackOffset) stackLen := by
  intro index inside stackIndex stackInside equal
  have outputContains := output_memory_contains call high ⟨index, inside, rfl⟩
  have stackContains := stack_memory_contains call stackLow stackHigh
    ⟨stackIndex, stackInside, rfl⟩
  have separation : (outputRegion initial capacity).Disjoint
      (Stack.region initial base16ctLowerEncodeStr.minStackBytes) :=
    call.separation.1 1 2 (by decide)
  rw [equal] at outputContains
  exact separation _ outputContains stackContains

theorem stack_return_apart (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len : Nat} (low : offset ≤ 32) (high : len ≤ offset) :
    RangeApart (stackPtr initial - BitVec.ofNat 64 offset) len (stackPtr initial) 8 := by
  have bounds := validCall_stack_bounds call
  apply RangeApart.of_toNat
  · rw [validCall_stack_sub_toNat call low]
    omega
  · omega
  · left
    rw [validCall_stack_sub_toNat call low]
    omega

theorem stack_store_return_preserved
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len : Nat} (low : offset ≤ 32) (high : len ≤ offset)
    (frame : AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 offset) len, .rip] s t) :
    (Operand.mem (stackPtr initial) : Operand 64).read t =
      (Operand.mem (stackPtr initial) : Operand 64).read s := by
  apply memLoad_congr
  intro index inside
  apply congrArg (fun byte : Option UInt8 ↦ byte.getD 0)
  apply frame.byte
  intro component member covers
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · obtain ⟨writeIndex, writeInside, equal⟩ := covers
    exact stack_return_apart call low high writeIndex writeInside index inside equal.symm
  · exact covers.elim

theorem stack_slots_apart (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {leftOffset leftLen rightOffset rightLen : Nat}
    (leftLow : leftOffset ≤ 32) (leftHigh : leftLen ≤ leftOffset + 8)
    (rightLow : rightOffset ≤ 32) (rightHigh : rightLen ≤ rightOffset + 8)
    (apart : rightOffset + leftLen ≤ leftOffset ∨ leftOffset + rightLen ≤ rightOffset) :
    RangeApart (stackPtr initial - BitVec.ofNat 64 leftOffset) leftLen
      (stackPtr initial - BitVec.ofNat 64 rightOffset) rightLen := by
  have bounds := validCall_stack_bounds call
  apply RangeApart.of_toNat
  · rw [validCall_stack_sub_toNat call leftLow]
    omega
  · rw [validCall_stack_sub_toNat call rightLow]
    omega
  · rw [validCall_stack_sub_toNat call leftLow, validCall_stack_sub_toNat call rightLow]
    omega

theorem stack_store_output_byte_preserved
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset len : Nat} (low : offset ≤ 32) (high : len ≤ offset + 8)
    (frame : AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 offset) len, .rip] s t)
    {index : Nat} (inside : index < capacity) :
    t.external[initial.regValue .rcx + BitVec.ofNat 64 index]? =
      s.external[initial.regValue .rcx + BitVec.ofNat 64 index]? := by
  apply frame.byte
  intro component member covers
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · obtain ⟨writeIndex, writeInside, equal⟩ := covers
    apply output_stack_apart call (offset := index) (len := 1) (by omega)
      low high 0 (by decide) writeIndex writeInside
    simpa only [BitVec.add_zero] using equal
  · exact covers.elim

theorem validCall_stack_offset_toNat
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    {offset : Nat} (high : offset ≤ 40) :
    (stackPtr initial - 32 + BitVec.ofNat 64 offset).toNat =
      (stackPtr initial).toNat - 32 + offset := by
  have bounds := validCall_stack_bounds call
  have sub : (stackPtr initial - 32).toNat = (stackPtr initial).toNat - 32 := by
    simpa only [BitVec.ofNat_eq_ofNat] using
      validCall_stack_sub_toNat call (offset := 32) (by decide)
  rw [address_add_toNat (by omega), sub]

theorem stack_offset_readable [Bindings]
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s)
    {offset len : Nat} (high : offset + len ≤ 40) :
    MemReadable s (stackPtr initial - 32 + BitVec.ofNat 64 offset) len := by
  have readable : MemReadable s (stackPtr initial - 32) 40 := by
    simpa only [BitVec.ofNat_eq_ofNat] using
      stack_readable call state (offset := 32) (len := 40) (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · have low := readable.low
    rw [address_add_toNat (by omega)]
    omega
  · intro index inside
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact readable.mem (offset + index) (by omega)

theorem stack_offset_writable [Bindings]
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s)
    {offset len : Nat} (high : offset + len ≤ 40) (positive : 0 < len)
    (_page : (stackPtr initial - 32 + BitVec.ofNat 64 offset).toNat % 4096 + len ≤ 4096) :
    MemWritable s (stackPtr initial - 32 + BitVec.ofNat 64 offset) len := by
  have readable := stack_offset_readable call state high
  refine MemWritable.of_not_reserved positive readable.low readable.mem ?_
  intro index inside reserved
  exact call.separation.2.1 (Stack.region initial base16ctLowerEncodeStr.minStackBytes)
    (by simp) _ (by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact stack_memory_contains call (offset := 32) (len := 40) (by decide) (by decide)
      ⟨offset + index, by omega, rfl⟩) (.inr reserved)

theorem stack_offset_writable8 [Bindings]
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s)
    {offset : Nat} (high : offset + 8 ≤ 40) (align : offset % 8 = 0) :
    MemWritable s (stackPtr initial - 32 + BitVec.ofNat 64 offset) 8 := by
  apply stack_offset_writable call state high (by decide)
  rw [validCall_stack_offset_toNat call (by omega)]
  have bounds := validCall_stack_bounds call
  have stackalign : (stackPtr initial).toNat % 16 = 8 := call.stack.2.2.2
  have modulus := Nat.mod_mod_of_dvd ((stackPtr initial).toNat - 32 + offset)
    (show 8 ∣ 4096 by decide)
  omega

theorem stack_offset_writable4 [Bindings]
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s)
    {offset : Nat} (high : offset + 4 ≤ 40) (align : offset % 4 = 0) :
    MemWritable s (stackPtr initial - 32 + BitVec.ofNat 64 offset) 4 := by
  apply stack_offset_writable call state high (by decide)
  rw [validCall_stack_offset_toNat call (by omega)]
  have bounds := validCall_stack_bounds call
  have stackalign : (stackPtr initial).toNat % 16 = 8 := call.stack.2.2.2
  have modulus := Nat.mod_mod_of_dvd ((stackPtr initial).toNat - 32 + offset)
    (show 4 ∣ 4096 by decide)
  omega

theorem stack_offset_writable1 [Bindings]
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s)
    {offset : Nat} (high : offset + 1 ≤ 40) :
    MemWritable s (stackPtr initial - 32 + BitVec.ofNat 64 offset) 1 := by
  apply stack_offset_writable call state high (by decide)
  have bound := Nat.mod_lt (stackPtr initial - 32 + BitVec.ofNat 64 offset).toNat
    (by decide : 0 < 4096)
  omega

theorem length_output_contains
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (fits : 2 * input.length ≤ capacity) {address : BitVec 64}
    (inside : (Component.mem (initial.regValue .rdx) 8).Covers address) :
    (lengthOutputRegion initial).Contains address.toNat := by
  obtain ⟨index, index_lt, rfl⟩ := inside
  exact region_contains_offset (call.lengthOutputInMemoryIfLengthWritten fits).1
    (Nat.le_refl _) (Nat.le_refl _) index_lt

theorem length_output_writable [Bindings]
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s) (fits : 2 * input.length ≤ capacity) :
    Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (initial.regValue .rdx) 8 := by
  have valid := call.lengthOutputInMemoryIfLengthWritten fits
  have initialWritable : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable initial (initial.regValue .rdx) 8 := by
    apply Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable.of_region valid.1 valid.2
    · intro address contains tables
      apply (call.separation.2.2 fits).2 address contains
      apply Or.inr
      obtain ⟨region, member, inside⟩ := tables
      simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + 8 at inside
        change 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + 0x2000
        omega
      · change 0x2000 ≤ address.toNat ∧ address.toNat < 0x2000 + 32 at inside
        change 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + 0x2000
        omega
    · exact Nat.le_refl _
    · exact Nat.le_refl _
  exact ⟨initialWritable.low, fun i hi ↦ state.grows _ (initialWritable.bytes i hi),
    initialWritable.tables⟩

theorem length_output_avoids_program
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (fits : 2 * input.length ≤ capacity) :
    ∀ i < 8, ¬ InProgram (initial.regValue .rdx + BitVec.ofNat 64 i) := by
  intro i hi inside
  exact (call.separation.2.2 fits).2 _
    (length_output_contains call fits ⟨i, hi, rfl⟩) (.inl inside)

theorem length_output_apart_stack
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (fits : 2 * input.length ≤ capacity) {offset len : Nat}
    (low : offset ≤ 32) (high : len ≤ offset + 8) :
    RangeApart (initial.regValue .rdx) 8
      (stackPtr initial - BitVec.ofNat 64 offset) len := by
  intro i hi j hj equal
  have a := length_output_contains call fits ⟨i, hi, rfl⟩
  have b := stack_memory_contains call low high ⟨j, hj, rfl⟩
  have apart : (lengthOutputRegion initial).Disjoint
      (Stack.region initial base16ctLowerEncodeStr.minStackBytes) :=
    (call.separation.2.2 fits).1 0 2 (by decide)
  rw [equal] at a
  exact apart _ a b

theorem length_output_apart_output
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (fits : 2 * input.length ≤ capacity) {offset len : Nat} (high : offset + len ≤ 2 * input.length) :
    RangeApart (initial.regValue .rdx) 8
      (initial.regValue .rcx + BitVec.ofNat 64 offset) len := by
  intro i hi j hj equal
  have a := length_output_contains call fits ⟨i, hi, rfl⟩
  have b : (outputRegion initial (2 * input.length)).Contains
      (initial.regValue .rcx + BitVec.ofNat 64 offset + BitVec.ofNat 64 j).toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    apply region_contains_offset (len := 2 * input.length)
      (by have h := call.outputInMemory.2.1; change (initial.regValue .rcx).toNat + capacity < 2 ^ 32 at h;
          change (initial.regValue .rcx).toNat + 2 * input.length < 2 ^ 32; omega)
      (Nat.le_refl _) (Nat.le_refl _) (by omega)
  have apart : (lengthOutputRegion initial).Disjoint (outputRegion initial (2 * input.length)) :=
    (call.separation.2.2 fits).1 0 1 (by decide)
  rw [equal] at a
  exact apart _ a b

end Base16ct.Proofs.EncodeStr.Lower
