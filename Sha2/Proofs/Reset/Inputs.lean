import Sha2.Proofs.Reset.Memory
import Sha2.Proofs.Wrapper.Inputs
import Sha2.Proofs.Common.SHA256.Absorb.Table
import Sha2.Proofs.Common.Memory.LoadBytes

set_option autoImplicit false

namespace Sha2.Proofs.Reset

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA256.Absorb

theorem table_readable {current : RamState} {base : BitVec 64} {count : Nat}
    (bounded : base.toNat + 8 * count < 2^32)
    (words : ∀ i : Fin count, ∃ value : BitVec 64,
      loadBytes current.external (base + BitVec.ofNat 64 (8 * i.val)) 8 = .ok value) :
    MemReadable current base (8 * count) := by
  refine ⟨by omega, ?_⟩
  intro j hj
  obtain ⟨value, word⟩ := words ⟨j / 8, by omega⟩
  have allocated := Sha2.Proofs.Common.Memory.loadBytes_allocated word (j % 8) (by omega)
  have address : base + BitVec.ofNat 64 (8 * (j / 8)) + BitVec.ofNat 64 (j % 8) =
      base + BitVec.ofNat 64 j := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1
    congr 1
    omega
  simpa only [address] using allocated

theorem table_separation {routine : Routine} {initial current : RamState}
    {inputs : Array Input} (call : TwoOutputs.ValidCall routine initial inputs)
    (layout : Table.Layout)
    (pointer : memLoad current.external
      (layout.chunk.sp initial + BitVec.ofNat 64 layout.pointerSlot) 64 = initial.regValue .rdi)
    (length : memLoad current.external
      (layout.chunk.sp initial + BitVec.ofNat 64 layout.lengthSlot) 64 = initial.regValue .rdx) :
    Table.Separation layout initial current routine.minStackBytes inputs := by
  have apart := (call.separation.2 (Stack.region initial routine.minStackBytes)
    (by simp)).1
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply apart
    simp only [readRegions, List.mem_cons]
    right
    right
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val, by simp, ?_⟩
    simp
  · rw [pointer]
    exact apart (pointerTable initial inputs.size) (by simp [readRegions])
  · rw [length]
    exact apart (lengthTable initial inputs.size) (by simp [readRegions])

theorem table_inputData {routine : Routine} {initial current : RamState}
    {inputs : Array Input} (call : TwoOutputs.ValidCall routine initial inputs)
    (frame : MemoryWriteFrame initial current
      #v[TwoOutputs.outputRegion routine initial, TwoOutputs.secondOutputRegion routine initial,
        Stack.region initial routine.minStackBytes])
    (layout : Table.Layout) (sp : BitVec 64)
    (pointer : memLoad current.external
      (sp + BitVec.ofNat 64 layout.pointerSlot) 64 = initial.regValue .rdi)
    (length : memLoad current.external
      (sp + BitVec.ofNat 64 layout.lengthSlot) 64 = initial.regValue .rdx) :
    Table.InputData layout sp inputs current := by
  have projected := firstOutput_validCall call
  have unchanged : ∀ region ∈ readRegions initial inputs, ∀ address : BitVec 64,
      region.Contains address.toNat → current.external[address]? = initial.external[address]? :=
    fun _ member _ inside ↦ read_unchanged call frame member inside
  refine ⟨?_, Sha2.Proofs.Wrapper.validCall_message_bound projected, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have bound := Sha2.Proofs.Wrapper.validCall_count_bound projected
    omega
  · rw [pointer]
    apply table_readable call.pointerTableValid.2
    intro i
    refine ⟨inputs[i].address, ?_⟩
    have word := Sha2.Proofs.Wrapper.table_word_of_read_unchanged unchanged
      (table := pointerTable initial inputs.size) (by simp [readRegions])
      call.pointerTableValid.2 rfl i (call.inputsInMemory i).2.1
    simpa only [pointerTable, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using word
  · rw [length]
    apply table_readable call.lengthTableValid.2
    intro i
    refine ⟨BitVec.ofNat 64 inputs[i].bytes.size, ?_⟩
    have word := Sha2.Proofs.Wrapper.table_word_of_read_unchanged unchanged
      (table := lengthTable initial inputs.size) (by simp [readRegions])
      call.lengthTableValid.2 rfl i (call.inputsInMemory i).2.2.1
    simpa only [lengthTable, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using word
  · intro i
    rw [pointer]
    exact Sha2.Proofs.Wrapper.validCall_input_pointer_of_read_unchanged projected unchanged i
  · intro i
    rw [length]
    exact Sha2.Proofs.Wrapper.validCall_input_length_of_read_unchanged projected unchanged i
  · intro i
    refine ⟨rfl, ?_⟩
    intro j
    simpa only [Input.region, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      Sha2.Proofs.Wrapper.validCall_input_byte_unchanged_of_read_unchanged projected unchanged i j
  · exact fun i ↦ (call.inputsInMemory i).2.2.2.1

end Sha2.Proofs.Reset
