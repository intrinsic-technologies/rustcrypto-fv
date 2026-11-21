import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem singleton_call_input [Bindings] {routine : Routine} {s : RamState} {input : ByteArray}
    {slices : Array Input} (h : ValidCallWithSlices routine s [input] slices) :
    ∃ address, slices = #[Input.mk address input] ∧
      (MemoryRegion.mk (s.regValue .rdi).toNat 8).Word64At s.external address ∧
      (MemoryRegion.mk (s.regValue .rdx).toNat 8).Word64At s.external (BitVec.ofNat 64 input.size) ∧
      address ≠ 0 ∧ (MemoryRegion.mk address.toNat input.size).Bounded ∧
      (MemoryRegion.mk address.toNat input.size).HasBytes s.external input := by
  obtain ⟨address, he⟩ := singleton_input h.slicesHoldInputs
  subst slices
  refine ⟨address, rfl, ?_⟩
  have hv := h.inputsInMemory.slicesValid ⟨0, by simp⟩
  simpa [ValidInput, tableEntry, pointerTable, lengthTable, registerRegion, Input.region] using hv

theorem preserved_input [Bindings] {routine : Routine} {s t : RamState} {input : ByteArray}
    {slices : Array Input} (h : ValidCallWithSlices routine s [input] slices)
    (frame : MemoryWriteFrame s t (wrapperRegions routine s)) :
    ∃ address, memLoad s.external (s.regValue .rdi) 64 = address ∧
      address ≠ 0 ∧ (MemoryRegion.mk address.toNat input.size).Bounded ∧
      (MemoryRegion.mk address.toNat input.size).HasBytes t.external input ∧
      MemReadable t (s.regValue .rdi) 8 ∧ MemReadable t (s.regValue .rdx) 8 ∧
      memLoad t.external (s.regValue .rdi) 64 = address ∧
      memLoad t.external (s.regValue .rdx) 64 = BitVec.ofNat 64 input.size := by
  obtain ⟨address, he, _, _, hn, hb, hbytes⟩ := singleton_call_input h
  subst slices
  have pb : (MemoryRegion.mk (s.regValue .rdi).toNat 8).Bounded := by
    simpa [pointerTable, registerRegion] using h.inputsInMemory.pointerTableValid.2
  have lb : (MemoryRegion.mk (s.regValue .rdx).toNat 8).Bounded := by
    simpa [lengthTable, registerRegion] using h.inputsInMemory.lengthTableValid.2
  have rp : (MemoryRegion.mk (s.regValue .rdi).toNat 8) ∈ readRegions s #[Input.mk address input] := by
    simp [readRegions, pointerTable, registerRegion]
  have rl : (MemoryRegion.mk (s.regValue .rdx).toNat 8) ∈ readRegions s #[Input.mk address input] := by
    simp [readRegions, lengthTable, registerRegion]
  have ri : (MemoryRegion.mk address.toNat input.size) ∈ readRegions s #[Input.mk address input] := by
    simp [readRegions, Input.region]
  have originalPointer : memLoad s.external (s.regValue .rdi) 64 = address := by
    simpa using input_pointer_memLoad h.inputsInMemory ⟨0, by simp⟩
  have originalLength : memLoad s.external (s.regValue .rdx) 64 = BitVec.ofNat 64 input.size := by
    simpa using input_length_memLoad h.inputsInMemory ⟨0, by simp⟩
  have mp := frame_memLoad frame (wrapper_read_disjoint h rp) pb (width := 64)
    (Nat.le_refl _) (Nat.le_refl _)
  have ml := frame_memLoad frame (wrapper_read_disjoint h rl) lb (width := 64)
    (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨address, originalPointer, hn, hb,
    frame_hasBytes frame (wrapper_read_disjoint h ri) hb hbytes, ?_, ?_,
    mp.trans originalPointer, ml.trans originalLength⟩
  · have hw : MemReadable s (s.regValue .rdi) 8 := by
      simpa using input_pointer_memReadable h.inputsInMemory ⟨0, by simp⟩
    refine ⟨hw.low, ?_⟩
    intro i hi
    rw [frame_read frame (wrapper_read_disjoint h rp)
      (memoryRegion_contains_add pb (Nat.le_refl _) (Nat.le_refl _) hi)]
    exact hw.mem i hi
  · have hw : MemReadable s (s.regValue .rdx) 8 := by
      simpa using input_length_memReadable h.inputsInMemory ⟨0, by simp⟩
    refine ⟨hw.low, ?_⟩
    intro i hi
    rw [frame_read frame (wrapper_read_disjoint h rl)
      (memoryRegion_contains_add lb (Nat.le_refl _) (Nat.le_refl _) hi)]
    exact hw.mem i hi

end P256.Proofs.Program
