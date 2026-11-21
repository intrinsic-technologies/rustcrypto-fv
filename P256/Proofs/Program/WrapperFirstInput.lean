import P256.Proofs.ProjectiveWrapper.Input

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem preserved_first_input [Bindings] {routine : Routine} {initial t : RamState}
    {input : ByteArray} {rest : List ByteArray} {slices : Array Input}
    (call : ValidCallWithSlices routine initial (input :: rest) slices)
    (frame : MemoryWriteFrame initial t (wrapperRegions routine initial)) :
    ∃ address, memLoad initial.external (initial.regValue .rdi) 64 = address ∧ address ≠ 0 ∧
      (MemoryRegion.mk address.toNat input.size).Bounded ∧
      (MemoryRegion.mk address.toNat input.size).HasBytes t.external input ∧
      MemReadable t (initial.regValue .rdi) 8 ∧ MemReadable t (initial.regValue .rdx) 8 ∧
      memLoad t.external (initial.regValue .rdi) 64 = address ∧
      memLoad t.external (initial.regValue .rdx) 64 = BitVec.ofNat 64 input.size := by
  have count : slices.size = rest.length + 1 := by
    have h := congrArg Array.size call.slicesHoldInputs
    simpa only [inputBytes, Array.size_map, List.size_toArray, List.length_cons] using h
  have index : 0 < slices.size := by omega
  have bytes : slices[0].bytes = input := by
    have h := congrArg (fun xs : Array ByteArray => xs[0]?) call.slicesHoldInputs
    change (inputBytes slices)[0]? = some input at h
    simpa only [inputBytes, Array.getElem?_map, Array.getElem?_eq_getElem index,
      Option.map_some, Option.some.injEq] using h
  have valid := call.inputsInMemory.slicesValid ⟨0, index⟩
  have p := P256.Proofs.ProjectiveWrapper.preserved_input_at call frame ⟨0, index⟩
  dsimp only [ValidInput, Fin.getElem_fin] at valid
  simp only [Fin.getElem_fin, Nat.mul_zero, BitVec.add_zero] at p
  refine ⟨slices[0].address, ?_, valid.2.2.1, ?_, ?_, p.2.1, p.2.2.1, p.2.2.2.1, ?_⟩
  · simpa using input_pointer_memLoad call.inputsInMemory ⟨0, index⟩
  · simpa only [Input.region, bytes] using valid.2.2.2.1
  · simpa only [Input.region, bytes] using p.1
  · simpa only [bytes] using p.2.2.2.2

theorem first_input_region [Bindings] {routine : Routine} {initial : RamState}
    {input : ByteArray} {rest : List ByteArray} {slices : Array Input}
    (call : ValidCallWithSlices routine initial (input :: rest) slices) :
    (MemoryRegion.mk (memLoad initial.external (initial.regValue .rdi) 64).toNat input.size) ∈
      readRegions initial slices := by
  have count : slices.size = rest.length + 1 := by
    have h := congrArg Array.size call.slicesHoldInputs
    simpa only [inputBytes, Array.size_map, List.size_toArray, List.length_cons] using h
  have index : 0 < slices.size := by omega
  have bytes : slices[0].bytes = input := by
    have h := congrArg (fun xs : Array ByteArray => xs[0]?) call.slicesHoldInputs
    change (inputBytes slices)[0]? = some input at h
    simpa only [inputBytes, Array.getElem?_map, Array.getElem?_eq_getElem index,
      Option.map_some, Option.some.injEq] using h
  have pointer : memLoad initial.external (initial.regValue .rdi) 64 = slices[0].address := by
    simpa using input_pointer_memLoad call.inputsInMemory ⟨0,index⟩
  rw [pointer, ← bytes]
  change slices[0].region ∈ readRegions initial slices
  simp only [readRegions, List.mem_cons]
  right; right
  simpa using (Array.mem_map.mpr ⟨slices[0], Array.getElem_mem index, rfl⟩ :
    slices[0].region ∈ slices.map Input.region)

end P256.Proofs.Program
