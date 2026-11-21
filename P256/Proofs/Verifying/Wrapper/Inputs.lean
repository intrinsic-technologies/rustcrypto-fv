import P256.Proofs.Verifying.Model
import P256.Proofs.ProjectiveWrapper.Input

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem call_slice_count [Bindings] {initial : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices) :
    slices.size = 3 := by
  have h := congrArg Array.size call.slicesHoldInputs
  simpa only [inputBytes, Array.size_map, List.size_toArray, List.length_cons, List.length_nil] using h

theorem key_input_bytes [Bindings] {initial : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (index : 0 < slices.size) : slices[0].bytes = key := by
  have eq := congrArg (fun xs : Array ByteArray => xs[0]?) call.slicesHoldInputs
  change (inputBytes slices)[0]? = some key at eq
  simpa only [inputBytes, Array.getElem?_map, Array.getElem?_eq_getElem index,
    Option.map_some, Option.some.injEq] using eq

theorem preserved_key_input [Bindings] {initial t : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices)
    (frame : MemoryWriteFrame initial t (wrapperRegions verifyingKeyVerify initial)) :
    ∃ address, memLoad initial.external (initial.regValue .rdi) 64 = address ∧ address ≠ 0 ∧
      (MemoryRegion.mk address.toNat key.size).Bounded ∧
      (MemoryRegion.mk address.toNat key.size).HasBytes t.external key ∧
      MemReadable t (initial.regValue .rdi) 8 ∧ MemReadable t (initial.regValue .rdx) 8 ∧
      memLoad t.external (initial.regValue .rdi) 64 = address ∧
      memLoad t.external (initial.regValue .rdx) 64 = BitVec.ofNat 64 key.size := by
  have index : 0 < slices.size := by rw [call_slice_count call]; decide
  have bytes := key_input_bytes call index
  have valid := call.inputsInMemory.slicesValid ⟨0, index⟩
  have p := P256.Proofs.ProjectiveWrapper.preserved_input_at call frame ⟨0, index⟩
  dsimp only [ValidInput, Fin.getElem_fin] at valid
  simp only [Fin.getElem_fin, Nat.mul_zero, BitVec.add_zero] at p
  refine ⟨slices[0].address, ?_, valid.2.2.1, ?_, ?_, p.2.1, p.2.2.1, p.2.2.2.1, ?_⟩
  · simpa using input_pointer_memLoad call.inputsInMemory ⟨0, index⟩
  · simpa only [Input.region, bytes] using valid.2.2.2.1
  · simpa only [Input.region, bytes] using p.1
  · simpa only [bytes] using p.2.2.2.2

end P256.Proofs.Verifying.Wrapper
