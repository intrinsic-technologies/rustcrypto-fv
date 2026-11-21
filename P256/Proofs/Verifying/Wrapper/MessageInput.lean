import P256.Proofs.Verifying.Wrapper.Inputs

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem message_input_bytes [Bindings] {initial : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (index : 2 < slices.size) : slices[2].bytes = message := by
  have eq := congrArg (fun xs : Array ByteArray => xs[2]?) call.slicesHoldInputs
  change (inputBytes slices)[2]? = some message at eq
  simpa only [inputBytes,Array.getElem?_map,Array.getElem?_eq_getElem index,
    Option.map_some,Option.some.injEq] using eq

theorem message_input_region [Bindings] {initial : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices) :
    (MemoryRegion.mk (memLoad initial.external (initial.regValue .rdi+16#64) 64).toNat message.size) ∈
      readRegions initial slices := by
  have index : 2 < slices.size := by rw [call_slice_count call]; decide
  have bytes := message_input_bytes call index
  have pointer : memLoad initial.external (initial.regValue .rdi+16#64) 64 = slices[2].address := by
    simpa using input_pointer_memLoad call.inputsInMemory ⟨2,index⟩
  rw [pointer,← bytes]
  change slices[2].region ∈ readRegions initial slices
  simp only [readRegions,List.mem_cons]
  right; right
  simpa using (Array.mem_map.mpr ⟨slices[2],Array.getElem_mem index,rfl⟩ :
    slices[2].region ∈ slices.map Input.region)

theorem preserved_message_input [Bindings] {initial t : RamState}
    {key signature message : ByteArray} {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (frame : MemoryWriteFrame initial t (wrapperRegions verifyingKeyVerify initial)) :
    ∃ address, memLoad initial.external (initial.regValue .rdi+16#64) 64 = address ∧ address ≠ 0 ∧
      (MemoryRegion.mk address.toNat message.size).Bounded ∧
      (MemoryRegion.mk address.toNat message.size).HasBytes t.external message ∧
      MemReadable t (initial.regValue .rdi+16#64) 8 ∧ MemReadable t (initial.regValue .rdx+16#64) 8 ∧
      memLoad t.external (initial.regValue .rdi+16#64) 64 = address ∧
      memLoad t.external (initial.regValue .rdx+16#64) 64 = BitVec.ofNat 64 message.size := by
  have index : 2 < slices.size := by rw [call_slice_count call]; decide
  have bytes := message_input_bytes call index
  have valid := call.inputsInMemory.slicesValid ⟨2,index⟩
  have p := P256.Proofs.ProjectiveWrapper.preserved_input_at call frame ⟨2,index⟩
  dsimp only [ValidInput,Fin.getElem_fin] at valid
  simp only [Fin.getElem_fin,Nat.reduceMul] at p
  refine ⟨slices[2].address,?_,valid.2.2.1,?_,?_,p.2.1,p.2.2.1,p.2.2.2.1,?_⟩
  · simpa using input_pointer_memLoad call.inputsInMemory ⟨2,index⟩
  · simpa only [Input.region,bytes] using valid.2.2.2.1
  · simpa only [Input.region,bytes] using p.1
  · simpa only [bytes] using p.2.2.2.2

end P256.Proofs.Verifying.Wrapper
