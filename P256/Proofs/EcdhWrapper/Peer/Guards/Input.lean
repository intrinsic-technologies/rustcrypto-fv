import P256.Proofs.ProjectiveWrapper.Input

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Guards

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem preserved_peer [Bindings] {initial t : RamState}
    {secret peer : ByteArray} {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (frame : MemoryWriteFrame initial t (wrapperRegions ecdhDiffieHellman initial)) :
    ∃ address, memLoad initial.external (initial.regValue .rdi+8) 64 = address ∧ address ≠ 0 ∧
      (MemoryRegion.mk address.toNat peer.size).Bounded ∧
      (MemoryRegion.mk address.toNat peer.size).HasBytes t.external peer ∧
      MemReadable t (initial.regValue .rdi+8) 8 ∧ MemReadable t (initial.regValue .rdx+8) 8 ∧
      memLoad t.external (initial.regValue .rdi+8) 64 = address ∧
      memLoad t.external (initial.regValue .rdx+8) 64 = BitVec.ofNat 64 peer.size := by
  have count : slices.size = 2 := by
    have h := congrArg Array.size call.slicesHoldInputs
    simpa only [inputBytes, Array.size_map, List.size_toArray, List.length_cons, List.length_nil, Nat.reduceAdd] using h
  have index : 1 < slices.size := by omega
  have bytes : slices[1].bytes = peer := by
    have h := congrArg (fun xs : Array ByteArray => xs[1]?) call.slicesHoldInputs
    change (inputBytes slices)[1]? = some peer at h
    simpa only [inputBytes, Array.getElem?_map, Array.getElem?_eq_getElem index,
      Option.map_some, Option.some.injEq] using h
  have valid := call.inputsInMemory.slicesValid ⟨1, index⟩
  have p := P256.Proofs.ProjectiveWrapper.preserved_input_at call frame ⟨1, index⟩
  dsimp only [ValidInput, Fin.getElem_fin] at valid
  simp only [Fin.getElem_fin, Nat.mul_one] at p
  refine ⟨slices[1].address, ?_, valid.2.2.1, ?_, ?_, p.2.1, p.2.2.1, p.2.2.2.1, ?_⟩
  · simpa using input_pointer_memLoad call.inputsInMemory ⟨1, index⟩
  · simpa only [Input.region, bytes] using valid.2.2.2.1
  · simpa only [Input.region, bytes] using p.1
  · have h := p.2.2.2.2
    rw [bytes] at h
    exact h

end P256.Proofs.EcdhWrapper.Peer.Guards
