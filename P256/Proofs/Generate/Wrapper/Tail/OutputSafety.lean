import P256.Proofs.Generate.Wrapper.Tail.Output
import P256.Proofs.Common.Instructions.CrossPageStore.Range

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Common.Instructions

theorem output_region_eq {initial : RamState} {input : ByteArray} {d : Nat}
    (draw : Ecdh.drawNonzeroScalar input = some d) :
    outputRegion signingKeyGenerateFromRng initial [input] = registerRegion initial .rcx 105 := by
  change registerRegion initial .rcx (8+(Spec.Generate.generatedSigningKey #[input]).size) = _
  rw [generated_key_size draw]

theorem output_capacity [Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} {d : Nat}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d) : 105 ≤ (initial.regValue .r8).toNat := by
  have bound := call.outputSufficesIfAccepted rfl
  change 8+(Spec.Generate.generatedSigningKey #[input]).size ≤ _ at bound
  rwa [generated_key_size draw] at bound

theorem output_writable [Bindings] {initial t : RamState} {input : ByteArray}
    {slices : Array Input} {d : Nat}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d)
    (grown : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome) :
    CrossPageStore.Writable t (initial.regValue .rcx) 105 := by
  have bounded : (registerRegion initial .rcx 105).Bounded := by
    simpa only [ValidOutput,output_region_eq draw] using (call.outputInMemoryIfAccepted rfl).2.1
  have allocated : (registerRegion initial .rcx 105).Allocated initial.external := by
    simpa only [ValidOutput,output_region_eq draw] using (call.outputInMemoryIfAccepted rfl).2.2
  have readable := readable_of_grow
    (memoryRegion_memReadable bounded allocated (Nat.le_refl _) (Nat.le_refl _)) grown
  refine ⟨readable,tables_of_not_reserved (by decide) readable.low ?_⟩
  intro i hi hp
  apply ((call.outputSeparationIfAccepted rfl).2
    (outputRegion signingKeyGenerateFromRng initial [input]) (by simp)).2 _ ?_ (.inr hp)
  rw [output_region_eq draw]
  exact memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem output_contains [Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} {d off len : Nat} {a : BitVec 64}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d) (bound : off+len ≤ 105)
    (covers : (Component.mem (initial.regValue .rcx+BitVec.ofNat 64 off) len).Covers a) :
    (outputRegion signingKeyGenerateFromRng initial [input]).Contains a.toNat := by
  have bounded : (registerRegion initial .rcx 105).Bounded := by
    simpa only [ValidOutput,output_region_eq draw] using (call.outputInMemoryIfAccepted rfl).2.1
  obtain ⟨i,hi,rfl⟩ := covers
  rw [BitVec.add_assoc,← BitVec.ofNat_add,output_region_eq draw]
  exact memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) (by change off+i < 105; omega)

theorem output_code [Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} {d off len codeOffset codeLen : Nat}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d) (bound : off+len ≤ 105)
    (code : codeOffset+codeLen ≤ 118431) :
    RangeApart (initial.regValue .rcx+BitVec.ofNat 64 off) len
      (Extracted.textAddress+BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj eq
  apply ((call.outputSeparationIfAccepted rfl).2
    (outputRegion signingKeyGenerateFromRng initial [input]) (by simp)).2 _
      (output_contains call draw bound ⟨i,hi,rfl⟩) (.inl ?_)
  rw [eq,BitVec.add_assoc,← BitVec.ofNat_add]
  exact inProgram_of_textOffset _ (by omega)

end P256.Proofs.Generate.Wrapper
