import Sha2.Spec.Program

set_option autoImplicit false

namespace Sha2.Proofs.Reset

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess

theorem firstOutput_validCall {routine : Routine} {initial : RamState}
    {inputs : Array Input} (call : TwoOutputs.ValidCall routine initial inputs) :
    ValidCall routine initial inputs := by
  refine ⟨call.directionFlagUnset, call.programLoaded, call.entry,
    call.countArgumentMatchesInputs, call.pointerTableValid, call.lengthTableValid,
    call.inputsInMemory, ?_, call.stack, ?_, call.returnAddress⟩
  · exact call.outputInMemory _ (by simp [TwoOutputs.outputRegion, outputRegion])
  · have subset : ∀ region ∈ [outputRegion routine initial,
        Stack.region initial routine.minStackBytes],
        region ∈ [TwoOutputs.outputRegion routine initial,
          TwoOutputs.secondOutputRegion routine initial,
          Stack.region initial routine.minStackBytes] := by
      intro region member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    refine ⟨?_, fun region member ↦ call.separation.2 region (subset region member)⟩
    have pairs := call.separation.1
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false] at pairs ⊢
    exact ⟨fun region same ↦ pairs.1 region (Or.inr same),
      fun _ impossible ↦ impossible.elim, .nil⟩

theorem read_unchanged {routine : Routine} {initial current : RamState}
    {inputs : Array Input} (call : TwoOutputs.ValidCall routine initial inputs)
    (frame : MemoryWriteFrame initial current
      #v[TwoOutputs.outputRegion routine initial, TwoOutputs.secondOutputRegion routine initial,
        Stack.region initial routine.minStackBytes])
    {region : MemoryRegion} (read : region ∈ readRegions initial inputs)
    {address : BitVec 64} (inside : region.Contains address.toNat) :
    current.external[address]? = initial.external[address]? := by
  apply frame address
  intro writable member
  exact (call.separation.2 writable (by simpa using member)).1 region read address.toNat inside

theorem firstOutput_unchanged {routine : Routine} {initial before after : RamState}
    {inputs : Array Input} (call : TwoOutputs.ValidCall routine initial inputs)
    (frame : MemoryWriteFrame before after
      #v[TwoOutputs.secondOutputRegion routine initial,
        Stack.region initial routine.minStackBytes])
    {address : BitVec 64}
    (inside : (TwoOutputs.outputRegion routine initial).Contains address.toNat) :
    after.external[address]? = before.external[address]? := by
  apply frame address
  intro region member
  have pairs := call.separation.1
  simp only [List.pairwise_cons] at pairs
  have disjoint := pairs.1 region
  apply disjoint ?_ address.toNat inside
  simpa using member

end Sha2.Proofs.Reset
