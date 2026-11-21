import Sha3.Proofs.Wrapper.Output
import Sha3.Proofs.Update.Layout

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def outputAddress (initial : RamState) (mode : Mode) : BitVec 64 :=
  match mode with
  | .plain | .reset => initial.regValue .rcx
  | .digest => initial.regValue .rdx
  | _ => initial.regValue .r9

theorem outputRegion_eq (initial : RamState) (v : Variant) (mode : Mode) (keccak : Bool := false) (fullState : Bool := false) :
    mode.output (mode.entry v keccak fullState) initial =
      ⟨(outputAddress initial mode).toNat, (v.digestBytes fullState)⟩ := by
  have h := Mode.entry_digestBytes mode v keccak fullState
  cases mode <;> simp only [Mode.output, outputRegion, digestOutputRegion,
    secondOutputRegion, registerRegion, outputAddress] <;> rw [h]

theorem output_mem_writeRegions (initial : RamState) (v : Variant) (mode : Mode) (keccak : Bool := false) (fullState : Bool := false) :
    mode.output (mode.entry v keccak fullState) initial ∈ writeRegions initial v mode keccak fullState := by
  cases mode with
  | plain | reset | digest => exact Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩
  | _ => exact Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩

theorem output_stack_disjoint {bindings : Bindings} {initial : RamState} {v : Variant}
    {mode : Mode} {inputs : Array Input} {split : Nat} {keccak fullState : Bool}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    (mode.output (mode.entry v keccak fullState) initial).Disjoint
      (Stack.region initial (mode.entry v keccak fullState).minStackBytes) := by
  cases mode with
  | plain | reset | digest => exact hCall.separation.1 ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
  | _ => exact hCall.separation.1 ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)

theorem before_after_disjoint {bindings : Bindings} {initial : RamState} {v : Variant}
    {mode : Mode} {inputs : Array Input} {split : Nat} {keccak fullState : Bool}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hm : mode.hasBeforeOutput = true) :
    (outputRegion (mode.entry v keccak fullState) initial).Disjoint
      (mode.output (mode.entry v keccak fullState) initial) := by
  cases mode <;> try cases hm
  all_goals exact hCall.separation.1 ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)

theorem before_stack_disjoint {bindings : Bindings} {initial : RamState} {v : Variant}
    {mode : Mode} {inputs : Array Input} {split : Nat} {keccak fullState : Bool}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hm : mode.hasBeforeOutput = true) :
    (outputRegion (mode.entry v keccak fullState) initial).Disjoint
      (Stack.region initial (mode.entry v keccak fullState).minStackBytes) := by
  cases mode <;> try cases hm
  all_goals exact hCall.separation.1 ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)

theorem ValidInvocation.beforeOutputWritable {bindings : Bindings} {initial : RamState}
    {v : Variant} {mode : Mode} {inputs : Array Input} {split : Nat} {keccak fullState : Bool}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hm : mode.hasBeforeOutput = true) :
    ValidOutput initial (outputRegion (mode.entry v keccak fullState) initial) := by
  cases mode <;> try cases hm
  all_goals exact hCall.call.outputInMemory

theorem output_of_canonical_at_address {v : Variant} {mode : Mode}
    {initial final : RamState} {inputs : Array Input} {split : Nat} {keccak fullState : Bool}
    (hbytes : ∀ i : Fin (v.digestBytes fullState),
      final.external[outputAddress initial mode + BitVec.ofNat 64 i.val]? =
        some (Finalize.digest v (Incremental.canonicalState Keccak.keccakLanes v.rate
          (message (afterInputs mode inputs split))) keccak fullState)[i]) :
    readBytes (mode.output (mode.entry v keccak fullState) initial) (mode.entry v keccak fullState).outputBytes final = .ok (expectedDigest v mode inputs split keccak fullState) := by
  apply output_of_canonical
  intro i
  simpa only [outputRegion_eq initial v mode keccak fullState, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hbytes i

theorem beforeOutput_of_canonical_at_address {v : Variant} {mode : Mode} {initial final : RamState}
    {inputs : Array Input} {split : Nat} {keccak fullState : Bool}
    (hbytes : ∀ i : Fin (v.digestBytes fullState),
      final.external[initial.regValue .rcx + BitVec.ofNat 64 i.val]? =
        some (Finalize.digest v (Incremental.canonicalState Keccak.keccakLanes v.rate
          (message (inputs.extract 0 split))) keccak fullState)[i]) :
    readOutput (mode.entry v keccak fullState) initial final =
      .ok (expectedBeforeDigest v inputs split mode keccak fullState) := by
  apply beforeOutput_of_canonical
  intro i
  simpa only [outputRegion, registerRegion, BitVec.ofNat_add,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] using hbytes i

theorem metadata_of_stateAt {pointer : BitVec 64} {state : Incremental.State} {s : RamState}
    (h : Update.StateAt pointer state s) :
    (Operand.mem (pointer + 200) : Operand 8).read s = BitVec.ofNat 8 state.cursor := by
  rw [← h.cursor]
  simp only [Update.cursor, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Sha3.Proofs.Wrapper
