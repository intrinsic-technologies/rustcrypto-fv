import Sha2.Proofs.Wrapper.Prologue.Execution

set_option autoImplicit false

namespace Sha2.Proofs.Reset

open Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

def regions (routine : Routine) (initial : RamState) : Vector MemoryRegion 3 :=
  #v[TwoOutputs.outputRegion routine initial, TwoOutputs.secondOutputRegion routine initial,
    Stack.region initial routine.minStackBytes]

theorem prologue [bindings : Bindings] {routine : Routine} {initial : RamState}
    {inputs : Array Input} (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (layout : Prologue.Layout) (six : layout.six = true)
    (capacity : 48 ≤ routine.minStackBytes)
    (inside : BlockInProgram routine.entryAddress layout.length)
    (code : CodeIn (codeRange routine.entryAddress (Prologue.bytes layout)) initial) :
    ∃ s, ExecutionState initial s (regions routine initial) ∧
      (Prologue.effect routine.entryAddress layout initial).Holds initial s ∧
      stackPtr s = stackPtr initial - BitVec.ofNat 64 (layout.allocation + 48) ∧
      s.RIP = routine.entryAddress + BitVec.ofNat 64 layout.length := by
  apply Sha2.Proofs.Wrapper.prologue_execution (regions routine initial) layout six
    routine.minStackBytes machine call.stack capacity
  · exact (call.separation.2 _ (by simp)).2
  · simp [regions]
  · intro region member address contains inProgram
    have listed : region ∈ [TwoOutputs.outputRegion routine initial,
        TwoOutputs.secondOutputRegion routine initial,
        Stack.region initial routine.minStackBytes] := by
      simpa [regions] using member
    exact (call.separation.2 region listed).2 address contains (Or.inl inProgram)
  · exact call.programLoaded
  · exact call.directionFlagUnset
  · exact call.returnAddress
  · exact call.entry
  · exact inside
  · exact code

end Sha2.Proofs.Reset
