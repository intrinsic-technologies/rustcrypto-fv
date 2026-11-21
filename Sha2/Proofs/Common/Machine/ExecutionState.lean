import Sha2.Proofs.Common.Machine.CallReturn
import Sha2.Proofs.Common.Machine.Interfaces

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86Proofs

structure ExecutionState [bindings : Bindings] (initial s : RamState) {n : Nat}
    (regions : Vector MemoryRegion n) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  machine : SupportedMachine bindings s
  loaded : ProgramLoaded s
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome
  directionFlag : DirectionFlagUnset s
  frame : MemoryWriteFrame initial s regions

theorem ExecutionState.of_agrees [Bindings] {initial s t : RamState} {n : Nat}
    {regions : Vector MemoryRegion n} {components : List Component} {fuel : Nat}
    (state : ExecutionState initial s regions)
    (avoids : ∀ region ∈ regions, region.Avoids InProgram)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t) (writes : WritesWithin components regions)
    (hdf : .df ∉ components) : ExecutionState initial t regions := by
  have memory := agrees.memoryWriteFrame writes
  obtain ⟨steps, execution⟩ := state.execution
  refine ⟨⟨steps + fuel, execution.trans run⟩,
    supportedMachine_of_ready_agrees state.machine ready agrees, ?_,
    fun a ha => agrees.grow a (state.allocated a ha),
    agrees.directionFlagClear hdf state.directionFlag,
    memoryWriteFrame_trans state.frame memory⟩
  intro address byte fetch
  rw [memory address]
  · exact state.loaded address byte fetch
  · intro region hr ha
    exact avoids region hr address ha ⟨byte, fetch⟩

theorem ExecutionState.of_callee [Bindings] {initial s t : RamState} {n : Nat}
    {regions : Vector MemoryRegion n} {outputBytes reserve : Nat}
    (state : ExecutionState initial s regions)
    (result : CalleeResult s t (returnBoundary initial) outputBytes reserve)
    (within : ∀ region ∈ #v[registerRegion s .rdi outputBytes, Stack.region s reserve],
      ∀ a, region.Contains a → ∃ outer ∈ regions, outer.Contains a) :
    ExecutionState initial t regions := by
  obtain ⟨before, first⟩ := state.execution
  obtain ⟨after, second⟩ := result.execution
  refine ⟨⟨before + after, first.trans second⟩, result.machine, result.loaded,
    fun a ha => result.allocated a (state.allocated a ha), result.abi.2.1, ?_⟩
  apply memoryWriteFrame_trans state.frame
  intro address outside
  apply result.frame address
  intro region hr ha
  obtain ⟨outer, ho, contains⟩ := within region hr address.toNat ha
  exact outside outer ho contains

end Sha2.Proofs.Common.Machine
