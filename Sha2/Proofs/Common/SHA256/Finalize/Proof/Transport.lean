import Sha2.Proofs.Common.Machine.ExecutionState
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem call_result_frame [Bindings] {s u t : RamState} {boundary : ReturnBoundary}
    {n outputBytes reserve : Nat} {regions : Vector MemoryRegion n}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (effect : (callEffect target ret s).Holds s u)
    (callWrites : WritesWithin (callEffect target ret s).components regions)
    (result : CalleeResult u t boundary outputBytes reserve)
    (within : ∀ region ∈ #v[registerRegion u .rdi outputBytes, Stack.region u reserve],
      ∀ a, region.Contains a → ∃ outer ∈ regions, outer.Contains a) :
    MemoryWriteFrame s t regions := by
  apply memoryWriteFrame_trans (effect.agrees.memoryWriteFrame callWrites)
  intro address outside
  apply result.frame address
  intro region member contains
  obtain ⟨outer, ho, ha⟩ := within region member address.toNat contains
  exact outside outer ho ha

theorem ExecutionState.of_run_call_result [Bindings] {initial s u t : RamState}
    {n outputBytes reserve fuel : Nat} {regions : Vector MemoryRegion n}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (state : ExecutionState initial s regions)
    (run : Advances (returnBoundary initial) fuel s t)
    (effect : (callEffect target ret s).Holds s u)
    (callWrites : WritesWithin (callEffect target ret s).components regions)
    (result : CalleeResult u t (returnBoundary initial) outputBytes reserve)
    (within : ∀ region ∈ #v[registerRegion u .rdi outputBytes, Stack.region u reserve],
      ∀ a, region.Contains a → ∃ outer ∈ regions, outer.Contains a) :
    ExecutionState initial t regions := by
  obtain ⟨priorFuel, prior⟩ := state.execution
  refine ⟨⟨priorFuel + fuel, prior.trans run⟩,
    result.machine, result.loaded, ?_, result.abi.2.1,
    memoryWriteFrame_trans state.frame (call_result_frame effect callWrites result within)⟩
  intro a allocated
  exact result.allocated a (effect.agrees.grow a (state.allocated a allocated))

theorem ExecutionState.of_call_result [Bindings] {initial s u t : RamState}
    {n outputBytes reserve fuel : Nat} {regions : Vector MemoryRegion n}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (state : ExecutionState initial s regions)
    (run : Advances (returnBoundary initial) fuel s u)
    (effect : (callEffect target ret s).Holds s u)
    (callWrites : WritesWithin (callEffect target ret s).components regions)
    (result : CalleeResult u t (returnBoundary initial) outputBytes reserve)
    (within : ∀ region ∈ #v[registerRegion u .rdi outputBytes, Stack.region u reserve],
      ∀ a, region.Contains a → ∃ outer ∈ regions, outer.Contains a) :
    ExecutionState initial t regions := by
  obtain ⟨calleeFuel, callee⟩ := result.execution
  exact state.of_run_call_result (run.trans callee) effect callWrites result within

end Sha2.Proofs.Common.Machine
