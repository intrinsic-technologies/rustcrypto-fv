import Sha2.Proofs.Common.Machine.StackRegion
import Sha2.Proofs.Common.Machine.ExecutionState
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem loaded_after_call [Bindings] {initial s u : RamState}
    {n outerReserve frameOffset : Nat} {regions : Vector MemoryRegion n}
    {entry ret : BitVec 64}
    (stack : Stack.Valid initial outerReserve)
    (avoids : (Stack.region initial outerReserve).Avoids
      (fun a => InProgram a ∨ InPageTables a))
    (state : ExecutionState initial s regions)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 frameOffset)
    (capacity : frameOffset + 8 ≤ outerReserve)
    (effect : (callEffect (fun _ => entry) ret s).Holds s u) : ProgramLoaded u := by
  have slot : pushAddr s = stackPtr initial - BitVec.ofNat 64 (frameOffset + 8) := by
    rw [pushAddr, rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have frame : MemoryWriteFrame s u #v[Stack.region initial outerReserve] := by
    apply effect.agrees.memoryWriteFrame
    intro c member a covered
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact covered.elim
    · refine ⟨Stack.region initial outerReserve, by simp, ?_⟩
      rw [slot] at covered
      exact stackRegion_contains_sub stack.2.2.1 (by omega) (by omega) covered
    · exact covered.elim
  have loaded : ProgramLoaded u := by
    intro a b fetch
    rw [frame a]
    · exact state.loaded a b fetch
    · intro region member contains
      have same : region = Stack.region initial outerReserve := by simpa using member
      subst region
      exact avoids a contains (.inl ⟨b, fetch⟩)
  exact loaded

end Sha2.Proofs.Common.Machine
