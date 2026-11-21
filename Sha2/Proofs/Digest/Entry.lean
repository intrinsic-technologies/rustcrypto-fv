import Sha2.Proofs.Digest.Prologue
import Sha2.Proofs.Wrapper.Prologue.Execution

set_option autoImplicit false

namespace Sha2.Proofs.Digest

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine
  X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem prologue512 [bindings : Bindings] (routine : Routine)
    (member : routine ∈ [sha384Digest, sha512Digest, sha512_224Digest, sha512_256Digest])
    {initial : RamState} {data : ByteArray}
    (machine : SupportedMachine bindings initial)
    (call : OneShot.ValidCall routine initial data) :
    ∃ s, ExecutionState initial s #v[OneShot.outputRegion routine initial, Stack.region initial 1152] ∧
      (Prologue.effect routine.entryAddress .six552 initial).Holds initial s ∧
      stackPtr s = stackPtr initial - 600 ∧ s.RIP = routine.entryAddress + (17 : BitVec 64) := by
  have budget : routine.minStackBytes = 1152 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  have stack : Stack.Valid initial 1152 := by simpa only [budget] using call.stack
  have avoid : (Stack.region initial 1152).Avoids (fun a => InProgram a ∨ InPageTables a) :=
    by
      simpa only [budget, InPageTables] using
        (call.separation.2 _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))).2
  apply Wrapper.prologue_execution
    #v[OneShot.outputRegion routine initial, Stack.region initial 1152]
    .six552 rfl 1152 machine stack (by decide) avoid (by simp) ?_
    call.programLoaded call.directionFlagUnset call.returnAddress routine.entryAddress call.entry
    (prologue512_inside routine member) (prologue512_code routine member call.programLoaded)
  intro region member a contains program
  have mem : region ∈ [OneShot.outputRegion routine initial, Stack.region initial 1152] := by
    simpa using member
  exact (call.separation.2 region (by simpa only [budget] using mem)).2 a contains (.inl program)

end Sha2.Proofs.Digest
