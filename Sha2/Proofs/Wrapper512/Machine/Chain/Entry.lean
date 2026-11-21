import Sha2.Proofs.Wrapper512.Dispatch.Initialize
import Sha2.Proofs.Common.Encoding.Serialize.Prologue

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Machine.Chain

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess
  X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Encoding.Serialize
open Sha2.Proofs.Wrapper512
open Sha2.Proofs.Wrapper512.Dispatch

structure Pushed [bindings : Bindings] (v : Variant) (initial s : RamState) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  machine : SupportedMachine bindings s
  loaded : ProgramLoaded s
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome
  saved : SavedStackAt initial s
  directionFlag : DirectionFlagUnset s
  frame : MemoryWriteFrame initial s
    #v[outputRegion v.routine initial, Stack.region initial v.routine.minStackBytes]
  rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 48
  agrees : AgreesExcept (saveFrame initial) initial s

 theorem pushed [bindings : Bindings] {v : Variant} {initial : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs) :
    ∃ s, Pushed v initial s ∧ s.RIP = v.pc 0xa := by
  obtain ⟨s, execution, ready, loaded, rip, rsp, memory, agrees⟩ :=
    save_registers512 ctx
  have machine : SupportedMachine bindings s :=
    supportedMachine_of_ready_agrees ctx.machine ready agrees
  have allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome →
      (s.external[a]?).isSome := agrees.grow
  have saved : SavedStackAt initial s := by
    constructor
    · intro slot hs
      rw [memory]
      exact saveMemory_saved initial slot hs
    · rw [memory]
      simp only [saveMemory, BitVec.sub_eq_add_neg]
      repeat rw [memLoad_memStore_apart_right _ (stackPtr initial) _ _ 64
        (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
  have directionFlag : DirectionFlagUnset s :=
    agrees.directionFlagClear (by simp [saveFrame]) ctx.call.directionFlagUnset
  have frame : MemoryWriteFrame initial s
      #v[outputRegion v.routine initial, Stack.region initial v.routine.minStackBytes] := by
    apply agrees.memoryWriteFrame
    intro c hc a ha
    simp only [saveFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨Stack.region initial v.routine.minStackBytes, by simp,
      stackRegion_contains_sub ctx.call.stack.2.2.1 (by
        simp only [Variant.routine, Form.stackBytes]
        omega) (by decide) ha⟩
  exact ⟨s, ⟨⟨6, execution⟩, machine, loaded, allocated, saved,
    directionFlag, frame, rsp, agrees⟩, rip⟩

end Sha2.Proofs.Wrapper512.Machine.Chain
