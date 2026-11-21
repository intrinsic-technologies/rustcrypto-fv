import Sha2.Proofs.Wrapper512.Dispatch.Contract

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Wrapper512

structure Step [Bindings] (v : Variant) (initial : RamState) (inputs : Array Input) (form : Form := .slices) : Prop where
  run : ∀ {index : Nat} {state : RamState},
    LoopState v initial state inputs index form →
    ∃ t, (LoopState v initial t inputs (index + 1) form ∨
      (Buffered v initial t (message inputs) form ∧
        t.RIP = v.pc (v.dispatchOffset form) form ∧
        v.countValue form initial t = BitVec.ofNat 64 inputs.size ∧
        (form = .traitFinalizeIntoReset false →
          memLoad t.external (outputSavePointer initial form) 64 = initial.regValue .rcx))) ∧
      (∃ fuel, Advances (returnBoundary initial) fuel state t) ∧
      MemoryWriteFrame state t #v[Stack.region initial (v.routine form).minStackBytes]

theorem all [Bindings] {v : Variant} {initial : RamState} {inputs : Array Input}
    {form : Form} (_ctx : Context v initial inputs form) (step : Step v initial inputs form)
    {index : Nat} {s : RamState} (state : LoopState v initial s inputs index form) :
    ∃ t, Buffered v initial t (message inputs) form ∧
      t.RIP = v.pc (v.dispatchOffset form) form ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] ∧
      v.countValue form initial t = BitVec.ofNat 64 inputs.size ∧
      (form = .traitFinalizeIntoReset false →
        memLoad t.external (outputSavePointer initial form) 64 = initial.regValue .rcx) := by
  generalize remainingEq : inputs.size - index = remaining
  induction remaining generalizing s index with
  | zero =>
      have h := state.remaining
      omega
  | succ remaining ih =>
      obtain ⟨t, result, ⟨fuel, run⟩, frame⟩ := step.run state
      rcases result with nextState | done
      · obtain ⟨u, buffered, rip, ⟨fuelU, runU⟩, frameU, countU, savedU⟩ := ih nextState (by omega)
        exact ⟨u, buffered, rip, ⟨fuel + fuelU, run.trans runU⟩, fun a outside => (frameU a outside).trans (frame a outside), countU, savedU⟩
      · exact ⟨t, done.1, done.2.1, ⟨fuel, run⟩, frame, done.2.2.1, done.2.2.2⟩

theorem contract_of_step [bindings : Bindings] {v : Variant}
    (initializer : ∀ {initial : RamState} {inputs : Array Input},
      Context v initial inputs →
        ∃ s, Buffered v initial s ByteArray.empty ∧
          s.RIP = v.pc 0xd0 ∧ s.regValue .rsi = BitVec.ofNat 64 inputs.size)
    (step : ∀ {initial : RamState} {inputs : Array Input},
      Context v initial inputs → Step v initial inputs) :
    DispatchContract v := by
  apply Dispatch.contract_of_parts initializer
  intro initial inputs ctx s state
  obtain ⟨t, buffered, rip, _, _, _, _⟩ := all ctx (step ctx) state
  exact ⟨t, buffered, rip⟩

end Sha2.Proofs.Wrapper512.Absorb
