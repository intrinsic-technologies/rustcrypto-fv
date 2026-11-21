import Hkdf.Proofs.Standard.Update.Entry
import Hkdf.Proofs.Standard.Update.Short
import Hkdf.Proofs.Standard.Update.Long
import Hkdf.Proofs.Standard.Update.Finish

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Update

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem absorb_one [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} {index : Nat} (ctx : Context initial salt inputs)
    (state : LoopState initial s salt inputs index) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      ((index + 1 = inputs.size ∧ Completed initial t salt inputs) ∨
        LoopState initial t salt inputs (index + 1)) := by
  obtain ⟨short, prepareFuel, u, prepareRun, readyU, prepared⟩ := prepare_input ctx state
  have consumed : ∃ fuel v, Advances (returnBoundary initial) fuel u v ∧ ReadyToStep v ∧
      InputDone initial v salt inputs index short := by
    cases short
    · exact long_input ctx readyU prepared
    · exact Short.short_input ctx readyU prepared
  obtain ⟨inputFuel, v, inputRun, readyV, done⟩ := consumed
  obtain ⟨finishFuel, t, finishRun, readyT, outcome⟩ := finish_input ctx readyV done
  exact ⟨prepareFuel + inputFuel + finishFuel, t,
    (prepareRun.trans inputRun).trans finishRun, readyT, outcome⟩

theorem absorb_all [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} {index : Nat} (ctx : Context initial salt inputs)
    (state : LoopState initial s salt inputs index) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      Completed initial t salt inputs := by
  generalize remainingEq : inputs.size - index = remaining
  induction remaining generalizing s index with
  | zero => have := state.remaining; omega
  | succ remaining ih =>
    obtain ⟨fuel, u, run, readyU, done | more⟩ := absorb_one ctx state
    · exact ⟨fuel, u, run, readyU, done.2⟩
    · obtain ⟨tailFuel, t, tailRun, readyT, completed⟩ :=
        ih more (by have := state.remaining; omega)
      exact ⟨fuel + tailFuel, t, run.trans tailRun, readyT, completed⟩

theorem from_initialized [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} (ctx : Context initial salt inputs) (ready : ReadyToStep s)
    (initialized : Initialized initial s salt) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      Completed initial t salt inputs := by
  obtain ⟨fuel, u, run, readyU, done | more⟩ := start ctx ready initialized
  · exact ⟨fuel, u, run, readyU, done.2⟩
  · obtain ⟨tailFuel, t, tailRun, readyT, completed⟩ := absorb_all ctx more
    exact ⟨fuel + tailFuel, t, run.trans tailRun, readyT, completed⟩

end Hkdf.Proofs.Standard.Update
