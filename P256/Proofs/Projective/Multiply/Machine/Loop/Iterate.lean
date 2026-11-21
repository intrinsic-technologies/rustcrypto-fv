import P256.Proofs.Projective.Multiply.Machine.Loop.Round.State

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem iterate_rounds [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective}
    (step : ∀ {u : RamState} {n : Nat}, Round.LoopState s u table n → n < 64 →
      ∃ fuel v, Advances boundary fuel u v ∧ Round.LoopState s v table (n+1))
    (initial : Round.LoopState s t table 0) {n : Nat} (bound : n ≤ 64) :
    ∃ fuel u, Advances boundary fuel t u ∧ Round.LoopState s u table n := by
  induction n with
  | zero => exact ⟨0, t, rfl, initial⟩
  | succ n ih =>
    obtain ⟨a, u, runU, stateU⟩ := ih (by omega)
    obtain ⟨b, v, runV, stateV⟩ := step stateU (by omega)
    exact ⟨a+b, v, runU.trans runV, stateV⟩

end P256.Proofs.Projective.Multiply.Machine.Loop
