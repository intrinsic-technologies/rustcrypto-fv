import P256.Proofs.Projective.Multiply.Machine.Loop.Round.Prepare
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.Lookup
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.Add
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.Finish

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem round_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective} {n : Nat} (pre : Pre s boundary)
    (input : Lookup.TableAt s (s.regValue .rsi) table)
    (state : LoopState s t table n) (bound : n < 64) :
    ∃ fuel u, Advances boundary fuel t u ∧ LoopState s u table (n+1) := by
  obtain ⟨a, v, runV, stateV, ax⟩ := prepare_round pre state bound
  obtain ⟨b, w, runW, stateW⟩ := prepare_copy pre stateV ax
  obtain ⟨c, x, runX, stateX, selected⟩ := lookup_round pre input stateW
  obtain ⟨d, y, runY, stateY, axY⟩ := add_round pre stateX selected
  obtain ⟨e, u, runU, stateU⟩ := finish_round pre stateY axY
  exact ⟨a+b+c+d+e, u, (((runV.trans runW).trans runX).trans runY).trans runU, stateU⟩

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
