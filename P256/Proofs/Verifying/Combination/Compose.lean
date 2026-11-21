import P256.Proofs.Verifying.Combination.Preparation.Contract
import P256.Proofs.Verifying.Combination.Output

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct_of_contracts (table : Table.Correct) (inline : Preparation.InlineCorrect)
    (multi : Loop.MultiCorrect) : Correct := by
  intro _ s boundary p q u v pre input hp hq
  obtain ⟨n, a, runA, stateA⟩ := Preparation.prepare_tables_of_correct table pre input
  obtain ⟨m, b, runB, stateB⟩ := inline s a boundary p q u v pre input stateA
  obtain ⟨k, t, result, runT, stateT, ripT, valueT, sum⟩ :=
    Output.transfer multi pre stateB input.2.1.1 input.2.2.2.1 hp hq
  obtain ⟨w, returned, valueW⟩ := finish pre stateT ripT valueT
    ⟨n+m+k, (runA.trans runB).trans runT⟩
  exact ⟨w, result, returned, valueW, sum⟩

end P256.Proofs.Verifying.Combination
