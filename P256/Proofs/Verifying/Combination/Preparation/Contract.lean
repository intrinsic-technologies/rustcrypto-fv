import P256.Proofs.Verifying.Combination.Preparation.SecondTable
import P256.Proofs.Verifying.Combination.Preparation.Naf.SecondSerialize

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def InlineCorrect : Prop :=
  ∀ [Bindings] (s t : RamState) (boundary : ReturnBoundary) (p q : Projective) (u v : Nat),
    Pre s boundary → InputAt s (s.regValue .rsi) p q u v → TablesOutput s t p q →
      ∃ fuel w, Advances boundary fuel t w ∧ Naf.MultiCallInput s w p q u v

end P256.Proofs.Verifying.Combination.Preparation
