import X86Proofs.Core.Gpr
import X86Proofs.Program.Compose

set_option autoImplicit false

namespace P256.Proofs.Common.Scalar.Addition.Choice

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem merge_byte_twice (a b : BitVec 8) (old : BitVec 64) :
    mergeGPR 8 a (mergeGPR 8 b old) = mergeGPR 8 a old := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [mergeGPR, show ¬ (8 : Nat) = 32 by decide, ite_false,
    getLsbD_setSlice _ _ _ _ _ hk]
  by_cases h : k < 8 <;> simp [h]

end P256.Proofs.Common.Scalar.Addition.Choice
