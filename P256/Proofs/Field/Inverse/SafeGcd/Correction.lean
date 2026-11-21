import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Value

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem correction_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {a m : Nat}
    (pre : Pre s boundary) (ha : Nat256At s (s.regValue .rsi) a)
    (hm : Nat256At s (s.regValue .rcx) m) (bound : a < m) :
    ∃ t, CalleeResult s t boundary 32 56 ∧
      Nat256At t (s.regValue .rdi)
        (if a = 0 ∨ ((s.regValue .rdx).setWidth 8 ^^^
          memLoad s.external (s.regValue .rsi + 32) 8) &&& 1 = 0 then a else m-a) := by
  obtain ⟨t, result, value⟩ := execution_correct pre
  rw [inputs_value ha hm bound] at value
  exact ⟨t, result, value⟩

end P256.Proofs.Field.Inverse.SafeGcd.Correction
