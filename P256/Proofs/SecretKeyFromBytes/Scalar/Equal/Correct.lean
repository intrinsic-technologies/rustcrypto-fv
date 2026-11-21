import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Prefix
import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Finish

set_option autoImplicit false

namespace P256.Proofs.SecretKeyFromBytes.Scalar.Equal

open X86 X86.Machine X86.UserProcess

theorem equal_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ t, Result s t boundary ∧
      (t.regValue .rax).setWidth 8 = if prefixEqual s 4 then 1 else 0 := by
  obtain ⟨t, ht⟩ := start_correct pre
  obtain ⟨u, hu⟩ := loop_four pre ht
  exact finish pre hu.toStage (by simpa using hu.rip) hu.accumulator

end P256.Proofs.SecretKeyFromBytes.Scalar.Equal
