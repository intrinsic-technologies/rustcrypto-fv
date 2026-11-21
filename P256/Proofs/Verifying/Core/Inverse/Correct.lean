import P256.Proofs.Verifying.Core.Inverse.Contract
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.CoreCall

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Inverse

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem nonzero_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {a : Nat}
    (pre : CalleePre s boundary 0x112fd0 32 40 768)
    (ha : Nat256At s (s.regValue .rsi) a)
    (positive : 0 < a) (bound : a < P256.Spec.Operations.domain.n) :
    ∃ t, CalleeResult s t boundary 40 768 ∧
      Nat256At t (s.regValue .rdi)
        (Standards.SECG.ECC.Curve.inverse P256.Spec.Operations.domain.n a) ∧
      t.external[s.regValue .rdi + 32]? = some 1 :=
  nonzero_correct_of_core SafeGcd.core_stage pre ha positive bound

end P256.Proofs.Verifying.Core.Inverse
