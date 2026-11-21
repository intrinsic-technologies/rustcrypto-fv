import P256.Proofs.Program.Interface
import P256.Proofs.Program.ScalarFrame.State
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program SecretKeyFromBytes.Scalar

def Correct : Prop :=
  ∀ [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat},
    CalleePre s boundary 0x113120 32 32 104 →
    Nat256At s (s.regValue .rsi) x →
    ∃ t, CalleeResult s t boundary 32 104 ∧
      Nat256At t (s.regValue .rdi) (x % Operations.domain.n)

abbrev State [Bindings] (s t : RamState) := ScalarFrame.FrameState s t 32 104 88

end P256.Proofs.Verifying.Core.Reduce
