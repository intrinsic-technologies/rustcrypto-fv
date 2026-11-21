import P256.Proofs.Sec1.Interface
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.PublicPoint

open P256.Spec Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

def Contract (bindings : Bindings) : Prop :=
  ∀ (s : RamState) (boundary : ReturnBoundary) (d : Nat),
    CalleePre s boundary 0x10e6f0 32 65 3352 →
    SecretKeyFromBytes.Scalar.Nat256At s (s.regValue .rsi) d →
    ∃ t, CalleeResult s t boundary 65 3352 ∧
      Sec1.AffineAt t (s.regValue .rdi) (Points.mul d Operations.domain.G)

end P256.Proofs.PublicPoint
