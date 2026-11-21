import P256.Proofs.Field.Inverse.Interface

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def NonzeroResult [Bindings] (initial final : RamState) (boundary : ReturnBoundary)
    (a : Nat) : Prop :=
  CalleeResult initial final boundary 40 704 ∧
    ∃ b, Nat256At final (initial.regValue .rdi) b ∧
      b < P256.Spec.Operations.domain.p ∧
      b * a % P256.Spec.Operations.domain.p = 2^512 % P256.Spec.Operations.domain.p ∧
      final.external[(initial.regValue .rdi) + 32]? = some 1

def ZeroResult [Bindings] (initial final : RamState) (boundary : ReturnBoundary) : Prop :=
  CalleeResult initial final boundary 40 704 ∧
    final.external[(initial.regValue .rdi) + 32]? = some 0

end P256.Proofs.Field.Inverse.SafeGcd.Core
