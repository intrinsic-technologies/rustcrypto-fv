import P256.Proofs.Program.Interface
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

abbrev Pre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop :=
  CalleePre s boundary 0x112ed0 32 33 72

def Contract (bindings : Bindings) : Prop :=
  ∀ (s : RamState) (boundary : ReturnBoundary) (bytes : ByteArray),
    Pre s boundary → (registerRegion s .rsi 32).HasBytes s.external bytes →
    ∃ t, CalleeResult s t boundary 33 72 ∧
      SecretKeyFromBytes.Scalar.Nat256At t (s.regValue .rdi) (Arith.uint bytes) ∧
      t.external[s.regValue .rdi + 32]? =
        some (if Arith.uint bytes < Operations.domain.n then 1 else 0) ∧
      t.regValue .rax = s.regValue .rdi

end P256.Proofs.Generate.Scalar
