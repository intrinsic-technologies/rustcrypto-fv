import P256.Proofs.Sec1.Decompress.Convert.Arithmetic
import P256.Proofs.Sec1.Decompress.Convert.Precondition
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Raw

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Convert

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option exponentiation.threshold 512 in
theorem convert_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : Pre s boundary) (input : Nat256At s (s.regValue .rsi) x) :
    ∃ t, CalleeResult s t boundary 32 160 ∧
      Field.MontgomeryAt t (s.regValue .rdi) (x % P256.Spec.Operations.domain.p) := by
  have right : Nat256At s (s.regValue .rdx) (2^512 % P256.Spec.Operations.domain.p) := by
    rw [pre.right]
    exact radixSquared_at pre.loaded
  obtain ⟨t, result, output⟩ := SquareRoot.raw_mul_correct (.inr rfl) pre.montgomery
    input right (raw_product_bound input.1)
  exact ⟨t, result, convert_representation input.1 output⟩

end P256.Proofs.Sec1.Decompress.Convert
