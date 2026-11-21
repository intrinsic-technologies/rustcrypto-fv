import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Raw
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem dynamic_mul_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : MontgomeryPre s boundary)
    (left : Field.MontgomeryAt s (s.regValue .rsi) x)
    (right : Field.MontgomeryAt s (s.regValue .rdx) y) :
    ∃ t, CalleeResult s t boundary 32 160 ∧
      Field.MontgomeryAt t (s.regValue .rdi) (x * y % P256.Spec.Operations.domain.p) := by
  have bound : (x * 2^256 % P256.Spec.Operations.domain.p) *
      (y * 2^256 % P256.Spec.Operations.domain.p) < P256.Spec.Operations.domain.p * 2^256 :=
    Nat.mul_lt_mul_of_lt_of_lt (Nat.mod_lt _ Field.Montgomery.p_pos)
      (Nat.lt_trans (Nat.mod_lt _ Field.Montgomery.p_pos) Field.Montgomery.p_lt_radix)
  obtain ⟨t, result, output⟩ := raw_mul_correct (Or.inl rfl) pre left.2 right.2 bound
  exact ⟨t, result, Field.montgomeryAt_product output⟩

end P256.Proofs.Sec1.SquareRoot
