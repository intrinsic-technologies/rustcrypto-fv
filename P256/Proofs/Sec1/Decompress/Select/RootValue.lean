import P256.Proofs.Sec1.Decompress.Select.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Select

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem squareRoot_fields {s : RamState} {address : BitVec 64} {x : Nat}
    (result : SquareRoot.SquareRootResultAt s address x) :
    Field.MontgomeryAt s address ((P256.Spec.Operations.sqrtMod x).getD 0) ∧
      s.external[address + 32]? =
        some (if (P256.Spec.Operations.sqrtMod x).isSome then 1 else 0) := by
  unfold SquareRoot.SquareRootResultAt at result
  generalize P256.Spec.Operations.sqrtMod x = value at result ⊢
  cases value <;> exact result

end P256.Proofs.Sec1.Decompress.Select
