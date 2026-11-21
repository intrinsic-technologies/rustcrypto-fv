import P256.Proofs.Scalar.Inverse.Interface
import P256.Proofs.Field.Inverse.SafeGcd.Core.Input

set_option autoImplicit false

namespace P256.Proofs.Scalar.Inverse

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Field.Inverse.SafeGcd.Core
open P256.Proofs.Field.Inverse.SafeGcd.Core.Input
open Shared.Arithmetic

set_option exponentiation.threshold 512 in
theorem inputs_conditions [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : SafeGcdPre s boundary) {a : Nat} (ha : Nat256At s (s.regValue .rsi) a)
    (bound : a < P256.Spec.Operations.domain.n) :
    Conditions (inputs s) ∧ modulus (inputs s) = P256.Spec.Operations.domain.n ∧
      argument (inputs s) = a ∧ scale (inputs s) = 1 := by
  have hm : modulus (inputs s) = P256.Spec.Operations.domain.n := readWords_value pre.modulus
  have ha' : argument (inputs s) = a := readWords_value ha
  have hs : scale (inputs s) = 1 := readWords_value pre.adjuster
  refine ⟨?_, hm, ha', hs⟩
  constructor
  · rw [hm]; decide +kernel
  · rw [hm]; decide +kernel
  · rw [hm]; decide +kernel
  · rw [hm]; change ((_ : Int) * (s.regValue .rcx).toNat) % (2 : Int)^64 = 1
    rw [pre.inverse]; decide +kernel
  · rw [hm, ha']; exact bound
  · rw [hm, hs]; decide +kernel

end P256.Proofs.Scalar.Inverse
