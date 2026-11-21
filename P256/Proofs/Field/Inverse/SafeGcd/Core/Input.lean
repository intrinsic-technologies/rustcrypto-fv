import P256.Proofs.Field.Inverse.SafeGcd.Core.Input.Memory
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Input

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar P256.Proofs.Field.Schoolbook
open Shared.Arithmetic

theorem readWords_value {s : RamState} {address : BitVec 64} {n : Nat}
    (h : Nat256At s address n) : packFour ((readWords s address).map BitVec.toNat) = n := by
  rw [Support.packed_limbs]
  exact readLimbs_toNat h

set_option exponentiation.threshold 512 in
theorem inputs_conditions [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : SafeGcdPre s boundary) {a : Nat} (ha : Nat256At s (s.regValue .rsi) a)
    (bound : a < P256.Spec.Operations.domain.p) :
    Conditions (inputs s) ∧ modulus (inputs s) = P256.Spec.Operations.domain.p ∧
      argument (inputs s) = a ∧ scale (inputs s) = 2^512 % P256.Spec.Operations.domain.p := by
  have hm : modulus (inputs s) = P256.Spec.Operations.domain.p := readWords_value pre.modulus
  have ha' : argument (inputs s) = a := readWords_value ha
  have hs : scale (inputs s) = 2^512 % P256.Spec.Operations.domain.p := readWords_value pre.adjuster
  refine ⟨?_, hm, ha', hs⟩
  constructor
  · rw [hm]; decide +kernel
  · rw [hm]; decide +kernel
  · rw [hm]; decide +kernel
  · rw [hm]; change ((_ : Int) * (s.regValue .rcx).toNat) % (2 : Int)^64 = 1
    rw [pre.inverse]; decide +kernel
  · rw [hm, ha']; exact bound
  · rw [hm, hs]; exact Nat.mod_lt _ (by decide +kernel)

end P256.Proofs.Field.Inverse.SafeGcd.Core.Input
