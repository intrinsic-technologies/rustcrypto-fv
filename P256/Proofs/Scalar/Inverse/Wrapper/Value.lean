import P256.Proofs.Scalar.Inverse.Wrapper.Input
import P256.Proofs.Field.Inverse.SafeGcd.Core.Input
import P256.Proofs.Scalar.Inverse.Arithmetic
import P256.Proofs.Scalar.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Scalar.Inverse.Wrapper

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Arithmetic
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar

set_option exponentiation.threshold 512 in
theorem inputs_conditions {s : RamState} {a : Nat}
    (ha : Nat256At s (s.regValue .rsi) a) (bound : a < P256.Spec.Operations.domain.n) :
    Conditions (scalarInput (inputs s)) ∧
      Shared.Arithmetic.modulus (scalarInput (inputs s)) = P256.Spec.Operations.domain.n ∧
      Shared.Arithmetic.argument (scalarInput (inputs s)) = a ∧
      Shared.Arithmetic.scale (scalarInput (inputs s)) = 1 := by
  have hm : Shared.Arithmetic.modulus (scalarInput (inputs s)) = P256.Spec.Operations.domain.n := by
    dsimp only [Shared.Arithmetic.modulus, scalarInput]
    decide +kernel
  have ha' : Shared.Arithmetic.argument (scalarInput (inputs s)) = a := Input.readWords_value ha
  have hs : Shared.Arithmetic.scale (scalarInput (inputs s)) = 1 := by
    dsimp only [Shared.Arithmetic.scale, scalarInput]
    decide +kernel
  refine ⟨?_, hm, ha', hs⟩
  constructor
  · rw [hm]; decide +kernel
  · rw [hm]; decide +kernel
  · rw [hm]; decide +kernel
  · rw [hm]
    change ((P256.Spec.Operations.domain.n : Int) * 0x332e375511ff43b1) % (2 : Int)^64 = 1
    decide +kernel
  · rw [hm, ha']; exact bound
  · rw [hm, hs]; decide +kernel

theorem result_value {s : RamState} {a : Nat}
    (ha : Nat256At s (s.regValue .rsi) a)
    (positive : 0 < a) (bound : a < P256.Spec.Operations.domain.n) :
    (Correction.limbs (resultWords (inputs s))).toNat =
      Standards.SECG.ECC.Curve.inverse P256.Spec.Operations.domain.n a ∧
      resultChoice (inputs s) = 1 := by
  obtain ⟨conditions, modulus, argument, scale⟩ := inputs_conditions ha bound
  have hp := result_product (scalarInput (inputs s)) conditions modulus
    (by rw [argument]; exact positive)
  have hc := resultChoice_one (scalarInput (inputs s)) conditions modulus
    (by rw [argument]; exact positive)
  rw [Support.packed_limbs, modulus, argument, scale] at hp
  exact ⟨inverse_unique positive bound hp.1 hp.2, hc⟩

theorem result_zero {s : RamState} (ha : Nat256At s (s.regValue .rsi) 0) :
    resultChoice (inputs s) = 0 :=
  Arithmetic.resultChoice_zero (scalarInput (inputs s)) (Input.readWords_value ha)

end P256.Proofs.Scalar.Inverse.Wrapper
