import P256.Proofs.Verifying.Core.Inverse.Input
import P256.Proofs.Field.Inverse.SafeGcd.Core.Input
import P256.Proofs.Verifying.Core.Inverse.Arithmetic
import P256.Proofs.Scalar.Inverse.Wrapper.Value
import P256.Proofs.Scalar.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Inverse

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Arithmetic
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem result_value {s : RamState} {a : Nat}
    (ha : Nat256At s (s.regValue .rsi) a)
    (positive : 0 < a) (bound : a < P256.Spec.Operations.domain.n) :
    (Correction.limbs (resultWords (inputs s))).toNat =
      Standards.SECG.ECC.Curve.inverse P256.Spec.Operations.domain.n a ∧
      resultChoice (inputs s) = 1 := by
  obtain ⟨conditions, modulus, argument, scale⟩ := P256.Proofs.Scalar.Inverse.Wrapper.inputs_conditions ha bound
  change Shared.Arithmetic.modulus (scalarInput (inputs s)) = _ at modulus
  change Shared.Arithmetic.argument (scalarInput (inputs s)) = _ at argument
  change Shared.Arithmetic.scale (scalarInput (inputs s)) = _ at scale
  have hp := SafeGcd.result_product (scalarInput (inputs s)) conditions modulus
    (by rw [argument]; exact positive)
  have hc := SafeGcd.resultChoice_one (scalarInput (inputs s)) conditions modulus
    (by rw [argument]; exact positive)
  rw [Support.packed_limbs, modulus, argument, scale] at hp
  exact ⟨P256.Proofs.Scalar.inverse_unique positive bound hp.1 hp.2, hc⟩


end P256.Proofs.Verifying.Core.Inverse
