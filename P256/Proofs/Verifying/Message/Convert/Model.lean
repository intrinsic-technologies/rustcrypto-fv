import P256.Proofs.Verifying.Message.Interface
import P256.Proofs.ProjectiveWrapper.Model

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec Standards.SECG.ECC

abbrev lifted := ProjectiveWrapper.Decode.projective

theorem lifted_valid (key : Curve.Point) (valid : Curve.onCurve Operations.domain key = true) :
    (lifted key).valid := ProjectiveWrapper.projective_valid key valid

theorem lifted_toAffine (key : Curve.Point)
    (valid : Curve.onCurve Operations.domain key = true) : (lifted key).toAffine = key :=
  ProjectiveWrapper.projective_toAffine key (lifted_valid key valid).1

theorem decoded_key {bytes : ByteArray} {key : Curve.Point}
    (decoded : Ecdsa.decodePublicKey bytes = some key) :
    Curve.onCurve Operations.domain key = true ∧ key ≠ .infinity := by
  unfold Ecdsa.decodePublicKey at decoded
  split at decoded
  next size =>
    have nonidentity : key ≠ .infinity := by
      intro eq
      subst key
      exact Sec1.decodePublicKey_ne_infinity bytes decoded
    have point : Points.decodePoint bytes = some key := by
      cases key with
      | infinity => exact (nonidentity rfl).elim
      | affine x y => exact Sec1.decodePublicKey_affine.mp decoded
    exact ⟨Sec1.Affine.decodePoint_some_onCurve point, nonidentity⟩
  next size => contradiction

end P256.Proofs.Verifying.Message.Convert
