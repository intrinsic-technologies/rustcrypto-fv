import P256.Proofs.Ecdh.Model
import P256.Proofs.SecretKeyFromBytes.Model
import P256.Proofs.Sec1.Model

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper

open P256.Spec P256.Spec.Program.Routines Standards.SECG.ECC

theorem arguments_iff (secret peer : ByteArray) :
    ecdhDiffieHellman.arguments #[secret, peer] = true ↔
      secret.size = 32 ∧ 0 < Arith.uint secret ∧ Arith.uint secret < Operations.domain.n ∧
        (Points.decodePoint peer).isSome = true := by
  have arguments : ecdhDiffieHellman.arguments #[secret, peer] =
      (Arith.isNonZeroScalar secret && Points.isAffineEncoding peer) := by
    simp [ecdhDiffieHellman, Functions.ecdhDiffieHellmanArguments, Arith.slices]
  rw [arguments, Bool.and_eq_true]
  change (Keys.secretOfBytes secret).isSome = true ∧
    (Points.decodePoint peer).isSome = true ↔ _
  rw [SecretKeyFromBytes.secretOfBytes_eq]
  split <;> simp_all <;> omega

theorem arguments_decoded {secret peer : ByteArray}
    (arguments : ecdhDiffieHellman.arguments #[secret, peer] = true) :
    ∃ point, secret.size = 32 ∧ 0 < Arith.uint secret ∧
      Arith.uint secret < Operations.domain.n ∧ Points.decodePoint peer = some point ∧
      Curve.onCurve Operations.domain point = true ∧ Sec1.EncodingShape peer := by
  obtain ⟨size, positive, bound, decoded⟩ := (arguments_iff secret peer).mp arguments
  obtain ⟨point, decoded⟩ := Option.isSome_iff_exists.mp decoded
  exact ⟨point, size, positive, bound, decoded,
    Sec1.Affine.decodePoint_some_onCurve decoded, Sec1.decodePoint_some_shape decoded⟩

theorem diffieHellman_of_decoded {secret peer : ByteArray} {point : Curve.Point}
    (decoded : Points.decodePoint peer = some point) :
    P256.Spec.Ecdh.diffieHellman #[secret, peer] =
      P256.Spec.Ecdh.sharedX (Arith.uint secret) point := by
  simp [P256.Spec.Ecdh.diffieHellman, Points.scalarArgument, Points.pointArgument,
    Points.pointOf, Arith.argument, Arith.element, Arith.uint, decoded]

theorem machine_output_of_decoded {secret peer : ByteArray} {point : Curve.Point}
    (size : secret.size = 32) (decoded : Points.decodePoint peer = some point) :
    Points.xBytes
      (Projective.Multiply.model (ProjectiveWrapper.Decode.projective point)
        (Arith.uint secret)).toAffine = P256.Spec.Ecdh.diffieHellman #[secret, peer] := by
  rw [Ecdh.model_sharedX (Sec1.Affine.decodePoint_some_onCurve decoded) ?_,
    diffieHellman_of_decoded decoded]
  have bound := SecretKeyFromBytes.Encoding.octetsToNat_lt secret
  simpa [Arith.uint, Arith.decodeBigEndian, size] using bound

theorem xBytes_size (point : Curve.Point) : (Points.xBytes point).size = 32 := by
  cases point <;> exact SecretKeyFromBytes.Encoding.natToOctets_size _ _

theorem diffieHellman_size (inputs : Array ByteArray) :
    (P256.Spec.Ecdh.diffieHellman inputs).size = 32 :=
  xBytes_size _

end P256.Proofs.EcdhWrapper
