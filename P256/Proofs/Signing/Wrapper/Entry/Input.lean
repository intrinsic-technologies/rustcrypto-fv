import P256.Proofs.SecretKeyFromBytes.Model
import P256.Proofs.Signing.Wrapper.Interface

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry

open P256.Spec P256.Spec.Program.Routines

theorem arguments_iff (secret message : ByteArray) :
    signingKeyTrySign.arguments #[secret, message] = true ↔
      secret.size = 32 ∧ 0 < Arith.uint secret ∧ Arith.uint secret < Operations.domain.n := by
  have arguments : signingKeyTrySign.arguments #[secret, message] =
      Arith.isNonZeroScalar secret := by
    simp [signingKeyTrySign, Functions.signingKeyTrySignArguments, Arith.slices, Arith.anyBytes]
  rw [arguments]
  change (Keys.secretOfBytes secret).isSome = true ↔ _
  rw [SecretKeyFromBytes.secretOfBytes_eq]
  split <;> simp_all

theorem secretValue_eq {secret message : ByteArray}
    (arguments : signingKeyTrySign.arguments #[secret, message] = true) :
    Ecdsa.secretValue secret = Arith.uint secret := by
  have valid := (arguments_iff secret message).mp arguments
  change (Keys.secretOfBytes secret).getD 0 = _
  simp [SecretKeyFromBytes.secretOfBytes_eq, valid]

end P256.Proofs.Signing.Wrapper.Entry
