import P256.Proofs.Signing.Core.Iteration.Stages
import P256.Proofs.Verifying.Core.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components

open P256.Spec Standards.SECG.ECC

def scalarS (secret nonce x : Nat) (digest : ByteArray) : Nat :=
  Curve.inverse Operations.domain.n nonce *
    ((Arith.uint digest % Operations.domain.n +
      (x % Operations.domain.n * secret) % Operations.domain.n) % Operations.domain.n) %
        Operations.domain.n

theorem scalarS_eq {secret nonce x : Nat} {digest : ByteArray} (size : digest.size = 32) :
    scalarS secret nonce x digest = Curve.inverse Operations.domain.n nonce *
      (ECDSA.digestToInt Operations.domain.n digest + (x % Operations.domain.n) * secret) %
        Operations.domain.n := by
  rw [Verifying.Core.digestToInt_eq size]
  simp only [scalarS, Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_mod_mod]

theorem signWithNonce_of_affine {secret nonce x y : Nat} {digest : ByteArray}
    (secretPositive : 0 < secret) (secretCanonical : secret < Operations.domain.n)
    (noncePositive : 0 < nonce) (nonceCanonical : nonce < Operations.domain.n)
    (size : digest.size = 32)
    (point : Curve.scalarMul Operations.domain nonce Operations.domain.G = .affine x y) :
    Ecdsa.signWithNonce secret nonce digest =
      if x % Operations.domain.n == 0 || scalarS secret nonce x digest == 0 then none
      else some (x % Operations.domain.n, scalarS secret nonce x digest) := by
  rw [scalarS_eq size]
  simp [Ecdsa.signWithNonce, ECDSA.signWithNonce, Nat.ne_of_gt secretPositive,
    Nat.not_le_of_gt secretCanonical, Nat.ne_of_gt noncePositive,
    Nat.not_le_of_gt nonceCanonical, point]

end P256.Proofs.Signing.Core.Iteration.Components
