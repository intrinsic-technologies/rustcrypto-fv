import P256.Proofs.Verifying.Model

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core

open P256.Spec Standards.SECG.ECC

theorem digestToInt_eq {digest : ByteArray} (size : digest.size = 32) :
    ECDSA.digestToInt Operations.domain.n digest = Arith.uint digest := by
  have orderBits : Operations.domain.n.log2+1 = 256 := by decide +kernel
  simp only [ECDSA.digestToInt,size,orderBits,Nat.reduceMul,Nat.sub_self,
    Nat.pow_zero,Nat.div_one]
  rfl

theorem reduced_digest_product (digest : ByteArray) (scalar : Nat) (size : digest.size = 32) :
    (Arith.uint digest % Operations.domain.n)*scalar % Operations.domain.n =
      ECDSA.digestToInt Operations.domain.n digest*scalar % Operations.domain.n := by
  rw [digestToInt_eq size,Nat.mod_mul_mod]


theorem result_acceptance {point result : Projective} {digest : ByteArray} {r scalarS : Nat}
    (rPositive : 0 < r) (rBound : r < Operations.domain.n)
    (sPositive : 0 < scalarS) (sBound : scalarS < Operations.domain.n)
    (sum : result.toAffine = Verifying.verificationPoint point.toAffine digest r scalarS) :
    ((if result.z = 0 then 0 else result.x * Curve.inverse Operations.domain.p result.z %
      Operations.domain.p) % Operations.domain.n == r) =
      Ecdsa.verifies point.toAffine digest (r,scalarS) := by
  rw [← Verifying.verificationResult_projective result r rPositive,sum]
  exact (Verifying.verifies_eq point.toAffine digest r scalarS rPositive rBound sPositive sBound).symm

theorem selected_x (result : Projective) :
    (if decide (result.z ≠ 0) then
      result.x * Curve.inverse Operations.domain.p result.z % Operations.domain.p else 0) =
    (if result.z = 0 then 0 else
      result.x * Curve.inverse Operations.domain.p result.z % Operations.domain.p) := by
  by_cases zero : result.z=0 <;> simp [zero]

end P256.Proofs.Verifying.Core
