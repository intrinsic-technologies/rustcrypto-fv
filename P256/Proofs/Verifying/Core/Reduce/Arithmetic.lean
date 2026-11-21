import P256.Proofs.Scalar.Multiply.Arithmetic.Reduction
import P256.Proofs.Scalar.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Reduce

open SecretKeyFromBytes.Scalar
export P256.Proofs.Scalar.Multiply.Arithmetic.Reduction (subtractOrder subtractOrder_toNat)

def reduceOrder (a : Limbs) : Limbs :=
  if orderBorrow a = 0 then subtractOrder a else a

theorem reduceOrder_toNat (a : Limbs) :
    (reduceOrder a).toNat = a.toNat % P256.Spec.Operations.domain.n := by
  have difference := subtractOrder_toNat a
  rw [Scalar.mod_order_eq_sub (limbs_toNat_lt a)]
  by_cases small : a.toNat < P256.Spec.Operations.domain.n
  · simp [reduceOrder,orderBorrow_eq,small]
  · simp only [orderBorrow_eq,small,ite_false] at difference
    change (subtractOrder a).toNat + P256.Spec.Operations.domain.n = a.toNat+0 at difference
    simp only [reduceOrder,orderBorrow_eq,small,ite_false,ite_true]
    omega

end P256.Proofs.Verifying.Core.Reduce
