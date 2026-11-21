import K256.Proofs.Common.Field.Multiply.Residue
import K256.Proofs.Common.Field.Multiply.Value
import K256.Proofs.Common.Field.SqrtRepr

namespace K256.Proofs.Common.Field

theorem mulWords_repr (a b : Limbs) (x y : Fin modulus)
    (ha : FieldRepr a x 8) (hb : FieldRepr b y 8) :
    FieldRepr (mulWords a b) (x * y) 1 := by
  obtain ⟨hv, hbound⟩ := Multiply.mulWords_value_and_bounds ha hb
  refine ⟨hbound, ?_⟩
  rw [Multiply.product_residue hv, Nat.mul_mod, ha.2, hb.2, Fin.val_mul]

theorem SqrtChain.mulWords_result_repr {a : Limbs} {x : Fin modulus} (ha : FieldRepr a x 8) :
    FieldRepr (result squareWords mulWords a chain)
      ⟨x.val ^ ((modulus + 1) / 4) % modulus, Nat.mod_lt _ (by decide)⟩ 8 :=
  result_repr mulWords mulWords_repr ha

end K256.Proofs.Common.Field
