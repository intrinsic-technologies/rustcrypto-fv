import K256.Proofs.Common.Field.Multiply
import K256.Proofs.Sec1.Serialize.Normalize.Correct

namespace K256.Proofs.Generate.Generator.Affine

open K256.Proofs.Common.Field

theorem normalizedProduct_repr {a b : Limbs} {x y : Fin modulus}
    (ha : FieldRepr a x 8) (hb : FieldRepr b y 8) :
    FieldRepr (Sec1.Serialize.Normalize.normalize (mulWords a b)) (x * y) 8 := by
  obtain ⟨widths, value⟩ := Sec1.Serialize.Normalize.normalize_correct _ _ 1
    (mulWords_repr a b x y ha hb) (by decide)
  refine ⟨?_, by rw [value, Nat.mod_eq_of_lt (x * y).isLt]⟩
  intro i
  have hi := widths i
  change _ < 2 ^ (if i.val = 4 then 48 else 52) at hi
  simp (disch := exact i.isLt) only [getElem!_pos]
  split <;> split at hi <;> have := i.isLt <;> omega

end K256.Proofs.Generate.Generator.Affine
