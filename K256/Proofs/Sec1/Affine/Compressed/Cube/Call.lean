import K256.Proofs.Sec1.Affine.Compressed.Cube.Steps.Residue
import K256.Proofs.Sec1.Affine.Compressed.Cube.Steps.Execution
import K256.Proofs.Sec1.Affine.Compressed.Cube.Steps.Product
import K256.Proofs.Sec1.Affine.Compressed.Cube.Steps.Square

namespace K256.Proofs.Sec1.Affine.Compressed

open X86.UserProcess X86Proofs K256.Proofs.Sec1.LIR K256.Proofs.Common.Field

theorem cubeCall {code : CodeMap} (cover : ∀ e ∈ fnCode, e ∈ code) : CubeCall code := by
  apply cubeExecution cover
  intro a b c d ok
  let xs := maskedX a b c d ok
  let x : Fin modulus := ⟨limbValue xs % modulus, Nat.mod_lt _ (by decide)⟩
  have hx : FieldRepr xs x 8 := maskedX_repr a b c d ok
  have hs := inputSquare_repr xs x hx
  have hm := cubeProduct_repr xs (inputSquare xs) x (x * x) hx (hs.mono (by decide))
  have hval : (x * (x * x)).val = (limbValue xs * limbValue xs * limbValue xs) % modulus := by
    simp only [Fin.val_mul, x, Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mul_assoc]
  simpa only [addSeven, hval, Nat.mod_add_mod] using addSeven_repr hm

end K256.Proofs.Sec1.Affine.Compressed
