import K256.Proofs.Sec1.Affine.Uncompressed.ProductWords
import K256.Proofs.Sec1.Affine.Compressed.Cube.Steps.Product

namespace K256.Proofs.Sec1.Affine.Uncompressed

open X86Proofs Common.Field

private theorem finalProduct_eq (s : Vector Word 9) :
    cubeProduct1201AB s = Compressed.cubeProduct120C87 s := by
  let reduced := (s[0] &&& 0xfffffffffffff) + s[4] * 0x1000003d10
  let lo := reduced + s[6]
  let finish (limb : Word) : Limbs :=
    #v[s[2], s[3], s[8], limb, (Compressed.cubeProduct120C87 s)[4]]
  exact congrArg finish (BitVec.and_comm lo 0xfffffffffffff)

private theorem cubeProduct_eq_compressed (a b : Limbs) :
    cubeProduct a b = Compressed.cubeProduct a b := by
  have e₁ :
      cubeProduct11FE67H a b = Compressed.cubeProduct120934H a b := rfl
  have e₂ (s : Vector Word 6) :
      cubeProduct11FED2 a b s = Compressed.cubeProduct1209B8 a b s := rfl
  have e₃ (s : Vector Word 11) :
      cubeProduct11FF5F a b s = Compressed.cubeProduct120A3C a b s := rfl
  have e₄ (s : Vector Word 15) :
      cubeProduct11FFD9C a b s = Compressed.cubeProduct120ABBC a b s := rfl
  have e₅ (s : Vector Word 7) :
      cubeProduct120038 a b s = Compressed.cubeProduct120B1A a b s := rfl
  have e₆ (s : Vector Word 12) :
      cubeProduct1200C8 a b s = Compressed.cubeProduct120BA9 a b s := rfl
  have e₇ (s : Vector Word 18) :
      cubeProduct12014D s = Compressed.cubeProduct120C2B s := rfl
  simp only [cubeProduct, Compressed.cubeProduct, e₁, e₂, e₃, e₄, e₅, e₆, e₇, finalProduct_eq]

theorem cubeProduct_repr (a b : Limbs) (x z : Fin modulus)
    (ha : FieldRepr a x 8) (hb : FieldRepr b z 1) :
    FieldRepr (cubeProduct a b) (z * x) 1 := by
  rw [cubeProduct_eq_compressed, Fin.mul_comm z x]
  exact Compressed.cubeProduct_repr a b x z ha (hb.mono (by decide))

end K256.Proofs.Sec1.Affine.Uncompressed
