import P256.Proofs.Projective.Representation

set_option autoImplicit false

namespace P256.Proofs.Projective

def add (left right : Projective) : Projective :=
  let p := P256.Spec.Operations.domain.p
  let fadd := fun x y => (x + y) % p
  let fsub := Standards.SECG.ECC.Curve.fieldSub p
  let fmul := fun x y => x * y % p
  let triple := fun x => fadd (fadd x x) x
  let xx := fmul left.x right.x
  let yy := fmul left.y right.y
  let zz := fmul left.z right.z
  let xy := fsub (fmul (fadd left.x left.y) (fadd right.x right.y)) (fadd xx yy)
  let yz := fsub (fmul (fadd left.y left.z) (fadd right.y right.z)) (fadd yy zz)
  let xz := fsub (fmul (fadd left.x left.z) (fadd right.x right.z)) (fadd xx zz)
  let bzz3 := triple (fsub xz (fmul P256.Spec.Operations.domain.b zz))
  let yyMinus := fsub yy bzz3
  let yyPlus := fadd yy bzz3
  let zz3 := triple zz
  let bxz3 := triple (fsub (fmul P256.Spec.Operations.domain.b xz) (fadd zz3 xx))
  let xxMinus := fsub (triple xx) zz3
  ⟨fsub (fmul yyPlus xy) (fmul yz bxz3),
    fadd (fmul yyPlus yyMinus) (fmul xxMinus bxz3),
    fadd (fmul yyMinus yz) (fmul xy xxMinus)⟩


theorem add_canonical (left right : Projective) : (left.add right).canonical := by
  have positive : 0 < P256.Spec.Operations.domain.p := by decide +kernel
  dsimp only [add, canonical, Standards.SECG.ECC.Curve.fieldSub]
  exact ⟨Nat.mod_lt _ positive, Nat.mod_lt _ positive, Nat.mod_lt _ positive⟩

end P256.Proofs.Projective
