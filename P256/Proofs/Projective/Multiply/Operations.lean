import P256.Proofs.Projective.Algebra

set_option autoImplicit false

namespace P256.Proofs.Projective

open Standards.SECG.ECC
open P256.Spec.Operations (domain)

def identity : Projective := ⟨0, 1, 0⟩

def double (point : Projective) : Projective :=
  let p := domain.p
  let fadd := fun x y => (x + y) % p
  let fsub := Curve.fieldSub p
  let fmul := fun x y => x * y % p
  let twice := fun x => fadd x x
  let triple := fun x => fadd (twice x) x
  let xx := fmul point.x point.x
  let yy := fmul point.y point.y
  let zz := fmul point.z point.z
  let xy2 := twice (fmul point.x point.y)
  let xz2 := twice (fmul point.x point.z)
  let bzz3 := triple (fsub (fmul domain.b zz) xz2)
  let yyMinus := fsub yy bzz3
  let yyPlus := fadd yy bzz3
  let bxz6 := triple (fsub (fmul domain.b xz2) (fadd (triple zz) xx))
  let xxMinus := fsub (triple xx) (triple zz)
  let yz2 := twice (fmul point.y point.z)
  ⟨fsub (fmul yyMinus xy2) (fmul bxz6 yz2),
    fadd (fmul yyPlus yyMinus) (fmul xxMinus bxz6),
    twice (twice (fmul yz2 yy))⟩

def negate (point : Projective) : Projective :=
  ⟨point.x, Curve.fieldSub domain.p 0 point.y, point.z⟩

end P256.Proofs.Projective
