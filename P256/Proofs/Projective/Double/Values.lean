import P256.Proofs.Projective.Multiply.Operations
import P256.Proofs.Projective.Representation

set_option autoImplicit false

open P256.Proofs.Field (MontgomeryAt)

namespace P256.Proofs.Projective.Double

open P256.Spec P256.Spec.Program P256.Proofs.Field Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Values where
  xx : Nat
  yy : Nat
  zz : Nat
  xy2 : Nat
  xz2 : Nat
  bzz3 : Nat
  yyMinus : Nat
  yyPlus : Nat
  bxz6 : Nat
  xxMinus : Nat
  yz2 : Nat

def values (point : Projective) : Values :=
  let p := P256.Spec.Operations.domain.p
  let fadd := fun x y => (x + y) % p
  let fsub := Standards.SECG.ECC.Curve.fieldSub p
  let fmul := fun x y => x * y % p
  let twice := fun x => fadd x x
  let triple := fun x => fadd (twice x) x
  let xx := fmul point.x point.x
  let yy := fmul point.y point.y
  let zz := fmul point.z point.z
  let xy2 := twice (fmul point.x point.y)
  let xz2 := twice (fmul point.x point.z)
  let bzz3 := triple (fsub (fmul P256.Spec.Operations.domain.b zz) xz2)
  let yyMinus := fsub yy bzz3
  let yyPlus := fadd yy bzz3
  let bxz6 := triple (fsub (fmul P256.Spec.Operations.domain.b xz2) (fadd (triple zz) xx))
  let xxMinus := fsub (triple xx) (triple zz)
  let yz2 := twice (fmul point.y point.z)
  ⟨xx, yy, zz, xy2, xz2, bzz3, yyMinus, yyPlus, bxz6, xxMinus, yz2⟩

def Values.xProduct (v : Values) : Nat :=
  v.yyMinus * v.xy2 % P256.Spec.Operations.domain.p

def Values.yProduct (v : Values) : Nat :=
  v.yyPlus * v.yyMinus % P256.Spec.Operations.domain.p

def Values.output (v : Values) : Projective :=
  let p := P256.Spec.Operations.domain.p
  let twice := fun x => (x + x) % p
  ⟨Standards.SECG.ECC.Curve.fieldSub p v.xProduct (v.bxz6 * v.yz2 % p),
    (v.yProduct + v.xxMinus * v.bxz6 % p) % p,
    twice (twice (v.yz2 * v.yy % p))⟩

structure SquaresAt (s t : RamState) (point : Projective) : Prop where
  pointAt : ProjectiveAt t (s.regValue .rdi) point
  rbx : t.regValue .rbx = s.regValue .rdi
  xx : MontgomeryAt t (stackPtr s - 624) (values point).xx
  yy : MontgomeryAt t (stackPtr s - 592) (values point).yy
  zz : MontgomeryAt t (stackPtr s - 560) (values point).zz

structure CrossTermsAt (s t : RamState) (point : Projective) : Prop where
  pointAt : ProjectiveAt t (s.regValue .rdi) point
  rbx : t.regValue .rbx = s.regValue .rdi
  rbp : t.regValue .rbp = 0xd89cdf6229c4bddf
  r14 : t.regValue .r14 = stackPtr s - 176
  r15 : t.regValue .r15 = stackPtr s - 432
  xx : MontgomeryAt t (stackPtr s - 624) (values point).xx
  yy : MontgomeryAt t (stackPtr s - 592) (values point).yy
  zz : MontgomeryAt t (stackPtr s - 560) (values point).zz
  xy2 : MontgomeryAt t (stackPtr s - 176) (values point).xy2
  xz2 : MontgomeryAt t (stackPtr s - 528) (values point).xz2
  bzz3 : MontgomeryAt t (stackPtr s - 432) (values point).bzz3

structure ProductsAt (s t : RamState) (point : Projective) : Prop where
  pointAt : ProjectiveAt t (s.regValue .rdi) point
  rbx : t.regValue .rbx = s.regValue .rdi
  rbp : t.regValue .rbp = 0xd89cdf6229c4bddf
  r15 : t.regValue .r15 = stackPtr s - 112
  xx : MontgomeryAt t (stackPtr s - 624) (values point).xx
  yy : MontgomeryAt t (stackPtr s - 592) (values point).yy
  zz : MontgomeryAt t (stackPtr s - 560) (values point).zz
  xz2 : MontgomeryAt t (stackPtr s - 528) (values point).xz2
  xProduct : MontgomeryAt t (stackPtr s - 208) (values point).xProduct
  yProduct : MontgomeryAt t (stackPtr s - 112) (values point).yProduct

structure CombinationsAt (s t : RamState) (point : Projective) : Prop where
  pointAt : ProjectiveAt t (s.regValue .rdi) point
  rbx : t.regValue .rbx = s.regValue .rdi
  r14 : t.regValue .r14 = stackPtr s - 304
  yy : MontgomeryAt t (stackPtr s - 592) (values point).yy
  bxz6 : MontgomeryAt t (stackPtr s - 304) (values point).bxz6
  xProduct : MontgomeryAt t (stackPtr s - 208) (values point).xProduct
  y : MontgomeryAt t (stackPtr s - 272) (values point).output.y

structure OutputAt (s t : RamState) (point : Projective) : Prop where
  rbx : t.regValue .rbx = s.regValue .rdi
  x : MontgomeryAt t (stackPtr s - 496) point.double.x
  y : MontgomeryAt t (stackPtr s - 272) point.double.y
  z : MontgomeryAt t (stackPtr s - 656) point.double.z

end P256.Proofs.Projective.Double
