import P256.Proofs.Projective.Formula
import P256.Proofs.Projective.Add.Entry
set_option autoImplicit false


namespace P256.Proofs.Projective.Add

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Values where
  xx : Nat
  yy : Nat
  zz : Nat
  xy : Nat
  yz : Nat
  xz : Nat
  bzz3 : Nat
  yyMinus : Nat
  yyPlus : Nat
  zz3 : Nat
  bxz3 : Nat
  xxMinus : Nat

def values (left right : Projective) : Values :=
  let p := P256.Spec.Operations.domain.p
  let add := fun x y => (x + y) % p
  let sub := Standards.SECG.ECC.Curve.fieldSub p
  let mul := fun x y => x * y % p
  let triple := fun x => add (add x x) x
  let xx := mul left.x right.x
  let yy := mul left.y right.y
  let zz := mul left.z right.z
  let xy := sub (mul (add left.x left.y) (add right.x right.y)) (add xx yy)
  let yz := sub (mul (add left.y left.z) (add right.y right.z)) (add yy zz)
  let xz := sub (mul (add left.x left.z) (add right.x right.z)) (add xx zz)
  let bzz3 := triple (sub xz (mul P256.Spec.Operations.domain.b zz))
  let yyMinus := sub yy bzz3
  let yyPlus := add yy bzz3
  let zz3 := triple zz
  let bxz3 := triple (sub (mul P256.Spec.Operations.domain.b xz) (add zz3 xx))
  let xxMinus := sub (triple xx) zz3
  ⟨xx, yy, zz, xy, yz, xz, bzz3, yyMinus, yyPlus, zz3, bxz3, xxMinus⟩

def Values.output (v : Values) : Projective :=
  let p := P256.Spec.Operations.domain.p
  ⟨Standards.SECG.ECC.Curve.fieldSub p (v.yyPlus * v.xy % p) (v.yz * v.bxz3 % p),
    (v.yyPlus * v.yyMinus % p + v.xxMinus * v.bxz3 % p) % p,
    (v.yyMinus * v.yz % p + v.xy * v.xxMinus % p) % p⟩

theorem values_output (left right : Projective) :
    (values left right).output = left.add right := rfl

structure ProductsAt (s t : RamState) (left right : Projective) : Prop where
  leftPoint : ProjectiveAt t (s.regValue .rdi) left
  rightPoint : ProjectiveAt t (s.regValue .rsi) right
  rbx : t.regValue .rbx = s.regValue .rdi
  r14 : t.regValue .r14 = s.regValue .rsi
  rbp : t.regValue .rbp = stackPtr s - 528
  xx : MontgomeryAt t (stackPtr s - 560) (values left right).xx
  yy : MontgomeryAt t (stackPtr s - 464) (values left right).yy
  zz : MontgomeryAt t (stackPtr s - 528) (values left right).zz

structure CrossTermsAt (s t : RamState) (left right : Projective) : Prop where
  rbx : t.regValue .rbx = s.regValue .rdi
  rbp : t.regValue .rbp = stackPtr s - 528
  xx : MontgomeryAt t (stackPtr s - 560) (values left right).xx
  yy : MontgomeryAt t (stackPtr s - 464) (values left right).yy
  zz : MontgomeryAt t (stackPtr s - 528) (values left right).zz
  xy : MontgomeryAt t (stackPtr s - 400) (values left right).xy
  yz : MontgomeryAt t (stackPtr s - 368) (values left right).yz
  xz : MontgomeryAt t (stackPtr s - 336) (values left right).xz

structure CombinationsAt (s t : RamState) (left right : Projective) : Prop where
  rbx : t.regValue .rbx = s.regValue .rdi
  r12 : t.regValue .r12 = stackPtr s - 112
  r13 : t.regValue .r13 = stackPtr s - 432
  rbp : t.regValue .rbp = stackPtr s - 176
  xy : MontgomeryAt t (stackPtr s - 400) (values left right).xy
  yz : MontgomeryAt t (stackPtr s - 368) (values left right).yz
  yyMinus : MontgomeryAt t (stackPtr s - 304) (values left right).yyMinus
  yyPlus : MontgomeryAt t (stackPtr s - 272) (values left right).yyPlus
  bxz3 : MontgomeryAt t (stackPtr s - 112) (values left right).bxz3
  xxMinus : MontgomeryAt t (stackPtr s - 432) (values left right).xxMinus

end P256.Proofs.Projective.Add
