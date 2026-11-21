import P256.Proofs.Sec1.Affine.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Select

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC

def xCoordinate : Option Curve.Point → Nat
  | some (.affine x _) => x
  | _ => 0

def yCoordinate : Option Curve.Point → Nat
  | some (.affine _ y) => y
  | _ => 0

structure Initialized [Bindings] (s t : RamState) (point : Option Curve.Point) : Prop
    extends Frame s t where
  rip : t.RIP = 0x110246
  output : t.regValue .rbx = s.regValue .rdi
  decoded : AffineResultAt t (stackPtr s - 744) point
  identity : AffineAt t (stackPtr s - 384) .infinity
  rax : t.regValue .rax = stackPtr s - 384
  source : t.regValue .r15 = stackPtr s - 744
  zero : t.regValue .r13 = 0

structure XSelected [Bindings] (s t : RamState) (point : Option Curve.Point) : Prop
    extends Frame s t where
  rip : t.RIP = 0x11025f
  output : t.regValue .rbx = s.regValue .rdi
  decoded : AffineResultAt t (stackPtr s - 744) point
  x : Field.MontgomeryAt t (stackPtr s - 480) (xCoordinate point)
  zeroY : Field.MontgomeryAt t (stackPtr s - 352) 0
  zero : t.regValue .r13 = 0
  choice : (t.regValue .rbp).setWidth 8 = if point.isSome then 1 else 0

structure Selected [Bindings] (s t : RamState) (point : Option Curve.Point) : Prop
    extends Frame s t where
  rip : t.RIP = 0x11027b
  output : t.regValue .rbx = s.regValue .rdi
  decoded : AffineResultAt t (stackPtr s - 744) point
  x : Field.MontgomeryAt t (stackPtr s - 480) (xCoordinate point)
  y : Field.MontgomeryAt t (stackPtr s - 448) (yCoordinate point)
  zero : t.regValue .r13 = 0
  choice : (t.regValue .rbp).setWidth 8 = if point.isSome then 1 else 0

end P256.Proofs.Sec1.Affine.Compact.Select
