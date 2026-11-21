import P256.Proofs.Sec1.Affine.Compact.Flags.Correct

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC

structure Prepared [Bindings] (s t : RamState) (point : Option Curve.Point) : Prop
    extends Frame s t where
  rip : t.RIP = 0x110500
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (stackPtr s - 480) (Select.xCoordinate point)
  y : Field.MontgomeryAt t (stackPtr s - 88) (Spec.Points.compactY (Select.yCoordinate point))
  choice : (t.regValue .rbp).setWidth 8 = if point.isSome then 1 else 0
  infinity : (t.regValue .r14).setWidth 8 = Flags.infinityFlag point
  mask : memLoad t.external (stackPtr s - 748) 8 = -(if point.isSome then 1 else 0)

def mapped (point : Option Curve.Point) : Option Curve.Point :=
  point.map fun
    | .affine x y => .affine x (Spec.Points.compactY y)
    | .infinity => .infinity

structure Relocated [Bindings] (s t : RamState) (point : Option Curve.Point) : Prop
    extends Frame s t where
  rip : t.RIP = 0x110565
  output : t.regValue .rbx = s.regValue .rdi
  decoded : AffineResultAt t (stackPtr s - 744) (mapped point)
  rdx : t.regValue .rdx = stackPtr s - 744
  choice : (t.regValue .rbp).setWidth 8 = if point.isSome then 1 else 0
  mask : memLoad t.external (stackPtr s - 748) 8 = -(if point.isSome then 1 else 0)

structure Ready [Bindings] (s t : RamState) (point : Option Curve.Point) : Prop
    extends Frame s t where
  rip : t.RIP = 0x11057f
  output : t.regValue .rbx = s.regValue .rdi
  decoded : AffineResultAt t (stackPtr s - 744) (mapped point)
  rax : t.regValue .rax = stackPtr s - 592
  rdx : t.regValue .rdx = stackPtr s - 744
  choice : (t.regValue .rbp).setWidth 8 = if point.isSome then 1 else 0
  mask : memLoad t.external (stackPtr s - 748) 8 = -(if point.isSome then 1 else 0)

structure XSelected [Bindings] (s t : RamState) (point : Option Curve.Point) : Prop
    extends Frame s t where
  rip : t.RIP = 0x11058e
  output : t.regValue .rbx = s.regValue .rdi
  decoded : AffineResultAt t (stackPtr s - 744) (mapped point)
  choice : (t.regValue .rbp).setWidth 8 = if point.isSome then 1 else 0
  mask : memLoad t.external (stackPtr s - 748) 8 = -(if point.isSome then 1 else 0)
  selected : point.isSome = true → ∀ i < 32,
    t.external[stackPtr s - 664 + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - 744 + BitVec.ofNat 64 i]?

structure Selected [Bindings] (s t : RamState) (point : Option Curve.Point) : Prop
    extends Frame s t where
  rip : t.RIP = 0x1105aa
  output : t.regValue .rbx = s.regValue .rdi
  decoded : AffineResultAt t (stackPtr s - 744) (mapped point)
  choice : (t.regValue .rbp).setWidth 8 = if point.isSome then 1 else 0
  mask : memLoad t.external (stackPtr s - 748) 8 = -(if point.isSome then 1 else 0)
  selected : point.isSome = true → ∀ i < 64,
    t.external[stackPtr s - 664 + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - 744 + BitVec.ofNat 64 i]?

end P256.Proofs.Sec1.Affine.Compact.Finish
