import P256.Proofs.Sec1.Affine.Compact.Flags.Correct

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Normalize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC

structure Original [Bindings] (s t : RamState) (point : Option Curve.Point) : Prop
    extends Frame s t where
  rip : t.RIP = 0x110358
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (stackPtr s - 480) (Select.xCoordinate point)
  y : Field.MontgomeryAt t (stackPtr s - 632) (Select.yCoordinate point)
  negativeInput : Field.MontgomeryAt t (stackPtr s - 416) (Select.yCoordinate point)
  r12 : t.regValue .r12 = stackPtr s - 632
  zero : t.regValue .r13 = 0
  choice : (t.regValue .rbp).setWidth 8 = if point.isSome then 1 else 0
  infinity : (t.regValue .r14).setWidth 8 = Flags.infinityFlag point
  mask : memLoad t.external (stackPtr s - 748) 8 = -(if point.isSome then 1 else 0)

structure Normalizing [Bindings] (s t : RamState) (point : Option Curve.Point) (pc : BitVec 64) : Prop
    extends Frame s t where
  rip : t.RIP = pc
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (stackPtr s - 480) (Select.xCoordinate point)
  y : Field.MontgomeryAt t (stackPtr s - 632) (Select.yCoordinate point)
  negative : Field.MontgomeryAt t (stackPtr s - 560) (Spec.Points.negElement (Select.yCoordinate point))
  r12 : t.regValue .r12 = stackPtr s - 632
  r15 : t.regValue .r15 = stackPtr s - 560
  zero : t.regValue .r13 = 0
  choice : (t.regValue .rbp).setWidth 8 = if point.isSome then 1 else 0
  infinity : (t.regValue .r14).setWidth 8 = Flags.infinityFlag point
  mask : memLoad t.external (stackPtr s - 748) 8 = -(if point.isSome then 1 else 0)


abbrev Negated [Bindings] (s t : RamState) (point : Option Curve.Point) :=
  Normalizing s t point 0x110370

abbrev ReadyDecode [Bindings] (s t : RamState) (point : Option Curve.Point) :=
  Normalizing s t point 0x1103b8

structure Decoded [Bindings] (s t : RamState) (point : Option Curve.Point) : Prop
    extends Normalizing s t point 0x1103d8 where
  canonicalY : SecretKeyFromBytes.Scalar.Nat256At t (stackPtr s-184) (Select.yCoordinate point)
  canonicalNegative : SecretKeyFromBytes.Scalar.Nat256At t (stackPtr s-416)
    (Spec.Points.negElement (Select.yCoordinate point))

end P256.Proofs.Sec1.Affine.Compact.Normalize
