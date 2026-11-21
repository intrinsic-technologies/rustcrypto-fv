import P256.Proofs.Sec1.Affine.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC

structure Prepared [Bindings] (s t : RamState) (point : Option Curve.Point) : Prop
    extends Frame s t where
  rip : t.RIP = 0x11015b
  output : t.regValue .rbx = s.regValue .rdi
  decoded : AffineResultAt t (stackPtr s - 744) point
  rax : t.regValue .rax = stackPtr s - 664
  rdx : t.regValue .rdx = stackPtr s - 744
  validity : t.regValue .r14 = BitVec.ofNat 64 point.isSome.toNat

structure XSelected [Bindings] (s t : RamState) (point : Option Curve.Point) : Prop
    extends Frame s t where
  rip : t.RIP = 0x110171
  output : t.regValue .rbx = s.regValue .rdi
  decoded : AffineResultAt t (stackPtr s - 744) point
  validity : t.regValue .r14 = BitVec.ofNat 64 point.isSome.toNat
  choice : (t.regValue .rbp).setWidth 8 = if point.isSome then 1 else 0
  selected : point.isSome = true → ∀ i < 32,
    t.external[stackPtr s - 384 + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - 744 + BitVec.ofNat 64 i]?

structure Selected [Bindings] (s t : RamState) (point : Option Curve.Point) : Prop
    extends Frame s t where
  rip : t.RIP = 0x11018d
  output : t.regValue .rbx = s.regValue .rdi
  decoded : AffineResultAt t (stackPtr s - 744) point
  validity : t.regValue .r14 = BitVec.ofNat 64 point.isSome.toNat
  choice : (t.regValue .rbp).setWidth 8 = if point.isSome then 1 else 0
  selected : point.isSome = true → ∀ i < 64,
    t.external[stackPtr s - 384 + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - 744 + BitVec.ofNat 64 i]?

end P256.Proofs.Sec1.Affine.Compressed.Finish
