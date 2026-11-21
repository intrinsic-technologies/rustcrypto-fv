import P256.Proofs.Ecdh.Interface
import P256.Proofs.Projective.Preserve
import P256.Proofs.Sec1.Interface

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize

open P256.Spec.Operations Standards.SECG.ECC
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

structure Selected [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (point : Projective) : Prop extends FrameState s t 32 3464 2056 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x100397
  output : t.regValue .rbx = s.regValue .rdi
  projective : ProjectiveAt t (stackPtr s - 1904) point
  inverse : Field.MontgomeryAt t (stackPtr s - 176) (Curve.inverse domain.p point.z)
  choice : (t.regValue .rbp).setWidth 8 = if point.z = 0 then 0 else 1
  r14 : t.regValue .r14 = stackPtr s - 176

structure Coordinates [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (point : Projective) : Prop extends FrameState s t 32 3464 2056 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x100447
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (stackPtr s - 1808)
    (point.x * Curve.inverse domain.p point.z % domain.p)
  y : Field.MontgomeryAt t (stackPtr s - 2008)
    (point.y * Curve.inverse domain.p point.z % domain.p)
  choice : (t.regValue .rbp).setWidth 8 = if point.z = 0 then 0 else 1
  r15 : t.regValue .r15 = stackPtr s - 1808

end P256.Proofs.Ecdh.Normalize
