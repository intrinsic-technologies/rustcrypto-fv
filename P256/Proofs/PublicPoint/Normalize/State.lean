import P256.Proofs.PublicPoint.Loop
import P256.Proofs.Sec1.Interface

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize

open P256.Spec.Operations Standards.SECG.ECC
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

structure Selected [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (point : Projective) : Prop extends FrameState s t 65 3352 1944 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10e9ad
  output : t.regValue .rbx = s.regValue .rdi
  projective : ProjectiveAt t (stackPtr s - 1880) point
  inverse : Field.MontgomeryAt t (stackPtr s - 1712) (Curve.inverse domain.p point.z)
  choice : (t.regValue .rbp).setWidth 8 = if point.z = 0 then 0 else 1
  r14 : t.regValue .r14 = stackPtr s - 1712

structure Coordinates [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (point : Projective) : Prop extends FrameState s t 65 3352 1944 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10ea45
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (stackPtr s - 912)
    (point.x * Curve.inverse domain.p point.z % domain.p)
  y : Field.MontgomeryAt t (stackPtr s - 1912)
    (point.y * Curve.inverse domain.p point.z % domain.p)
  choice : (t.regValue .rbp).setWidth 8 = if point.z = 0 then 0 else 1
  r15 : t.regValue .r15 = stackPtr s - 912

end P256.Proofs.PublicPoint.Normalize
