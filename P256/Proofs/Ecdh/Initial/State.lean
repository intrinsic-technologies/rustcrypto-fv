import P256.Proofs.Ecdh.Interface
import P256.Proofs.Projective.Multiply.Operations

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Initial

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Standards.SECG.ECC

def lifted (point : Curve.Point) : Projective :=
  match point with
  | .infinity => ⟨0, 0, 1⟩
  | .affine x y => ⟨x, y, 1⟩

structure Copied [Bindings] (s t : RamState) (point : Curve.Point) : Prop extends Ecdh.Frame s t where
  rip : t.RIP = 0x1000e6
  output : t.regValue .rbx = s.regValue .rdi
  scalar : memLoad t.external (frameBase s + 8) 64 = s.regValue .rsi
  source : ProjectiveAt t (frameBase s + 248) (lifted point)
  identity : ProjectiveAt t (frameBase s + 1016) Projective.identity
  r14 : t.regValue .r14 = frameBase s + 280
  r12 : t.regValue .r12 = frameBase s + 312
  r13 : t.regValue .r13 = frameBase s + 1016
  choice : (t.regValue .rax).setWidth 8 = if point = .infinity then 1 else 0

structure Selected [Bindings] (s t : RamState) (point : Curve.Point) : Prop extends Ecdh.Frame s t where
  rip : t.RIP = 0x10013a
  output : t.regValue .rbx = s.regValue .rdi
  scalar : memLoad t.external (frameBase s + 8) 64 = s.regValue .rsi
  base : ProjectiveAt t (frameBase s + 1784) (ProjectiveWrapper.Decode.projective point)
  r15 : t.regValue .r15 = frameBase s + 1784

end P256.Proofs.Ecdh.Initial
