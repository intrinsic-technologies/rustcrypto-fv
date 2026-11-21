import P256.Proofs.PublicPoint.Normalize.State

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.Finish

open P256.Spec.Operations Standards.SECG.ECC
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

abbrev frameBase (s : RamState) := stackPtr s - 1944

theorem buffer_add (s : RamState) (a : BitVec 64) (b i : Nat) :
    (frameBase s + a) + BitVec.ofNat 64 (b+i) =
      (frameBase s + (a + BitVec.ofNat 64 b)) + BitVec.ofNat 64 i := by
  simp only [BitVec.ofNat_add,BitVec.add_assoc]

structure Prepared [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (point : Projective) : Prop extends FrameState s t 65 3352 1944 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10eab9
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (frameBase s + 264)
    (point.x * Curve.inverse domain.p point.z % domain.p)
  y : Field.MontgomeryAt t (frameBase s + 296)
    (point.y * Curve.inverse domain.p point.z % domain.p)
  zeroX : Field.MontgomeryAt t (frameBase s + 1032) 0
  zeroY : Field.MontgomeryAt t (frameBase s + 1064) 0
  tag : t.external[frameBase s + 328]? = some 0
  choice : (t.regValue .rbp).setWidth 8 = if point.z = 0 then 0 else 1
  rax : t.regValue .rax = frameBase s + 1032
  rdx : t.regValue .rdx = frameBase s + 264

end P256.Proofs.PublicPoint.Normalize.Finish
