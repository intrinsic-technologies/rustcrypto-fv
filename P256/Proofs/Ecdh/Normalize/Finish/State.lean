import P256.Proofs.Ecdh.Normalize.State

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Finish

open P256.Spec.Operations Standards.SECG.ECC
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

abbrev frameBase (s : RamState) := stackPtr s - 2056

structure Prepared [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (point : Projective) : Prop extends FrameState s t 32 3464 2056 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x1004bb
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (stackPtr s - 1040)
    (point.x * Curve.inverse domain.p point.z % domain.p)
  y : Field.MontgomeryAt t (stackPtr s - 1008)
    (point.y * Curve.inverse domain.p point.z % domain.p)
  zeroX : Field.MontgomeryAt t (stackPtr s - 1808) 0
  zeroY : Field.MontgomeryAt t (stackPtr s - 1776) 0
  choice : (t.regValue .rbp).setWidth 8 = if point.z = 0 then 0 else 1
  rax : t.regValue .rax = stackPtr s - 1808
  rdx : t.regValue .rdx = stackPtr s - 1040

structure Selected [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (x : Nat) : Prop extends FrameState s t 32 3464 2056 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x1004e6
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (stackPtr s - 1976) x

end P256.Proofs.Ecdh.Normalize.Finish
