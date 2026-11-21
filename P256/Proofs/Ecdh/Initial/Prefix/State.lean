import P256.Proofs.Ecdh.Initial.State

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Initial.Prefix

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Standards.SECG.ECC

structure Prepared [Bindings] (s t : RamState) (point : Curve.Point) : Prop extends Ecdh.Frame s t where
  rip : t.RIP = 0x1000db
  output : t.regValue .rbx = s.regValue .rdi
  scalar : memLoad t.external (frameBase s + 8) 64 = s.regValue .rsi
  source : ProjectiveAt t (frameBase s + 248) (lifted point)
  r14 : t.regValue .r14 = frameBase s + 280
  r12 : t.regValue .r12 = frameBase s + 312
  r13 : t.regValue .r13 = frameBase s + 1016
  destination : t.regValue .rdi = frameBase s + 1016
  constant : t.regValue .rsi = 0x202490
  count : t.regValue .rcx = 12
  peer : t.regValue .rdx = s.regValue .rdx

end P256.Proofs.Ecdh.Initial.Prefix
