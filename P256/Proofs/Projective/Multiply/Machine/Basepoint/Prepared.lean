import P256.Proofs.Projective.Multiply.Machine.Basepoint.Interface

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

structure Prepared [Bindings] (s t : RamState) (boundary : ReturnBoundary) : Prop extends
    ScalarFrame.FrameState s t 65 3352 1944 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10e907
  output : t.regValue .rbx = s.regValue .rdi
  scalar : t.regValue .r15 = s.regValue .rsi
  table : Lookup.TableAt t (stackPtr s - 1680) (Projective.table basePoint)

end P256.Proofs.Projective.Multiply.Machine.Basepoint
