import P256.Proofs.Signing.Core.Initialize.State
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure Entered [Bindings] (s t u : RamState) : Prop where
  frame : ScalarFrame.FrameState s u 65 4584 2304
  bytes : ∀ offset < 2288, u.external[frameBase s + BitVec.ofNat 64 offset]? =
    t.external[frameBase s + BitVec.ofNat 64 offset]?
  registers : ∀ r : Syntax.Reg, r ≠ .rsp → u.regValue r = t.regValue r
  rip : u.RIP = 0x107790
  returnAddress : (returnBoundary u).rip = 0x10ca6f
  entropyLength : loadBytes u.external (u.regValue .rsp + 8) 8 = .ok (0 : BitVec 64)
  orderPointer : loadBytes u.external (u.regValue .rsp + 16) 8 = .ok (frameBase s + 272)

end P256.Proofs.Signing.Core.Initialize
