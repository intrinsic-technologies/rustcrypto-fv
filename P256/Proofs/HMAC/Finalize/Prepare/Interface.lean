import P256.Proofs.HMAC.Finalize.Interface

open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure OuterReady [Bindings] (initial s : RamState) (key input : ByteArray) : Prop
    extends ScalarFrame.FrameState initial s 0 672 328 where
  rip : s.RIP = 0x100f9b
  outputPointer : s.regValue .rbx = initial.regValue .rsi
  sourcePointer : s.regValue .r15 = initial.regValue .rdi
  state : HmacStateAt s (initial.regValue .rdi) key input
  outer : Sha256StateAt s (stackPtr initial - 152#64) (keyPad key 0x5c)

structure CopyReady [Bindings] (initial s : RamState) (key input : ByteArray) : Prop
    extends ScalarFrame.FrameState initial s 0 672 328 where
  rip : s.RIP = 0x100fb4
  outputPointer : s.regValue .rbx = initial.regValue .rsi
  inputPointer : s.regValue .rsi = initial.regValue .rdi + 64
  destinationPointer : s.regValue .rdi = stackPtr s + 72
  countRegister : s.regValue .rcx = 13
  inner : Sha256StateAt s (initial.regValue .rdi + 64) (keyPad key 0x36 ++ input)
  outer : Sha256StateAt s (stackPtr initial - 152#64) (keyPad key 0x5c)

end P256.Proofs.HMAC.Finalize.Prepare
