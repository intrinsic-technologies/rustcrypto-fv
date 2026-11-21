import P256.Proofs.Nonce.UpdateValue.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure CallReady [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x10abdd
  valuePointer : s.regValue .rbx = initial.regValue .rdi + 32
  hashPointer : s.regValue .rdi = scratch initial + 272
  outputPointer : s.regValue .rsi = scratch initial + 8
  drbg : DrbgAt s (initial.regValue .rdi) state
  hmac : HMAC.HmacStateAt s (scratch initial + 272) state.key state.value

structure Called [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (state : State) : Prop extends P256.Proofs.Program.ScalarFrame.FrameState initial s 64 1168 496 where
  pre : HMAC.HmacFinalizePre s boundary state.key state.value
  valuePointer : s.regValue .rbx = initial.regValue .rdi + 32
  hashPointer : s.regValue .rdi = stackPtr initial - 216
  outputPointer : s.regValue .rsi = stackPtr initial - 480
  drbg : DrbgAt s (initial.regValue .rdi) state
  ret : (returnBoundary s).rip = 0x10abe2

structure Finalized [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x10abe2
  valuePointer : s.regValue .rbx = initial.regValue .rdi + 32
  drbg : DrbgAt s (initial.regValue .rdi) state
  output : (MemoryRegion.mk (scratch initial + 8).toNat 32).HasBytes s.external
    (Standards.RFC.HMAC.hmac P256.Spec.Operations.hash 64 state.key state.value)

end P256.Proofs.Nonce.UpdateValue.Finish
