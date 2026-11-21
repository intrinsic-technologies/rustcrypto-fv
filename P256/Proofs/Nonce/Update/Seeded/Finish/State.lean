import P256.Proofs.Nonce.Update.Seeded.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Context [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  drbg : DrbgAt s (initial.regValue .rdi) state
  savedPointer : memLoad s.external (scratch initial + 72) 64 = initial.regValue .rdi

structure CopyReady [Bindings] (initial s : RamState) (state : State) (input : ByteArray) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a861
  source : s.regValue .rsi = scratch initial + 256
  destination : s.regValue .rdi = scratch initial + 432
  hashPointer : s.regValue .rbx = scratch initial + 432
  count : s.regValue .rdx = 168
  hmac : HMAC.HmacStateAt s (scratch initial + 256) state.key input

structure Copied [Bindings] (initial s : RamState) (state : State) (input : ByteArray) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a867
  hashPointer : s.regValue .rbx = scratch initial + 432
  hmac : HMAC.HmacStateAt s (scratch initial + 432) state.key input

structure HashReady [Bindings] (initial s : RamState) (state : State) (input : ByteArray) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a890
  hashPointer : s.regValue .rdi = scratch initial + 432
  outputPointer : s.regValue .rsi = scratch initial
  hmac : HMAC.HmacStateAt s (scratch initial + 432) state.key input

structure Hashed [Bindings] (initial s : RamState) (state : State) (input : ByteArray) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a895
  output : (MemoryRegion.mk (scratch initial).toNat 32).HasBytes s.external
    ((Standards.RFC.HMAC.hmac P256.Spec.Operations.hash 64) state.key input)

structure ValueReady [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x10a8dc
  drbgPointer : s.regValue .rdi = initial.regValue .rdi
  drbg : DrbgAt s (initial.regValue .rdi) state

end P256.Proofs.Nonce.Update.Seeded.Finish
