import P256.Proofs.Nonce.UpdateValue.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Entered [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x10ab06
  valuePointer : s.regValue .rbx = initial.regValue .rdi + 32
  bufferPointer : s.regValue .r14 = scratch initial + 168
  position : s.regValue .r15 = 0
  drbg : DrbgAt s (initial.regValue .rdi) state
  hmac : HMAC.HmacStateAt s (scratch initial + 104) state.key ByteArray.empty

structure Buffered [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x10ab96
  valuePointer : s.regValue .rbx = initial.regValue .rdi + 32
  drbg : DrbgAt s (initial.regValue .rdi) state
  hmac : HMAC.HmacStateAt s (scratch initial + 104) state.key state.value

end P256.Proofs.Nonce.UpdateValue.Absorb
