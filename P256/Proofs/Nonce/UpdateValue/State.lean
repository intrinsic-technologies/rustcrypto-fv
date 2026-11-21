import P256.Proofs.Nonce.UpdateValue.PrologueFrame
import P256.Proofs.Nonce.UpdateValue.Bytes

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

abbrev FrameState [Bindings] (initial s : RamState) : Prop := ScalarFrame.FrameState initial s 64 1168 488

def scratch (s : RamState) : BitVec 64 := stackPtr s - 488

structure Saved [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x10a911
  statePointer : s.regValue .rdi = initial.regValue .rdi
  drbg : DrbgAt s (initial.regValue .rdi) state

structure Prepared [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x10aaf3
  statePointer : s.regValue .rbx = initial.regValue .rdi
  bufferPointer : s.regValue .r14 = scratch initial + 168
  drbg : DrbgAt s (initial.regValue .rdi) state
  hmac : HMAC.HmacStateAt s (scratch initial + 104) state.key ByteArray.empty

structure Absorbed [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x10abb1
  valuePointer : s.regValue .rbx = initial.regValue .rdi + 32
  hmacPointer : s.regValue .r14 = scratch initial + 272
  drbg : DrbgAt s (initial.regValue .rdi) state
  hmac : HMAC.HmacStateAt s (scratch initial + 272) state.key state.value

end P256.Proofs.Nonce.UpdateValue
