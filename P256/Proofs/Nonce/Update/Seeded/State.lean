import P256.Proofs.Nonce.Update.Phases

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Entered [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x10a455
  drbg : DrbgAt s (initial.regValue .rdi) state
  drbgPointer : s.regValue .rbx = initial.regValue .rdi
  savedPointer : memLoad s.external (scratch initial + 72) 64 = initial.regValue .rdi
  savedValue : memLoad s.external (scratch initial + 64) 64 = initial.regValue .rdi + 32
  descriptors : s.regValue .rbp = initial.regValue .rsi
  savedEnd : memLoad s.external (scratch initial + 80) 64 =
    initial.regValue .rsi + initial.regValue .rdx * 16

structure Prepared [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x10a627
  drbg : DrbgAt s (initial.regValue .rdi) state
  hmac : HMAC.HmacStateAt s (scratch initial + 256) state.key ByteArray.empty
  bufferPointer : s.regValue .r12 = scratch initial + 320
  savedPointer : memLoad s.external (scratch initial + 72) 64 = initial.regValue .rdi
  savedValue : memLoad s.external (scratch initial + 64) 64 = initial.regValue .rdi + 32
  descriptors : s.regValue .rbp = initial.regValue .rsi
  savedEnd : memLoad s.external (scratch initial + 80) 64 =
    initial.regValue .rsi + initial.regValue .rdx * 16

structure Absorbed [Bindings] (initial s : RamState) (state : State)
    (seed : ByteArray) : Prop extends FrameState initial s where
  rip : s.RIP = 0x10a849
  drbg : DrbgAt s (initial.regValue .rdi) state
  hmac : HMAC.HmacStateAt s (scratch initial + 256) state.key
    (state.value ++ ⟨#[1]⟩ ++ seed)
  savedPointer : memLoad s.external (scratch initial + 72) 64 = initial.regValue .rdi

end P256.Proofs.Nonce.Update.Seeded
