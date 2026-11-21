import P256.Proofs.Nonce.Update.State
import P256.Proofs.HMAC.Interface

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Prepared [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x10a12f
  drbgPointer : s.regValue .rbx = initial.regValue .rdi
  descriptors : s.regValue .rbp = initial.regValue .rsi
  inputCount : s.regValue .r13 = initial.regValue .rdx
  drbg : DrbgAt s (initial.regValue .rdi) state
  hmac : HMAC.HmacStateAt s (scratch initial + 88) state.key ByteArray.empty

structure Absorbed [Bindings] (initial s : RamState) (state : State)
    (input : UpdateInput) : Prop extends FrameState initial s where
  rip : s.RIP = 0x10a39c
  drbg : DrbgAt s (initial.regValue .rdi) state
  hmac : HMAC.HmacStateAt s (scratch initial + 88) state.key
    (state.value ++ ⟨#[0]⟩ ++ input.seed)
  savedPointer : memLoad s.external (scratch initial + 72) 64 = initial.regValue .rdi
  savedValue : memLoad s.external (scratch initial + 64) 64 = initial.regValue .rdi + 32
  savedCount : memLoad s.external (scratch initial + 424) 64 = initial.regValue .rdx
  descriptors : s.regValue .rbp = initial.regValue .rsi
  savedEnd : memLoad s.external (scratch initial + 80) 64 =
    initial.regValue .rsi + initial.regValue .rdx * 16

structure RoundZeroDone [Bindings] (initial s : RamState) (state : State)
    (input : UpdateInput) : Prop extends FrameState initial s where
  rip : s.RIP = 0x10a446
  drbg : DrbgAt s (initial.regValue .rdi) (updateRound 0 input.seed state)
  drbgPointer : s.regValue .rbx = initial.regValue .rdi
  savedPointer : memLoad s.external (scratch initial + 72) 64 = initial.regValue .rdi
  savedValue : memLoad s.external (scratch initial + 64) 64 = initial.regValue .rdi + 32
  savedCount : memLoad s.external (scratch initial + 424) 64 = initial.regValue .rdx
  descriptors : s.regValue .rbp = initial.regValue .rsi
  savedEnd : memLoad s.external (scratch initial + 80) 64 =
    initial.regValue .rsi + initial.regValue .rdx * 16

structure Finished [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x10a8e1
  drbg : DrbgAt s (initial.regValue .rdi) state

end P256.Proofs.Nonce.Update
