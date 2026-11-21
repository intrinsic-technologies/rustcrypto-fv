import P256.Proofs.Nonce.Update.Phases
import P256.Proofs.Nonce.UpdateValue.Bytes

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

structure Tagged [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x10a261
  drbg : DrbgAt s (initial.regValue .rdi) state
  hmac : HMAC.HmacStateAt s (scratch initial + 88) state.key (state.value ++ ⟨#[0]⟩)
  savedPointer : memLoad s.external (scratch initial + 72) 64 = initial.regValue .rdi
  savedValue : memLoad s.external (scratch initial + 64) 64 = initial.regValue .rdi + 32
  descriptors : s.regValue .rbp = initial.regValue .rsi
  inputCount : s.regValue .r13 = initial.regValue .rdx

end P256.Proofs.Nonce.Update.Absorb
