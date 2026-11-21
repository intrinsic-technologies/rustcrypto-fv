import P256.Proofs.Nonce.Update.Absorb.State
import P256.Proofs.Nonce.Update.Absorb.SeedCopy
import P256.Proofs.Nonce.Update.Prepare.CompressionMemory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Context [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  drbg : DrbgAt s (initial.regValue .rdi) state
  savedPointer : memLoad s.external (scratch initial + 72) 64 = initial.regValue .rdi
  savedValue : memLoad s.external (scratch initial + 64) 64 = initial.regValue .rdi + 32
  savedCount : memLoad s.external (scratch initial + 424) 64 = initial.regValue .rdx
  descriptors : s.regValue .rbp = initial.regValue .rsi
  savedEnd : memLoad s.external (scratch initial + 80) 64 = initial.regValue .rsi + initial.regValue .rdx * 16

structure Loop [Bindings] (initial s : RamState) (state : State) (input : ByteArray)
    (index : Nat) : Prop extends Context initial s state where
  rip : s.RIP = 0x10a2c3
  current : s.regValue .r14 = initial.regValue .rsi + BitVec.ofNat 64 (16 * index)
  hmac : HMAC.HmacStateAt s (scratch initial + 88) state.key input

end P256.Proofs.Nonce.Update.Absorb.Seeded
