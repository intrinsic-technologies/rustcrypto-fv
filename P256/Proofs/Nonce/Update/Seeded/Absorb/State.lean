import P256.Proofs.Nonce.Update.Seeded.State
import P256.Proofs.Nonce.Update.Absorb.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Context [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  drbg : DrbgAt s (initial.regValue .rdi) state
  bufferPointer : s.regValue .r12 = scratch initial + 320
  savedPointer : memLoad s.external (scratch initial + 72) 64 = initial.regValue .rdi
  savedValue : memLoad s.external (scratch initial + 64) 64 = initial.regValue .rdi + 32
  savedEnd : memLoad s.external (scratch initial + 80) 64 =
    initial.regValue .rsi + initial.regValue .rdx * 16

structure Loop [Bindings] (initial s : RamState) (state : State) (input : ByteArray)
    (index : Nat) : Prop extends Context initial s state where
  rip : s.RIP = 0x10a78d
  current : s.regValue .rbp = initial.regValue .rsi + BitVec.ofNat 64 (16 * index)
  hashPointer : s.regValue .r14 = scratch initial + 384
  copyPointer : s.regValue .r13 = 0x11c930
  hmac : HMAC.HmacStateAt s (scratch initial + 256) state.key input

namespace Prefix

structure Entered [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a643
  valuePointer : s.regValue .rcx = initial.regValue .rdi + 32
  position : s.regValue .r15 = 0
  descriptors : s.regValue .rbp = initial.regValue .rsi
  hmac : HMAC.HmacStateAt s (scratch initial + 256) state.key ByteArray.empty

structure Copied [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a665
  position : s.regValue .r15 = 0
  descriptors : s.regValue .rbp = initial.regValue .rsi
  hmac : HMAC.HmacStateAt s (scratch initial + 256) state.key ByteArray.empty
  value : (MemoryRegion.mk (scratch initial + 320).toNat 32).HasBytes s.external state.value

end Prefix

end P256.Proofs.Nonce.Update.Seeded.Absorb
