import P256.Proofs.Nonce.Update.Absorb.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem state_readable [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (frame : FrameState initial s) {offset len : Nat} (bound : offset + len ≤ 64) :
    MemReadable s (initial.regValue .rdi + BitVec.ofNat 64 offset) len := by
  apply readable_of_grow ?_ frame.allocated
  have low : (initial.regValue .rdi).toNat + 64 < 2^32 := pre.stateBounded
  have address : (initial.regValue .rdi + BitVec.ofNat 64 offset).toNat =
      (initial.regValue .rdi).toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64),
      Nat.mod_eq_of_lt (by omega)]
  apply memoryRegion_memReadable pre.stateBounded pre.stateAllocated
  · rw [address]
    change (initial.regValue .rdi).toNat ≤ _
    omega
  · rw [address]
    change (initial.regValue .rdi).toNat + offset + len ≤ (initial.regValue .rdi).toNat + 64
    omega

structure Entered [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x10a15c
  valuePointer : s.regValue .rsi = initial.regValue .rdi + 32
  bufferPointer : s.regValue .r14 = scratch initial + 152
  position : s.regValue .r15 = 0
  drbg : DrbgAt s (initial.regValue .rdi) state
  hmac : HMAC.HmacStateAt s (scratch initial + 88) state.key ByteArray.empty
  savedPointer : memLoad s.external (scratch initial + 72) 64 = initial.regValue .rdi
  savedValue : memLoad s.external (scratch initial + 64) 64 = initial.regValue .rdi + 32
  descriptors : s.regValue .rbp = initial.regValue .rsi
  inputCount : s.regValue .r13 = initial.regValue .rdx

structure Copied [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x10a17e
  position : s.regValue .r15 = 0
  drbg : DrbgAt s (initial.regValue .rdi) state
  hmac : HMAC.HmacStateAt s (scratch initial + 88) state.key ByteArray.empty
  value : (MemoryRegion.mk (scratch initial + 152).toNat 32).HasBytes s.external state.value
  savedPointer : memLoad s.external (scratch initial + 72) 64 = initial.regValue .rdi
  savedValue : memLoad s.external (scratch initial + 64) 64 = initial.regValue .rdi + 32
  descriptors : s.regValue .rbp = initial.regValue .rsi
  inputCount : s.regValue .r13 = initial.regValue .rdx

end P256.Proofs.Nonce.Update.Absorb.Prefix
