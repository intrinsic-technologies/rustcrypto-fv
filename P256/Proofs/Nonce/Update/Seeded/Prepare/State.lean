import P256.Proofs.Program.Code
import P256.Proofs.Nonce.Update.Seeded.State
import P256.Proofs.SHA256.Interface

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Context [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  drbg : DrbgAt s (initial.regValue .rdi) state
  drbgPointer : s.regValue .rbx = initial.regValue .rdi
  savedPointer : memLoad s.external (scratch initial + 72) 64 = initial.regValue .rdi
  savedValue : memLoad s.external (scratch initial + 64) 64 = initial.regValue .rdi + 32
  descriptors : s.regValue .rbp = initial.regValue .rsi
  savedEnd : memLoad s.external (scratch initial + 80) 64 =
    initial.regValue .rsi + initial.regValue .rdx * 16

structure KeyReady [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a455

structure Keyed [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a4cb
  key : (MemoryRegion.mk (scratch initial).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0)

structure InnerPadded [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a4ed
  key : (MemoryRegion.mk (scratch initial).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x36)

structure CompressionInput [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a55c
  bufferPointer : s.regValue .r12 = scratch initial + 320
  destination : s.regValue .rdi = scratch initial + 320
  source : s.regValue .rsi = scratch initial
  count : s.regValue .rdx = 1
  key : (MemoryRegion.mk (scratch initial).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x36)
  hash : SHA256.HashStateAt s (scratch initial + 320) SHA256.initialHash
  position : s.external[scratch initial + 319]? = some 0
  blocks : loadBytes s.external (scratch initial + 352) 8 = .ok 1

structure Compressed [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a561
  bufferPointer : s.regValue .r12 = scratch initial + 320
  key : (MemoryRegion.mk (scratch initial).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x36)
  inner : HMAC.Sha256StateAt s (scratch initial + 256) (HMAC.keyPad state.key 0x36)

structure OuterPadded [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a58d
  bufferPointer : s.regValue .r12 = scratch initial + 320
  key : (MemoryRegion.mk (scratch initial).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x5c)
  inner : HMAC.Sha256StateAt s (scratch initial + 256) (HMAC.keyPad state.key 0x36)

end P256.Proofs.Nonce.Update.Seeded.Prepare
