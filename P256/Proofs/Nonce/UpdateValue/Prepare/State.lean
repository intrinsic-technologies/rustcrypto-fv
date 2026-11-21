import P256.Proofs.Nonce.UpdateValue.State
import P256.Proofs.HMAC.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Context [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  statePointer : s.regValue .rbx = initial.regValue .rdi
  drbg : DrbgAt s (initial.regValue .rdi) state

structure Keyed [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a98b
  key : (MemoryRegion.mk (scratch initial + 8).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0)

structure InnerPadded [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a9ae
  key : (MemoryRegion.mk (scratch initial + 8).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x36)

structure CompressionInput [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10aa1f
  destination : s.regValue .rdi = scratch initial + 168
  source : s.regValue .rsi = scratch initial + 8
  count : s.regValue .rdx = 1
  bufferPointer : s.regValue .r14 = scratch initial + 168
  key : (MemoryRegion.mk (scratch initial + 8).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x36)
  hash : SHA256.HashStateAt s (scratch initial + 168) P256.Proofs.SHA256.initialHash
  position : s.external[scratch initial + 167]? = some 0
  blocks : loadBytes s.external (scratch initial + 200) 8 = .ok 1

structure Compressed [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10aa24
  bufferPointer : s.regValue .r14 = scratch initial + 168
  key : (MemoryRegion.mk (scratch initial + 8).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x36)
  inner : HMAC.Sha256StateAt s (scratch initial + 104) (HMAC.keyPad state.key 0x36)

structure OuterPadded [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10aa5e
  bufferPointer : s.regValue .r14 = scratch initial + 168
  key : (MemoryRegion.mk (scratch initial + 8).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x5c)
  inner : HMAC.Sha256StateAt s (scratch initial + 104) (HMAC.keyPad state.key 0x36)

end P256.Proofs.Nonce.UpdateValue.Prepare
