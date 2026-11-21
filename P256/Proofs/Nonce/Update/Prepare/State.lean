import P256.Proofs.Nonce.Update.Phases
import P256.Proofs.HMAC.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Context [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  drbgPointer : s.regValue .rbx = initial.regValue .rdi
  descriptors : s.regValue .rbp = initial.regValue .rsi
  inputCount : s.regValue .r13 = initial.regValue .rdx
  drbg : DrbgAt s (initial.regValue .rdi) state

structure Keyed [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x109fca
  key : (MemoryRegion.mk (scratch initial + 88).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0)

structure InnerPadded [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x109fee
  key : (MemoryRegion.mk (scratch initial + 88).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x36)

structure Compressed [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a061
  key : (MemoryRegion.mk (scratch initial + 88).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x36)
  inner : HMAC.Sha256StateAt s (scratch initial + 256) (HMAC.keyPad state.key 0x36)

structure OuterPadded [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a08e
  key : (MemoryRegion.mk (scratch initial + 88).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x5c)
  inner : HMAC.Sha256StateAt s (scratch initial + 256) (HMAC.keyPad state.key 0x36)

end P256.Proofs.Nonce.Update.Prepare
