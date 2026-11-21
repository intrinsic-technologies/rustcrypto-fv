import P256.Proofs.Nonce.Update.Prepare.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure CompressionInput [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a05c
  destination : s.regValue .rdi = scratch initial + 320
  source : s.regValue .rsi = scratch initial + 88
  count : s.regValue .rdx = 1
  key : (MemoryRegion.mk (scratch initial + 88).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x36)
  hash : SHA256.HashStateAt s (scratch initial + 320) P256.Proofs.SHA256.initialHash
  position : s.external[scratch initial + 319]? = some 0
  blocks : loadBytes s.external (scratch initial + 352) 8 = .ok 1

end P256.Proofs.Nonce.Update.Prepare
