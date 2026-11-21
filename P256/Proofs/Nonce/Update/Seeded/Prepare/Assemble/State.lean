import P256.Proofs.Nonce.Update.Seeded.Prepare.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Prepare.Assemble

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure InnerCopied [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a5a5
  bufferPointer : s.regValue .r12 = scratch initial + 320
  key : (MemoryRegion.mk (scratch initial).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x5c)
  inner : HMAC.Sha256StateAt s (scratch initial + 496) (HMAC.keyPad state.key 0x36)

structure CopyReady [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a60c
  bufferPointer : s.regValue .r12 = scratch initial + 320
  hmac : HMAC.HmacStateAt s (scratch initial + 432) state.key ByteArray.empty

end P256.Proofs.Nonce.Update.Seeded.Prepare.Assemble
