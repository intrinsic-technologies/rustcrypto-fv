import P256.Proofs.Nonce.UpdateValue.Prepare.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare.Assemble

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure InnerCopied [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10aa73
  bufferPointer : s.regValue .r14 = scratch initial + 168
  key : (MemoryRegion.mk (scratch initial + 8).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x5c)
  inner : HMAC.Sha256StateAt s (scratch initial + 336) (HMAC.keyPad state.key 0x36)

structure CopyReady [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10aaed
  bufferPointer : s.regValue .r14 = scratch initial + 168
  destination : s.regValue .rdi = scratch initial + 104
  source : s.regValue .rsi = scratch initial + 272
  count : s.regValue .rdx = 168
  hmac : HMAC.HmacStateAt s (scratch initial + 272) state.key ByteArray.empty

end P256.Proofs.Nonce.UpdateValue.Prepare.Assemble
