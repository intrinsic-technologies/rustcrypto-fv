import P256.Proofs.Signing.Wrapper.Hash.Absorb.Interface
import P256.Proofs.HMAC.State

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Short

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Copied [Bindings] (initial start t : RamState) (message : ByteArray) : Prop
    extends Frame initial start t where
  rip : t.RIP = 0x102793
  length : t.regValue .rbp = BitVec.ofNat 64 message.size
  buffer : (MemoryRegion.mk (frameBase initial + 176).toNat message.size).HasBytes
    t.external message
  hash : SHA256.HashStateAt t (frameBase initial + 240) SHA256.initialHash
  count : loadBytes t.external (frameBase initial + 272) 8 = .ok (0#64)

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Short
