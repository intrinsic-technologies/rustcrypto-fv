import P256.Proofs.Signing.Wrapper.Hash.Absorb.Interface

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Result [Bindings] (initial start t : RamState)
    (message : ByteArray) : Prop extends Frame initial start t where
  rip : t.RIP = 0x102a19
  digest : (MemoryRegion.mk (frameBase initial + 0).toNat 32).HasBytes
    t.external (Operations.hash message)

def Correct : Prop :=
  ∀ [Bindings] {initial start s : RamState} {secret message : ByteArray},
    HashEntry initial start secret message → Absorb.Result initial start s message →
    ∃ t, Result initial start t message

end P256.Proofs.Signing.Wrapper.Hash.Finalize
