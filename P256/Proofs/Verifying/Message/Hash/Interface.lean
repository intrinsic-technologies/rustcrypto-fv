import P256.Proofs.Verifying.Message.Initialize

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Result [Bindings] (initial t : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) : Prop extends Frame initial t where
  execution : ∃ fuel, Advances boundary fuel initial t
  rip : t.RIP = 0x10d957
  digest : (MemoryRegion.mk (frameBase initial + 424).toNat 32).HasBytes
    t.external (Operations.hash message)
  savedKey : memLoad t.external (frameBase initial + 456) 64 = initial.regValue .rsi
  savedOutput : memLoad t.external (frameBase initial + 384) 64 = initial.regValue .rdi
  savedSignature : memLoad t.external (frameBase initial + 464) 64 = initial.regValue .r8
  stackFrame : MemoryWriteFrame initial t #v[Stack.region initial 9992]

def Correct : Prop :=
  ∀ [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {message : ByteArray},
    Message.Pre initial boundary message → Initialized initial s boundary →
    ∃ t, Result initial t boundary message

end P256.Proofs.Verifying.Message.Hash
