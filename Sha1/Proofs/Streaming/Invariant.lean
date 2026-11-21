import Sha1.Proofs.Buffered.Update.Contracts
import Sha1.Proofs.Streaming.Slices
import Sha1.Proofs.Streaming.Loop

namespace Sha1.Proofs.Streaming.UpdateFinalize

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Buffered

structure Frame [Bindings] (initial s : RamState) : Prop where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  df : DirectionFlagUnset s
  stack : stackPtr s = stackPtr initial - 360
  output : stackWord s 0xc0 = initial.regValue .rcx
  pointers : stackWord s 0xc8 = initial.regValue .rdi
  lengths : stackWord s 0xd0 = initial.regValue .rdx
  savedRbx : stackWord s 312 = initial.regValue .rbx
  savedR12 : stackWord s 320 = initial.regValue .r12
  savedR13 : stackWord s 328 = initial.regValue .r13
  savedR14 : stackWord s 336 = initial.regValue .r14
  savedR15 : stackWord s 344 = initial.regValue .r15
  savedRbp : stackWord s 352 = initial.regValue .rbp
  returnSlot : stackWord s 360 = (returnBoundary initial).rip
  memory : MemoryWriteFrame initial s #v[Stack.region initial SliceHash.updateFinalize.minStackBytes]
  grows : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome
  fixed : fixedPart s = fixedPart initial

structure Header [Bindings] (initial : RamState) (inputs : Array Slices.Input)
    (index : Nat) (s : RamState) : Prop extends Frame initial s where
  absorbed : Absorbed (stackPtr s + 0xd8) (Slices.message (inputs.extract 0 index)) s
  rip : s.RIP = if index < inputs.size then 0x101cdd else 0x101dcb
  counters : index < inputs.size →
    s.regValue .r15 = BitVec.ofNat 64 index ∧ s.regValue .r12 = BitVec.ofNat 64 inputs.size

end Sha1.Proofs.Streaming.UpdateFinalize
