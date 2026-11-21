import Sha2.Proofs.Common.SHA256.Finalize.Layout
import Sha2.Proofs.Common.SHA256.Hasher
import Sha2.Proofs.Common.Machine.ExecutionState
import Sha2.Proofs.Wrapper.Hash.Finalize.Mathematics

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

abbrev paddedBuffer := Sha2.Proofs.Wrapper.Hash.Finalize.paddedBuffer
abbrev finalPrefix := Sha2.Proofs.Wrapper.Hash.Finalize.finalPrefix
abbrev finalBlock := Sha2.Proofs.Wrapper.Hash.Finalize.finalBlock

def countValue (L : Layout) (message : ByteArray) : BitVec 64 :=
  if L.variant.registers.preShifted then BitVec.ofNat 64 (message.size / 64) <<< 9
    else BitVec.ofNat 64 (message.size / 64)

structure Prepared (L : Layout) (sp : BitVec 64) (message : ByteArray)
    (s : RamState) : Prop where
  rip : s.RIP = L.entry
  rsp : stackPtr s = sp
  hasher : HasherAt s (L.buffer sp) message L.hashVariant.initialHash
  tailLength : (.reg L.variant.registers.tail : Operand 64).read s =
    BitVec.ofNat 64 (message.size % 64)
  blocks : (.reg L.variant.registers.blocks : Operand 64).read s = countValue L message
  hashPointer : L.variant.needsHashPointer = true →
    (.reg L.variant.hashReg : Operand 64).read s = L.hash sp

structure PhaseFrame (L : Layout) (sp : BitVec 64) (before after : RamState) : Prop where
  memory : MemoryWriteFrame before after (footprint L sp)
  registers : ∀ r : BitVec 5, r.toNat < 16 → r ∉ L.variant.clobbered →
    (.reg r : Operand 64).read after = (.reg r : Operand 64).read before

structure Preserved [Bindings] (L : Layout) (initial before current : RamState)
    {n : Nat} (regions : Vector MemoryRegion n) : Prop where
  state : ExecutionState initial current regions
  rsp : stackPtr current = L.sp initial
  frame : PhaseFrame L (L.sp initial) before current

structure Padded [Bindings] (L : Layout) (initial before current : RamState)
    {n : Nat} (regions : Vector MemoryRegion n) (message : ByteArray) : Prop
    extends Preserved L initial before current regions where
  rip : current.RIP = L.branch
  hashWords : HashStateAt current (L.hash (L.sp initial))
    (compressBlocks L.hashVariant.initialHash message)
  tailLength : (.reg L.variant.registers.tail : Operand 64).read current =
    BitVec.ofNat 64 (message.size % 64)
  blocks : (.reg L.variant.registers.blocks : Operand 64).read current = countValue L message
  paddingLength : (.reg L.variant.padReg : Operand 64).read current =
    BitVec.ofNat 64 (63 - message.size % 64)
  hashPointer : L.variant.needsHashPointer = true →
    (.reg L.variant.hashReg : Operand 64).read current = L.hash (L.sp initial)
  bytes : (⟨(L.buffer (L.sp initial)).toNat, 64⟩ : MemoryRegion).HasBytes
    current.external (paddedBuffer message)

structure HashAt [Bindings] (L : Layout) (initial before current : RamState)
    {n : Nat} (regions : Vector MemoryRegion n) (hash : Array UInt32) : Prop
    extends Preserved L initial before current regions where
  hashWords : HashStateAt current (L.hash (L.sp initial)) hash
  hashPointer : L.variant ≠ .finalizeFirst →
    (.reg L.variant.hashReg : Operand 64).read current = L.hash (L.sp initial)

structure Working [Bindings] (L : Layout) (initial before current : RamState)
    {n : Nat} (regions : Vector MemoryRegion n) (message : ByteArray)
    (hash : Array UInt32) : Prop extends HashAt L initial before current regions hash where
  tailLength : (.reg L.variant.registers.tail : Operand 64).read current =
    BitVec.ofNat 64 (message.size % 64)
  blocks : (.reg L.variant.registers.blocks : Operand 64).read current = countValue L message

structure LengthReady [Bindings] (L : Layout) (initial before current : RamState)
    {n : Nat} (regions : Vector MemoryRegion n) (message : ByteArray)
    (hash : Array UInt32) : Prop extends HashAt L initial before current regions hash where
  rip : current.RIP = L.lastHead
  prefixBytes : (⟨(L.buffer (L.sp initial)).toNat, 56⟩ : MemoryRegion).HasBytes
    current.external (finalPrefix message)
  lengthWord : (.reg L.variant.registers.tail : Operand 64).read current =
    Common.Instructions.bswap64 (BitVec.ofNat 64 (8 * message.size))

structure Finalized [Bindings] (L : Layout) (initial before current : RamState)
    {n : Nat} (regions : Vector MemoryRegion n) (message : ByteArray) : Prop
    extends Preserved L initial before current regions where
  rip : current.RIP = L.exit
  hashPointer : (.reg L.variant.hashReg : Operand 64).read current = L.hash (L.sp initial)
  digest : ∃ hash, HashStateAt current (L.hash (L.sp initial)) hash ∧
    L.hashVariant.serializeHash hash = L.hashVariant.hash message

end Sha2.Proofs.Common.SHA256.Finalize
