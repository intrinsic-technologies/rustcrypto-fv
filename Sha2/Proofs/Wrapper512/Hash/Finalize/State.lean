import Sha2.Proofs.Wrapper512.State
import Sha2.Proofs.Common.SHA512.Mathematics.Padding.Tail
import Sha2.Proofs.Common.SHA512.Mathematics.Padding.Serialization
import Sha2.Proofs.Common.Instructions.Bswap
import Sha2.Proofs.Common.Encoding.PointEncoding

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Encoding
open Sha2.Proofs.Wrapper512

def paddedBuffer (message : ByteArray) : ByteArray :=
  remainderBytes message ++ ⟨#[128]⟩ ++
    ⟨Array.replicate (127 - message.size % 128) 0⟩

def finalPrefix (message : ByteArray) : ByteArray :=
  if message.size % 128 < 112 then
    remainderBytes message ++ ⟨#[128]⟩ ++
      ⟨Array.replicate (111 - message.size % 128) 0⟩
  else
    ⟨Array.replicate 112 0⟩

def finalBlock (message : ByteArray) : ByteArray :=
  finalPrefix message ++ Sha2.Proofs.NIST.Encoding.natToOctets 16 (8 * message.size)

abbrev lengthOffset (v : Variant) (form : Form) : Nat :=
  match form with
  | .slices => 0x32a
  | .digest => 0x243
  | .reset stage => if stage.val = 2 then (match v with | .sha384 => 0x818 | .sha512 => 0x838 | .sha512_224 => 0x7f8 | .sha512_256 => 0x7f8) else 0x4d1
  | .finalizeIntoReset second => if second then (match v with | .sha384 => 0x6a9 | .sha512 => 0x6c9 | .sha512_224 => 0x68b | .sha512_256 => 0x68b) else 0x308
  | .traitFinalizeIntoReset second => if second then (match v with | .sha384 => 0x744 | .sha512 => 0x764 | .sha512_224 => 0x724 | .sha512_256 => 0x724) else 0x398

abbrev storeOffset (v : Variant) (form : Form) : Nat :=
  match form with
  | .slices => 0x343
  | .digest => 0x25c
  | .reset stage => if stage.val = 2 then (match v with | .sha384 => 0x825 | .sha512 => 0x845 | .sha512_224 => 0x805 | .sha512_256 => 0x805) else 0x4dd
  | .finalizeIntoReset second => if second then (match v with | .sha384 => 0x6c2 | .sha512 => 0x6e2 | .sha512_224 => 0x6a4 | .sha512_256 => 0x6a4) else 0x315
  | .traitFinalizeIntoReset second => if second then (match v with | .sha384 => 0x75d | .sha512 => 0x77d | .sha512_224 => 0x73d | .sha512_256 => 0x73d) else 0x3a5

abbrev storeEndOffset (v : Variant) (form : Form) : Nat :=
  match form with
  | .slices => 0x353
  | .digest => 0x266
  | .reset stage => if stage.val = 2 then (match v with | .sha384 => 0x82f | .sha512 => 0x84f | .sha512_224 => 0x80f | .sha512_256 => 0x80f) else 0x4e7
  | .finalizeIntoReset second => if second then (match v with | .sha384 => 0x6d2 | .sha512 => 0x6f2 | .sha512_224 => 0x6b4 | .sha512_256 => 0x6b4) else 0x325
  | .traitFinalizeIntoReset second => if second then (match v with | .sha384 => 0x76d | .sha512 => 0x78d | .sha512_224 => 0x74d | .sha512_256 => 0x74d) else 0x3b5

abbrev lowLengthRegister (v : Variant) (form : Form) : Syntax.Reg :=
  match form with
  | .slices => .rax
  | .digest => .rax
  | .reset stage => if stage.val = 2 then .r12 else .rbp
  | .finalizeIntoReset second => if second then .rax else .r13
  | .traitFinalizeIntoReset second => if second then .rax else (match v with | .sha384 => .r13 | .sha512 => .r12 | .sha512_224 => .r13 | .sha512_256 => .r13)

abbrev highCountRegister (v : Variant) (form : Form) : Syntax.Reg :=
  match form with
  | .slices => .r15
  | .digest => .r12
  | .reset stage => if stage.val = 2 then .r15 else .r15
  | .finalizeIntoReset second => if second then .r15 else (match v with | .sha384 => .r15 | .sha512 => .r15 | .sha512_224 => .r12 | .sha512_256 => .r12)
  | .traitFinalizeIntoReset second => if second then .r15 else (match v with | .sha384 => .r12 | .sha512 => .r15 | .sha512_224 => .r12 | .sha512_256 => .r12)

abbrev lowCountRegister (v : Variant) (form : Form) : Syntax.Reg :=
  match form with
  | .slices => .r12
  | .digest => .r13
  | .reset stage => if stage.val = 2 then .r14 else .r14
  | .finalizeIntoReset second => if second then .r12 else .r14
  | .traitFinalizeIntoReset second => if second then .r12 else (match v with | .sha384 => .r15 | .sha512 => .r14 | .sha512_224 => .r15 | .sha512_256 => .r15)

abbrev tailRegister (v : Variant) (form : Form) : Syntax.Reg :=
  match form with
  | .slices => .r13
  | .digest => .rbp
  | .reset stage => if stage.val = 2 then .r12 else .rbp
  | .finalizeIntoReset second => if second then .r13 else .r13
  | .traitFinalizeIntoReset second => if second then .r13 else (match v with | .sha384 => .r13 | .sha512 => .r12 | .sha512_224 => .r13 | .sha512_256 => .r13)

abbrev paddingRegister (v : Variant) (form : Form) : Syntax.Reg :=
  match form with
  | .slices => .rbx
  | .digest => .r15
  | .reset stage => if stage.val = 2 then .rbx else .rbx
  | .finalizeIntoReset second => if second then .r14 else .rbx
  | .traitFinalizeIntoReset second => if second then .r14 else (match v with | .sha384 => .r14 | .sha512 => .rbx | .sha512_224 => .r14 | .sha512_256 => .r14)

abbrev branchOffset (v : Variant) (form : Form) : Nat :=
  match form with
  | .slices => 0x271
  | .digest => 0x193
  | .reset stage => if stage.val = 2 then (match v with | .sha384 => 0x763 | .sha512 => 0x783 | .sha512_224 => 0x743 | .sha512_256 => 0x743) else 0x41c
  | .finalizeIntoReset second => if second then (match v with | .sha384 => 0x5c9 | .sha512 => 0x5e9 | .sha512_224 => 0x5ab | .sha512_256 => 0x5ab) else 0x250
  | .traitFinalizeIntoReset second => if second then (match v with | .sha384 => 0x68b | .sha512 => 0x6ab | .sha512_224 => 0x66b | .sha512_256 => 0x66b) else 0x2bb

abbrev countsShifted (form : Form) : Bool :=
  match form with
  | .reset _ | .finalizeIntoReset false | .traitFinalizeIntoReset false => true
  | _ => false

abbrev lowCountValue (form : Form) (message : ByteArray) : BitVec 64 :=
  if countsShifted form then BitVec.ofNat 64 (message.size / 128) <<< 10
  else BitVec.ofNat 64 (message.size / 128)

abbrev highCountValue (form : Form) (message : ByteArray) : BitVec 64 :=
  if countsShifted form then
    (BitVec.ofNat 64 ((message.size / 128) / 2^64) ++
      BitVec.ofNat 64 (message.size / 128)).extractLsb' 54 64
  else BitVec.ofNat 64 ((message.size / 128) / 2^64)

abbrev hashPointerState (v : Variant) (form : Form) (initial s : RamState) : Prop :=
  match form with
  | .slices | .digest => s.regValue .r14 = stackPtr initial - 472
  | .reset _ | .finalizeIntoReset false => True
  | .finalizeIntoReset true | .traitFinalizeIntoReset true =>
      s.regValue .rbx = stackPtr initial - BitVec.ofNat 64 form.finalMemory.hash
  | .traitFinalizeIntoReset false =>
      s.regValue (if v = .sha512 then .rbp else .rbx) =
        stackPtr initial - BitVec.ofNat 64 form.finalMemory.hash ∧
      s.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx

structure HashAt [Bindings] (v : Variant) (initial s : RamState)
    (hash : Array UInt64) (form : Form := .slices) : Prop extends Preserved v initial s form where
  hashWords : HashStateAt s (stackPtr initial - BitVec.ofNat 64 form.finalMemory.hash) hash
  hashPointer : hashPointerState v form initial s

structure Working [Bindings] (v : Variant) (initial s : RamState)
    (message : ByteArray) (hash : Array UInt64) (form : Form := .slices) : Prop
    extends HashAt v initial s hash form where
  blocks : s.regValue (lowCountRegister v form) = lowCountValue form message
  blocksHigh : s.regValue (highCountRegister v form) = highCountValue form message
  tailLength : s.regValue (tailRegister v form) = BitVec.ofNat 64 (message.size % 128)

structure Padded [Bindings] (v : Variant) (initial s : RamState)
    (message : ByteArray) (form : Form := .slices) : Prop
    extends Working v initial s message (compressBlocks v.initialHash message) form where
  rip : s.RIP = v.pc (branchOffset v form) form
  bytes : (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat, 128⟩ : MemoryRegion).HasBytes
    s.external (paddedBuffer message)
  paddingLength : s.regValue (paddingRegister v form) = BitVec.ofNat 64 (127 - message.size % 128)

structure LengthReady [Bindings] (v : Variant) (initial s : RamState)
    (message : ByteArray) (hash : Array UInt64) (form : Form := .slices) : Prop
    extends HashAt v initial s hash form where
  rip : s.RIP = v.pc (storeOffset v form) form
  prefixBytes : (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat, 112⟩ : MemoryRegion).HasBytes
    s.external (finalPrefix message)
  lengthLow : s.regValue (lowLengthRegister v form) =
    bswap64 (BitVec.ofNat 64 (8 * message.size))
  lengthHigh : s.regValue (highCountRegister v form) = bswap64 (BitVec.ofNat 64 ((8 * message.size) / 2^64))

theorem paddedBuffer_size (message : ByteArray) : (paddedBuffer message).size = 128 := by
  simp only [paddedBuffer, ByteArray.size_append, remainderBytes_size]
  simp only [ByteArray.size, Array.size_replicate]
  change message.data.size % 128 + 1 + (127 - message.data.size % 128) = 128
  have h := Nat.mod_lt message.size (by decide : 0 < 128)
  omega

theorem finalPrefix_size (message : ByteArray) : (finalPrefix message).size = 112 := by
  unfold finalPrefix
  have hm : message.size = message.data.size := rfl
  split
  · rename_i hsmall
    simp only [ByteArray.size_append, remainderBytes_size]
    simp only [ByteArray.size, Array.size_replicate]
    change message.data.size % 128 + 1 + (111 - message.data.size % 128) = 112
    have hdata : message.data.size % 128 < 112 := by
      simpa only [hm] using hsmall
    have h' : message.data.size % 128 < 128 := Nat.mod_lt _ (by decide)
    omega
  · rename_i hlarge
    simp only [ByteArray.size, Array.size_replicate]

theorem finalBlock_size (message : ByteArray) : (finalBlock message).size = 128 := by
  simp only [finalBlock, ByteArray.size_append, finalPrefix_size,
    Sha2.Proofs.Common.Encoding.natToOctets_size]

end Sha2.Proofs.Wrapper512.Hash.Finalize
