import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Read
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Inputs
import Hkdf.Proofs.Common.Encoding.Serialize.Stack

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem descriptorWords [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {length : Nat} {key info : ByteArray} {ptr : BitVec 64}
    (pre : ExpandPre entry boundary key info ptr length) (positive : 0 < length)
    (limit : length ≤ 8160) (saved : SavedFrame entry s boundary length)
    (cursor : s.regValue .r13 = entry.regValue .rsi) :
    MemReadable s (s.regValue .r13) 8 ∧ MemReadable s (s.regValue .r13 + 8) 8 ∧
      memLoad s.external (s.regValue .r13) 64 = ptr ∧ inputLength s = BitVec.ofNat 64 info.size := by
  let table := entry.regValue .rsi
  have bound := pre.call.readsBounded (registerRegion entry .rsi 16) (by simp)
  have alloc := pre.call.readsAllocated (registerRegion entry .rsi 16) (by simp)
  have hi : table.toNat + 16 < 2^32 := bound
  have read (offset : Nat) (le : offset + 8 ≤ 16) :
      MemReadable s (table + BitVec.ofNat 64 offset) 8 := by
    have addr : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show offset < 2^64 by omega),
        Nat.mod_eq_of_lt (by omega)]
    apply Encoding.Serialize.readable_of_grow (t := s) _ saved.allocated
    apply memoryRegion_memReadable bound alloc
    · change table.toNat ≤ _
      rw [addr]
      omega
    · change _ ≤ table.toNat + 16
      rw [addr]
      omega
  obtain ⟨_, ptrWord, lenWord, _⟩ := roundInputs pre saved.frame positive limit
  change _ ∧ _ ∧ _ ∧ memLoad s.external (s.regValue .r13 + 8) 64 = _
  rw [cursor]
  exact ⟨by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using read 0 (by decide),
    read 8 (by decide), ptrWord, lenWord⟩

theorem bufferedBytes {s : RamState} {key previous : ByteArray}
    (active : HmacAt s (stackPtr s + 272) key previous) (small : previous.size < 64) :
    bufferIndex s = BitVec.ofNat 64 previous.size := by
  have h := active.inner.tailLength
  simp only [ByteArray.size_append, HMAC.xorPad_keyBlock_size,
    BitVec.add_assoc, BitVec.reduceAdd] at h
  have pos : (64 + previous.size) % 64 = previous.size := by omega
  rw [pos] at h
  unfold bufferIndex
  change (memLoad s.external (stackPtr s + 335) 8).setWidth 64 = _
  rw [memLoad_8]
  change ((s.external[stackPtr s + (335#64)]?).getD 0).toBitVec.setWidth 64 = _
  rw [h]
  simp only [Option.getD_some, UInt8.toBitVec_ofNat']
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

end Hkdf.Proofs.NewExpand.Expand.Info
