import Hkdf.Proofs.Common.State
import Hkdf.Proofs.Common.Streaming
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Footprint

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Counter

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.SHA256

abbrev singletonByte (b : UInt8) : ByteArray := ⟨#[b]⟩

abbrev innerMessage (key message : ByteArray) : ByteArray :=
  HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message

structure Buffered (entry s : RamState) (key message : ByteArray) : Prop where
  words : HashStateAt s (base entry + 336) (compressBlocks initialHash (innerMessage key message))
  tail : (area entry 272 ((innerMessage key message).size % 64)).HasBytes
    s.external (remainderBytes (innerMessage key message))
  blocks : loadBytes s.external (base entry + 368) 8 = .ok (BitVec.ofNat 64 ((innerMessage key message).size / 64))
  outerWords : HashStateAt s (base entry + 376)
    (compressBlocks initialHash (HMAC.xorPad (HMAC.keyBlock key) 0x5c))
  outerBlocks : loadBytes s.external (base entry + 408) 8 = .ok 1

private theorem hash_address (p : BitVec 64) : p + 272 + 64 = p + 336 := by bv_omega
theorem tail_address (p : BitVec 64) : p + 272 + 63 = p + 335 := by bv_omega
private theorem blocks_address (p : BitVec 64) : p + 272 + 96 = p + 368 := by bv_omega
private theorem outer_address (p : BitVec 64) : p + 272 + 104 = p + 376 := by bv_omega
private theorem outer_blocks_address (p : BitVec 64) : p + 272 + 136 = p + 408 := by bv_omega

theorem buffer_hmac {entry s : RamState} {key message : ByteArray}
    (buf : Buffered entry s key message)
    (len : s.external[base entry + 335]? = some (UInt8.ofNat ((innerMessage key message).size % 64))) :
    HmacAt s (base entry + 272) key message := by
  refine ⟨⟨?_, buf.tail, ?_, ?_⟩, ?_, ?_⟩
  · rw [hash_address]
    exact buf.words
  · rw [tail_address]
    exact len
  · rw [blocks_address]
    exact buf.blocks
  · rw [outer_address]
    exact buf.outerWords
  · rw [outer_blocks_address]
    exact buf.outerBlocks

theorem buffered_of_hmac {entry s : RamState} {key message : ByteArray}
    (hmac : HmacAt s (base entry + 272) key message) : Buffered entry s key message := by
  refine ⟨?_, hmac.inner.tail, ?_, ?_, ?_⟩
  · rw [← hash_address]
    exact hmac.inner.hashWords
  · rw [← blocks_address]
    exact hmac.inner.blocks
  · rw [← outer_address]
    exact hmac.outerHash
  · rw [← outer_blocks_address]
    exact hmac.outerBlocks

theorem tail_with_byte {entry s t : RamState} {a : ByteArray} {tail : Nat} {b : UInt8}
    (before : (area entry 272 tail).HasBytes s.external a)
    (same : (Component.mem (base entry + 272) tail).Agrees s t)
    (byte : t.external[base entry + BitVec.ofNat 64 (272 + tail)]? = some b) :
    (area entry 272 (tail + 1)).HasBytes t.external (a ++ singletonByte b) := by
  have asize : a.size = tail := before.1
  have total : (a ++ singletonByte b).size = tail + 1 := by
    rw [ByteArray.size_append, asize]; rfl
  refine ⟨total, fun i => ?_⟩
  change t.external[BitVec.ofNat 64 ((base entry + 272#64).toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  by_cases inside : i.val < a.size
  · rw [ByteArray.getElem_append_left inside]
    have eq := same i.val (by omega)
    have item := before.2 ⟨i.val, inside⟩
    change s.external[BitVec.ofNat 64 ((base entry + 272#64).toNat + i.val)]? = _ at item
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at item
    exact eq.trans item
  · have hi : i.val < tail + 1 := Nat.lt_of_lt_of_le i.isLt (Nat.le_of_eq total)
    have last : i.val = tail := by omega
    rw [ByteArray.getElem_append_right (Nat.le_of_not_lt inside)]
    have idx : i.val - a.size = 0 := by omega
    have h : (singletonByte b)[i.val - a.size]'(by
      have : (singletonByte b).size = 1 := rfl
      omega) = b := by
      change (#[b] : Array UInt8)[i.val - a.size]'_ = b
      simp only [idx, Array.getElem_singleton]
    rw [h, last, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact byte

theorem remainder_append_byte (a : ByteArray) (b : UInt8) :
    remainderBytes (a ++ singletonByte b) =
      if a.size % 64 = 63 then ByteArray.empty else remainderBytes a ++ singletonByte b := by
  rw [remainderBytes_append_buffered]
  have size : (remainderBytes a ++ singletonByte b).size = a.size % 64 + 1 := by
    rw [ByteArray.size_append, remainderBytes_size]; rfl
  split
  · rename_i full
    apply ByteArray.size_eq_zero_iff.mp
    rw [remainderBytes_size, size, full]
  · rename_i short
    have hr : (remainderBytes a ++ singletonByte b).size < 64 := by rw [size]; omega
    rw [remainderBytes, Nat.div_eq_of_lt hr, Nat.mul_zero, ByteArray.extract_zero_size]

theorem quotient_append_byte (a : ByteArray) (b : UInt8) :
    (a ++ singletonByte b).size / 64 =
      a.size / 64 + (if a.size % 64 = 63 then 1 else 0) := by
  have size : (a ++ singletonByte b).size = a.size + 1 := by rw [ByteArray.size_append]; rfl
  rw [size]
  split <;> omega

theorem remainder_size_append_byte (a : ByteArray) (b : UInt8) :
    (a ++ singletonByte b).size % 64 =
      if a.size % 64 = 63 then 0 else a.size % 64 + 1 := by
  have size : (a ++ singletonByte b).size = a.size + 1 := by rw [ByteArray.size_append]; rfl
  rw [size]
  split <;> omega

private theorem tail_of_agreement {entry s t : RamState} {tailSize : Nat} {bytes : ByteArray}
    (old : (area entry 272 tailSize).HasBytes s.external bytes)
    (same : (Component.mem (base entry + 272) tailSize).Agrees s t) :
    (area entry 272 tailSize).HasBytes t.external bytes := by
  have size : bytes.size = tailSize := old.1
  refine ⟨old.1, fun i => ?_⟩
  have hi : i.val < tailSize := Nat.lt_of_lt_of_le i.isLt (Nat.le_of_eq size)
  have eq := same i.val hi
  change t.external[BitVec.ofNat 64 ((base entry + 272#64).toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  apply eq.trans
  have byte := old.2 i
  change s.external[BitVec.ofNat 64 ((base entry + 272#64).toNat + i.val)]? = _ at byte
  rwa [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte

theorem Buffered.of_agreement {entry s t : RamState} {key message : ByteArray}
    (buf : Buffered entry s key message)
    (tail : (Component.mem (base entry + 272) ((innerMessage key message).size % 64)).Agrees s t)
    (words : (Component.mem (base entry + 336) 32).Agrees s t)
    (blocks : (Component.mem (base entry + 368) 8).Agrees s t)
    (outerWords : (Component.mem (base entry + 376) 32).Agrees s t)
    (outerBlocks : (Component.mem (base entry + 408) 8).Agrees s t) :
    Buffered entry t key message := by
  have keepBlocks : loadBytes t.external (base entry + 368) 8 =
      loadBytes s.external (base entry + 368) 8 :=
    Memory.loadBytes_congr (before := s.external) (after := t.external) blocks
  have keepOuterBlocks : loadBytes t.external (base entry + 408) 8 =
      loadBytes s.external (base entry + 408) 8 :=
    Memory.loadBytes_congr (before := s.external) (after := t.external) outerBlocks
  exact ⟨hashState_of_bytes (s := s) (t := t) (a := base entry + 336) (b := base entry + 336) buf.words words,
    tail_of_agreement (s := s) (t := t) buf.tail tail, keepBlocks.trans buf.blocks,
    hashState_of_bytes (s := s) (t := t) (a := base entry + 376) (b := base entry + 376) buf.outerWords outerWords,
    keepOuterBlocks.trans buf.outerBlocks⟩

end Hkdf.Proofs.NewExpand.Expand.Counter
