import Hkdf.Proofs.Common.State
import Hkdf.Proofs.Common.Streaming

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info.Short

open Prelude X86 X86.Machine X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.SHA256

theorem hmac_append {s t : RamState} {p : BitVec 64} {key prev info : ByteArray}
    (input : HmacAt s p key prev) (short : prev.size + info.size < 64)
    (keptPrefix : ∀ i < prev.size,
      t.external[p + BitVec.ofNat 64 i]? = s.external[p + BitVec.ofNat 64 i]?)
    (fields : ∀ i, 64 ≤ i → i < 144 →
      t.external[p + BitVec.ofNat 64 i]? = s.external[p + BitVec.ofNat 64 i]?)
    (copied : (⟨(p + BitVec.ofNat 64 prev.size).toNat, info.size⟩ : MemoryRegion).HasBytes
      t.external info)
    (index : t.external[p + 63]? = some (UInt8.ofNat (prev.size + info.size))) :
    HmacAt t p key (prev ++ info) := by
  let pad := HMAC.xorPad (HMAC.keyBlock key) 0x36
  have padSize : pad.size = 64 := HMAC.xorPad_keyBlock_size key 0x36
  have prevShort : prev.size < 64 := by omega
  have nextShort : (prev ++ info).size < 64 := by simpa only [ByteArray.size_append] using short
  have padMod (message : ByteArray) (small : message.size < 64) :
      (pad ++ message).size % 64 = message.size := by
    rw [ByteArray.size_append, padSize]
    omega
  have padDiv (message : ByteArray) (small : message.size < 64) :
      (pad ++ message).size / 64 = 1 := by
    rw [ByteArray.size_append, padSize]
    omega
  have padTail (message : ByteArray) (small : message.size < 64) :
      remainderBytes (pad ++ message) = message := by
    rw [remainderBytes_append_aligned _ _ (by rw [padSize]),
      remainderBytes, Nat.div_eq_of_lt small, Nat.mul_zero, ByteArray.extract_zero_size]
  have sameHash : compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (pad ++ (prev ++ info)) =
      compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (pad ++ prev) := by
    rw [← ByteArray.append_assoc]
    apply compressBlocks_append_short
    rw [padMod _ prevShort]
    omega
  have prevTail : (⟨p.toNat, prev.size⟩ : MemoryRegion).HasBytes s.external prev := by
    have oldTail := input.inner.tail
    change (⟨p.toNat, (pad ++ prev).size % 64⟩ : MemoryRegion).HasBytes s.external
      (remainderBytes (pad ++ prev)) at oldTail
    simpa only [padMod _ prevShort, padTail _ prevShort] using oldTail
  have nextTail : (⟨p.toNat, (prev ++ info).size⟩ : MemoryRegion).HasBytes t.external
      (prev ++ info) := by
    refine ⟨rfl, fun i => ?_⟩
    change t.external[BitVec.ofNat 64 (p.toNat + i.val)]? = some ((prev ++ info)[i.val])
    by_cases left : i.val < prev.size
    · have byte := prevTail.2 ⟨i.val, left⟩
      rw [ByteArray.getElem_append_left left]
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        (keptPrefix i.val left).trans (by
          simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using byte)
    · have il := i.isLt
      have bound : i.val < prev.size + info.size := by
        simpa only [ByteArray.size_append] using il
      have byte := copied.2 ⟨i.val - prev.size, by omega⟩
      have addr : (p + BitVec.ofNat 64 prev.size) + BitVec.ofNat 64 (i.val - prev.size) =
          p + BitVec.ofNat 64 i.val := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, show prev.size + (i.val - prev.size) = i.val by omega]
      rw [ByteArray.getElem_append_right (by omega)]
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, addr] using byte
  have segment (offset count : Nat) (lo : 64 ≤ offset) (hi : offset + count ≤ 144) :
      (Component.mem (p + BitVec.ofNat 64 offset) count).Agrees s t := by
    intro i bound
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact fields _ (by omega) (by omega)
  refine ⟨⟨?_, ?_, ?_, ?_⟩,
    hashState_of_bytes input.outerHash (segment 104 32 (by decide) (by decide)),
    (Memory.loadBytes_congr (segment 136 8 (by decide) (by decide))).trans input.outerBlocks⟩
  · change HashStateAt t (p + 64)
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (pad ++ (prev ++ info)))
    rw [sameHash]
    exact hashState_of_bytes input.inner.hashWords (segment 64 32 (by decide) (by decide))
  · change (⟨p.toNat, (pad ++ (prev ++ info)).size % 64⟩ : MemoryRegion).HasBytes t.external
      (remainderBytes (pad ++ (prev ++ info)))
    simpa only [padMod _ nextShort, padTail _ nextShort] using nextTail
  · change t.external[p + 63]? = some (UInt8.ofNat ((pad ++ (prev ++ info)).size % 64))
    rw [padMod _ nextShort, ByteArray.size_append]
    exact index
  · change loadBytes t.external (p + 96) 8 = .ok (BitVec.ofNat 64 ((pad ++ (prev ++ info)).size / 64))
    rw [padDiv _ nextShort]
    have blocks := input.inner.blocks
    change loadBytes s.external (p + 96) 8 = .ok (BitVec.ofNat 64 ((pad ++ prev).size / 64)) at blocks
    rw [padDiv _ prevShort] at blocks
    exact (Memory.loadBytes_congr (segment 96 8 (by decide) (by decide))).trans blocks

end Hkdf.Proofs.NewExpand.Expand.Info.Short
