import Hkdf.Proofs.Common.State
import Hkdf.Proofs.Common.Streaming

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Update

open Hkdf.Proofs.Common Hkdf.Proofs.Common.SHA256
open Prelude X86 X86.Machine X86Proofs

structure HashFields (s : RamState) (p : BitVec 64) (key ikm : ByteArray) : Prop where
  hashWords : HashStateAt s (p + 64) (compressBlocks
    (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (HMAC.xorPad (HMAC.keyBlock key) 0x36)) ikm)
  blocks : loadBytes s.external (p + 96) 8 = .ok (BitVec.ofNat 64 (1 + ikm.size / 64))
  outerHash : HashStateAt s (p + 104) (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash
    (HMAC.xorPad (HMAC.keyBlock key) 0x5c))
  outerBlocks : loadBytes s.external (p + 136) 8 = .ok 1

theorem HashFields.short {s : RamState} {p : BitVec 64} {key ikm : ByteArray}
    (hmac : HmacAt s p key ByteArray.empty) (small : ikm.size < 64) :
    HashFields s p key ikm := by
  refine ⟨?_, ?_, hmac.outerHash, hmac.outerBlocks⟩
  · rw [compressBlocks_short _ _ small]
    simpa only [ByteArray.append_empty] using hmac.inner.hashWords
  · simpa only [ByteArray.append_empty, HMAC.xorPad_keyBlock_size, Nat.reduceDiv,
      Nat.div_eq_of_lt small, Nat.add_zero] using hmac.inner.blocks

theorem HashFields.preserved {s t : RamState} {p : BitVec 64} {key ikm : ByteArray}
    (fields : HashFields s p key ikm)
    (same : ∀ i, 64 ≤ i → i < 144 →
      t.external[p + BitVec.ofNat 64 i]? = s.external[p + BitVec.ofNat 64 i]?) :
    HashFields t p key ikm := by
  have segment (off len : Nat) (lo : 64 ≤ off) (hi : off + len ≤ 144) :
      (Component.mem (p + BitVec.ofNat 64 off) len).Agrees s t := by
    intro i il
    rw [BitVec.add_assoc, ←BitVec.ofNat_add]
    exact same _ (by omega) (by omega)
  exact ⟨hashState_of_bytes fields.hashWords (segment 64 32 (by decide) (by decide)),
    (Memory.loadBytes_congr (segment 96 8 (by decide) (by decide))).trans fields.blocks,
    hashState_of_bytes fields.outerHash (segment 104 32 (by decide) (by decide)),
    (Memory.loadBytes_congr (segment 136 8 (by decide) (by decide))).trans fields.outerBlocks⟩

theorem HashFields.hmac {s : RamState} {p : BitVec 64} {key ikm : ByteArray}
    (fields : HashFields s p key ikm)
    (tail : (⟨p.toNat, ikm.size % 64⟩ : MemoryRegion).HasBytes s.external (remainderBytes ikm))
    (length : s.external[p + 63]? = some (UInt8.ofNat (ikm.size % 64))) :
    HmacAt s p key ikm := by
  have aligned : (HMAC.xorPad (HMAC.keyBlock key) 0x36).size % 64 = 0 := by
    rw [HMAC.xorPad_keyBlock_size]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fields.outerHash, fields.outerBlocks⟩
  · rw [compressBlocks_append _ _ _ aligned]
    exact fields.hashWords
  · change (⟨p.toNat, _⟩ : MemoryRegion).HasBytes s.external (remainderBytes (_ ++ _))
    rw [remainderBytes_append_aligned _ _ aligned, ByteArray.size_append, HMAC.xorPad_keyBlock_size,
      show (64 + ikm.size) % 64 = ikm.size % 64 by omega]
    exact tail
  · simpa only [ByteArray.size_append, HMAC.xorPad_keyBlock_size,
      show (64 + ikm.size) % 64 = ikm.size % 64 by omega] using length
  · simpa only [ByteArray.size_append, HMAC.xorPad_keyBlock_size,
      show (64 + ikm.size) / 64 = 1 + ikm.size / 64 by omega] using fields.blocks

end Hkdf.Proofs.NewExpand.Extract.Update
