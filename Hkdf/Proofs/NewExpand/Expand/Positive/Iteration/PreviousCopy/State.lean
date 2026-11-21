import Hkdf.Proofs.Common.State
import Hkdf.Proofs.Common.Streaming

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.PreviousCopy

open Prelude X86 X86.Machine X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.SHA256

theorem hmac_after_copy {s t : RamState} {p : BitVec 64} {key previous : ByteArray}
    (initial : HmacAt s p key ByteArray.empty)
    (tail : (⟨p.toNat, 32⟩ : MemoryRegion).HasBytes t.external previous)
    (lengthByte : t.external[p + 63]? = some 32)
    (preserved : ∀ (i : Nat), 64 ≤ i → i < 144 →
      t.external[p + BitVec.ofNat 64 i]? = s.external[p + BitVec.ofNat 64 i]?) :
    HmacAt t p key previous := by
  let pad := HMAC.xorPad (HMAC.keyBlock key) 0x36
  have padSize : pad.size = 64 := HMAC.xorPad_keyBlock_size key 0x36
  have size : previous.size = 32 := tail.1
  have total : (pad ++ previous).size = 96 := by
    rw [ByteArray.size_append, padSize, size]
  have emptySize : (pad ++ ByteArray.empty).size = 64 := by
    rw [ByteArray.size_append, ByteArray.size_empty, padSize, Nat.add_zero]
  have digest : compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (pad ++ previous) =
      compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (pad ++ ByteArray.empty) := by
    rw [compressBlocks_append_short _ pad previous (by rw [size, padSize]; decide),
      ByteArray.append_empty]
  have tailBytes : (pad ++ previous).extract (64 * ((pad ++ previous).size / 64))
      (pad ++ previous).size = previous := by
    rw [total]
    change (pad ++ previous).extract 64 96 = previous
    rw [← padSize, show 96 = pad.size + previous.size by rw [padSize, size]]
    exact ByteArray.extract_append_eq_right rfl rfl
  have kept (offset len : Nat) (lo : 64 ≤ offset) (hi : offset + len ≤ 144) :
      ∀ i < len, t.external[p + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[p + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i ihi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact preserved _ (by omega) (by omega)
  have blocks (offset : Nat) (lo : 64 ≤ offset) (hi : offset + 8 ≤ 144) :
      loadBytes t.external (p + BitVec.ofNat 64 offset) 8 =
        loadBytes s.external (p + BitVec.ofNat 64 offset) 8 :=
    Memory.loadBytes_congr (kept offset 8 lo hi)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · change HashStateAt t (p + 64) (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (pad ++ previous))
    rw [digest]
    exact hashState_of_bytes initial.inner.hashWords (kept 64 32 (by decide) (by decide))
  · change (⟨p.toNat, (pad ++ previous).size % 64⟩ : MemoryRegion).HasBytes t.external _
    rw [tailBytes, total]
    exact tail
  · change t.external[p + 63]? = some (UInt8.ofNat ((pad ++ previous).size % 64))
    rw [total]
    exact lengthByte
  · change loadBytes t.external (p + 96) 8 = .ok (BitVec.ofNat 64 ((pad ++ previous).size / 64))
    have same : loadBytes t.external (p + 96) 8 = loadBytes s.external (p + 96) 8 :=
      blocks 96 (by decide) (by decide)
    rw [same, total]
    have count := initial.inner.blocks
    change loadBytes s.external (p + 96) 8 =
      .ok (BitVec.ofNat 64 ((pad ++ ByteArray.empty).size / 64)) at count
    rw [emptySize] at count
    exact count
  · exact hashState_of_bytes initial.outerHash (kept 104 32 (by decide) (by decide))
  · exact (blocks 136 (by decide) (by decide)).trans initial.outerBlocks

end Hkdf.Proofs.NewExpand.Expand.PreviousCopy
