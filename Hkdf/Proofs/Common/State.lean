import Hkdf.Proofs.Common.HMAC
import Hkdf.Proofs.Common.SHA256.Mathematics.Padding.Tail
import Hkdf.Proofs.Common.SHA256.Interfaces
import Hkdf.Proofs.Common.Memory
import Hkdf.Proofs.Common.Memory.LoadBytes

namespace Hkdf.Proofs.Common

open Prelude X86 X86.Machine X86Proofs
open Hkdf.Proofs.Common.SHA256

theorem hashState_of_bytes {s t : RamState} {a b : BitVec 64} {hash : Array UInt32}
    (input : Common.SHA256.HashStateAt s a hash)
    (bytes : ∀ i < 32, t.external[b + BitVec.ofNat 64 i]? = s.external[a + BitVec.ofNat 64 i]?) :
    Common.SHA256.HashStateAt t b hash := by
  refine ⟨input.1, fun i hi => ?_⟩
  have eq (j : Nat) (hj : j < 4) :
      t.external[b + BitVec.ofNat 64 (4*i) + BitVec.ofNat 64 j]? =
      s.external[a + BitVec.ofNat 64 (4*i) + BitVec.ofNat 64 j]? := by
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using bytes (4*i+j) (by omega)
  have h0 := eq 0 (by decide)
  have h1 := eq 1 (by decide)
  have h2 := eq 2 (by decide)
  have h3 := eq 3 (by decide)
  have raw := input.2 i hi
  simp only [loadBytes, loadBytes.loop, addAddress, fromNat, Nat.zero_add, Nat.reduceAdd] at raw ⊢
  rw [h0, h1, h2, h3]
  split at raw <;> try contradiction
  split at raw <;> try contradiction
  split at raw <;> try contradiction
  split at raw <;> try contradiction
  simp_all only

structure StreamAt (s : RamState) (p : BitVec 64) (message : ByteArray) : Prop where
  hashWords : HashStateAt s (p + 64)
    (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash message)
  tail : (⟨p.toNat, message.size % 64⟩ : MemoryRegion).HasBytes s.external
    (message.extract (64 * (message.size / 64)) message.size)
  tailLength : s.external[p + 63]? = some (UInt8.ofNat (message.size % 64))
  blocks : loadBytes s.external (p + 96) 8 = .ok (BitVec.ofNat 64 (message.size / 64))

structure HmacAt (s : RamState) (p : BitVec 64) (key message : ByteArray) : Prop where
  inner : StreamAt s p (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message)
  outerHash : HashStateAt s (p + 104)
    (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (HMAC.xorPad (HMAC.keyBlock key) 0x5c))
  outerBlocks : loadBytes s.external (p + 136) 8 = .ok 1

structure SimpleHmacAt (s : RamState) (p : BitVec 64) (key message : ByteArray) : Prop where
  outerPad : (⟨p.toNat, 64⟩ : MemoryRegion).HasBytes s.external
    (HMAC.xorPad (HMAC.keyBlock key) 0x5c)
  inner : StreamAt s (p + 64) (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message)

theorem StreamAt.of_copy {s t : RamState} {src dest : BitVec 64} {message : ByteArray}
    (input : StreamAt s src message)
    (bytes : ∀ i < 104,
      t.external[dest + BitVec.ofNat 64 i]? = s.external[src + BitVec.ofNat 64 i]?) :
    StreamAt t dest message := by
  refine ⟨Hkdf.Proofs.Common.hashState_of_bytes input.hashWords ?_,
    ⟨input.tail.1, ?_⟩, ?_, ?_⟩
  · intro i hi
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
      bytes (64 + i) (by omega)
  · intro i
    have size : (message.extract (64 * (message.size / 64)) message.size).size =
        message.size % 64 := input.tail.1
    have hi : i.val < message.size % 64 := by simpa only [size] using i.isLt
    have same := bytes i.val (by omega)
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      same.trans (by simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat,
        BitVec.setWidth_eq] using input.tail.2 i)
  · exact (bytes 63 (by decide)).trans input.tailLength
  · apply Bytes.loadBytes64
    intro i hi
    have same :
        t.external[dest + 96 + BitVec.ofNat 64 i]? =
          s.external[src + 96 + BitVec.ofNat 64 i]? := by
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
        bytes (96 + i) (by omega)
    exact same.trans (Hkdf.Proofs.Common.Memory.bytes_of_loadBytes64 input.blocks i hi)

theorem HmacAt.of_copy {s t : RamState} {src dest : BitVec 64} {key message : ByteArray}
    (input : HmacAt s src key message)
    (bytes : ∀ i < 144,
      t.external[dest + BitVec.ofNat 64 i]? = s.external[src + BitVec.ofNat 64 i]?) :
    HmacAt t dest key message := by
  refine ⟨input.inner.of_copy ?_,
    Hkdf.Proofs.Common.hashState_of_bytes input.outerHash ?_, ?_⟩
  · intro i hi
    exact bytes i (by omega)
  · intro i hi
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using bytes (104 + i) (by omega)
  · apply Bytes.loadBytes64
    intro i hi
    have same :
        t.external[dest + 136 + BitVec.ofNat 64 i]? =
          s.external[src + 136 + BitVec.ofNat 64 i]? := by
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using bytes (136 + i) (by omega)
    exact same.trans (Hkdf.Proofs.Common.Memory.bytes_of_loadBytes64 input.outerBlocks i hi)

theorem SimpleHmacAt.of_copy {s t : RamState} {src dest : BitVec 64} {key message : ByteArray}
    (input : SimpleHmacAt s src key message)
    (bytes : ∀ i < 168,
      t.external[dest + BitVec.ofNat 64 i]? = s.external[src + BitVec.ofNat 64 i]?) :
    SimpleHmacAt t dest key message := by
  refine ⟨⟨input.outerPad.1, ?_⟩, input.inner.of_copy ?_⟩
  · intro i
    have hi : i.val < 64 := by simpa only [HMAC.xorPad_keyBlock_size] using i.isLt
    have same := bytes i.val (by omega)
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      same.trans (by simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat,
        BitVec.setWidth_eq] using input.outerPad.2 i)
  · intro i hi
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using bytes (64 + i) (by omega)

theorem StreamAt.single_block_iff {s : RamState} {p : BitVec 64} {block : ByteArray}
    (size : block.size = 64) :
    StreamAt s p block ↔
      HashStateAt s (p + 64)
        (Hkdf.Proofs.NIST.SHA256.compress Hkdf.Proofs.NIST.SHA256.initialHash
          (Hkdf.Proofs.NIST.Encoding.octetsToBits block)) ∧
      s.external[p + 63]? = some 0 ∧ loadBytes s.external (p + 96) 8 = .ok 1 := by
  have zero : UInt8.ofNat 0 = (0 : UInt8) := by decide +kernel
  constructor
  · intro input
    refine ⟨?_, ?_, ?_⟩
    · simpa only [compressBlocks_single _ block size] using input.hashWords
    · simpa only [size, Nat.reduceMod, zero] using input.tailLength
    · simpa only [size, Nat.reduceDiv, BitVec.ofNat_eq_ofNat] using input.blocks
  · rintro ⟨hashWords, tailLength, blocks⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [compressBlocks_single _ block size] using hashWords
    · have empty_tail : (⟨p.toNat, 0⟩ : MemoryRegion).HasBytes s.external ByteArray.empty :=
        ⟨rfl, fun i ↦ Fin.elim0 i⟩
      simpa only [size, Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, ByteArray.extract_same]
        using empty_tail
    · simpa only [size, Nat.reduceMod, zero] using tailLength
    · simpa only [size, Nat.reduceDiv, BitVec.ofNat_eq_ofNat] using blocks

end Hkdf.Proofs.Common
