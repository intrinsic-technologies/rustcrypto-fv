import Hkdf.Proofs.NewExpand.Extract.Initialize.Assemble.Layout

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Initialize.Assemble

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.SHA256

theorem packed_bytes {s u : RamState} (effect : (layoutEffect s).Holds s u)
    (source : MemReadable s (rspOf s) 80)
    (destination : MemReadable u (rspOf s + 264) 80) :
    ∀ i < 80, u.external[rspOf s + 264 + BitVec.ofNat 64 i]? =
      s.external[rspOf s + BitVec.ofNat 64 i]? := by
  have stores := effect.writes
  simp only [layoutEffect, Write.AllHold, Operand.read] at stores
  have words : ∀ j < 10,
      memLoad u.external (rspOf s + 264 + BitVec.ofNat 64 (8*j)) 64 =
        memLoad s.external (rspOf s + BitVec.ofNat 64
          (8*j)) 64 := by
    rcases stores with ⟨_, _, _, _, _, w9, w8, w7, w5, w6, w0, w1, w2, w3, w4⟩
    intro j hj
    rcases (by omega : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨
      j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.add_zero]
    · exact w0
    · exact w1
    · exact w2
    · exact w3
    · exact w4
    · exact w5
    · exact w6
    · exact w7
    · exact w8
    · exact w9
  intro i hi
  have allocated {t : RamState} {p : BitVec 64} (readable : MemReadable t p 80) :
      ∀ j < 64 / 8, (t.external[p + BitVec.ofNat 64 (8 * (i / 8)) + BitVec.ofNat 64 j]?).isSome := by
    intro j hj
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact readable.mem _ (by omega)
  have target := Bytes.of_memLoad (n := 64) (allocated destination) (i%8) (by omega)
  have original := Bytes.of_memLoad (n := 64) (allocated source) (i%8) (by omega)
  rw [words (i / 8) (by omega)] at target
  have transferred := target.trans original.symm
  have offset (p : BitVec 64) : p + BitVec.ofNat 64 (8*(i/8)) + BitVec.ofNat 64 (i%8) =
      p + BitVec.ofNat 64 i := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8*(i/8) + i%8 = i by omega]
  rwa [offset, offset] at transferred

theorem hmac_of_packed {s t : RamState} {p : BitVec 64} {key : ByteArray}
    (inner : HashStateAt s p (compressBlocks initialHash (HMAC.xorPad (HMAC.keyBlock key) 0x36)))
    (innerCount : loadBytes s.external (p + 32) 8 = .ok 1)
    (outer : HashStateAt s (p + 40) (compressBlocks initialHash (HMAC.xorPad (HMAC.keyBlock key) 0x5c)))
    (outerCount : loadBytes s.external (p + 72) 8 = .ok 1)
    (copied : ∀ i < 80, t.external[p + 184 + BitVec.ofNat 64 i]? =
      s.external[p + BitVec.ofNat 64 i]?)
    (tailLength : t.external[p + 183]? = some 0) : HmacAt t (p + 120) key ByteArray.empty := by
  have subrange (offset : Nat) (i : Nat) (bound : offset + i < 80) :
      t.external[(p + 184 + BitVec.ofNat 64 offset) + BitVec.ofNat 64 i]? =
      s.external[(p + BitVec.ofNat 64 offset) + BitVec.ofNat 64 i]? := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using copied (offset + i) bound
  have count (offset : Nat) (bound : offset + 8 ≤ 80)
      (input : loadBytes s.external (p + BitVec.ofNat 64 offset) 8 = .ok 1) :
      loadBytes t.external (p + 184 + BitVec.ofNat 64 offset) 8 = .ok 1 := by
    apply Bytes.loadBytes64
    intro i hi
    exact (subrange offset i (by omega)).trans (Memory.bytes_of_loadBytes64 input i hi)
  refine ⟨?_, ?_, ?_⟩
  · rw [show HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ ByteArray.empty =
        HMAC.xorPad (HMAC.keyBlock key) 0x36 by simp]
    apply (StreamAt.single_block_iff (HMAC.xorPad_keyBlock_size key 0x36)).mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [← compressBlocks_single _ _ (HMAC.xorPad_keyBlock_size key 0x36)]
      apply hashState_of_bytes inner
      intro i hi
      rw [show p + 120 + 64 = p + 184 by rw [BitVec.add_assoc]; rfl]
      exact copied i (by omega)
    · rw [show p + 120 + 63 = p + 183 by rw [BitVec.add_assoc]; rfl]
      exact tailLength
    · simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
        count 32 (by decide) innerCount
  · apply hashState_of_bytes outer
    intro i hi
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
      subrange 40 i (by omega)
  · simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
      count 72 (by decide) outerCount

end Hkdf.Proofs.NewExpand.Extract.Initialize.Assemble
