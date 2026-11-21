import P256.Proofs.Signing.Wrapper.Hash.Finalize.Serialize.Machine
import P256.Proofs.SHA256.Memory.Serialization
import P256.Proofs.SHA256.Mathematics.Padding.Standard.Serialization

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Serialize

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SHA256
open P256.Proofs.Common.SHA256.Compression

theorem payload {s t : RamState} {hash : Array UInt32}
    (pre : Pre s) (hh : HashStateAt s (rspOf s + 128) hash)
    (h : (effect s).Holds s t) :
    (⟨(rspOf s + 0).toNat, 32⟩ : MemoryRegion).HasBytes
      t.external (serializeHash hash) := by
  have source (j : Nat) (hj : j < 8) :
      MemReadable s (rspOf s + 128 + BitVec.ofNat 64 (4 * j)) 4 := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using pre.readable 128 (by simp)
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using pre.readable 132 (by simp)
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using pre.readable 136 (by simp)
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using pre.readable 140 (by simp)
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using pre.readable 144 (by simp)
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using pre.readable 148 (by simp)
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using pre.readable 152 (by simp)
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using pre.readable 156 (by simp)
  have allocated (j : Nat) (hj : j < 8) :
      MemReadable t (rspOf s + 0 + BitVec.ofNat 64 (4 * j)) 4 := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using
          ((pre.writable 0 (by simp)).toMemReadable.of_holds h)
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using
          ((pre.writable 4 (by simp)).toMemReadable.of_holds h)
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using
          ((pre.writable 8 (by simp)).toMemReadable.of_holds h)
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using
          ((pre.writable 12 (by simp)).toMemReadable.of_holds h)
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using
          ((pre.writable 16 (by simp)).toMemReadable.of_holds h)
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using
          ((pre.writable 20 (by simp)).toMemReadable.of_holds h)
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using
          ((pre.writable 24 (by simp)).toMemReadable.of_holds h)
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.add_zero, BitVec.reduceAdd] using
          ((pre.writable 28 (by simp)).toMemReadable.of_holds h)
  have values : ∀ j < 8,
      memLoad s.external (rspOf s + 128 + BitVec.ofNat 64 (4 * j)) 32 = hash[j]!.toBitVec := by
    intro j hj
    exact memLoad32_of_loadBytes4 (source j hj).mem (hh.2 j hj)
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read] at stores
  have words : ∀ j < 8, memLoad t.external
      (rspOf s + 0 + BitVec.ofNat 64 (4 * j)) 32 = bswap32 hash[j]!.toBitVec := by
    intro j hj
    rw [← values j hj]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.1
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.1
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have bytes := bigEndian_bytes (s := t) (address := rspOf s + 0) (hash := hash) (by
    intro i hi
    have byte := (allocated (i / 4) (by omega)).mem (i % 4) (by omega)
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 * (i / 4) + i % 4 = i by omega] using byte) words
  refine ⟨by simp only [MemoryRegion.HasLength, serializeHash_size, hh.1], ?_⟩
  intro i
  have hi : i.val < 32 := by simpa only [serializeHash_size, hh.1] using i.isLt
  change t.external[BitVec.ofNat 64 ((rspOf s + 0).toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, serializeHash_getElem]
  exact bytes i.val hi

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Serialize
