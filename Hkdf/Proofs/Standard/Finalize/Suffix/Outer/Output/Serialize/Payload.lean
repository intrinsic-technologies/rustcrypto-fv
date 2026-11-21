import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output.Serialize.Machine
import Hkdf.Proofs.Common.Memory
import Hkdf.Proofs.Common.SHA256.Words
import Hkdf.Proofs.Common.SHA256.Mathematics.Padding.Serialization

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output.Serialize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.SHA256
open Hkdf.Proofs.Common.SHA256.Compression

theorem rsp_unchanged {s t : RamState} (h : (effect s).Holds s t) : rspOf t = rspOf s := by
  exact h.agrees.read (by simp [effect, Effect.components])

theorem payload {s t : RamState} {hash : Array UInt32}
    (pre : Pre s) (hashWords : HashStateAt s (rspOf s + 176) hash)
    (h : (effect s).Holds s t) :
    (⟨(rspOf s + 216).toNat, 32⟩ : MemoryRegion).HasBytes t.external (serializeHash hash) := by
  have allocated : ∀ i < 32, (t.external[rspOf s + 216 + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    have hj : i / 4 < 8 := by omega
    have hw : MemReadable t (rspOf s + 216 + BitVec.ofNat 64 (4 * (i / 4))) 4 := by
      apply MemReadable.of_holds h
      rcases (by omega : i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3 ∨
        i / 4 = 4 ∨ i / 4 = 5 ∨ i / 4 = 6 ∨ i / 4 = 7) with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 216 (by simp)).toMemReadable
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 220 (by simp)).toMemReadable
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 224 (by simp)).toMemReadable
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 228 (by simp)).toMemReadable
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 232 (by simp)).toMemReadable
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 236 (by simp)).toMemReadable
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 240 (by simp)).toMemReadable
      · simpa only [h0, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (pre.writable 244 (by simp)).toMemReadable
    have byte := hw.mem (i % 4) (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 4 * (i / 4) + i % 4 = i by omega] at byte
    exact byte
  have values : ∀ j < 8,
      memLoad s.external (rspOf s + 176 + BitVec.ofNat 64 (4 * j)) 32 = hash[j]!.toBitVec := by
    intro j hj
    apply memLoad32_of_loadBytes4
    · intro k hk
      have hr : MemReadable s (rspOf s + 176 + BitVec.ofNat 64 (4 * j)) 4 := by
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 176 (by simp)
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 180 (by simp)
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 184 (by simp)
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 188 (by simp)
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 192 (by simp)
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 196 (by simp)
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 200 (by simp)
        · simpa only [BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            pre.readable 204 (by simp)
      exact hr.mem k hk
    · exact hashWords.2 j hj
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read] at stores
  have words : ∀ j < 8, memLoad t.external
      (rspOf s + 216 + BitVec.ofNat 64 (4 * j)) 32 = bswap32 hash[j]!.toBitVec := by
    intro j hj
    rw [← values j hj]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.1
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.1
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have bytes := Hkdf.Proofs.Common.Memory.bigEndian_bytes allocated words
  refine ⟨by simp only [MemoryRegion.HasLength, serializeHash_size, hashWords.1], ?_⟩
  intro i
  have hi : i.val < 32 := by simpa only [serializeHash_size, hashWords.1] using i.isLt
  change t.external[BitVec.ofNat 64 ((rspOf s + 216).toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, serializeHash_getElem]
  exact bytes i.val hi

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output.Serialize
