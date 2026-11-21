import Sha2.Proofs.Common.SHA256.Serialize.Blocks
import Sha2.Proofs.Common.SHA256.Words
import Sha2.Proofs.Common.SHA256.Mathematics.Padding.Serialization
import Sha2.Proofs.Wrapper.Hash.Serialize.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Serialize

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA256.Compression

def wordRegister (i : Nat) : BitVec 5 :=
  (#[0, 1, 2, 6, 7, 8, 9, 10] : Array (BitVec 5))[i]!

def SwappedRegisters (s : RamState) (hash : Array UInt32) (truncated : Bool := false) : Prop :=
  hash.size = 8 ∧ ∀ j < (if truncated then 7 else 8),
    (.reg (wordRegister j) : Operand 32).read s = bswap32 hash[j]!.toBitVec

theorem loadSwap_words {p : BitVec 64} {offset : HashOffset} {s t : RamState}
    {hash : Array UInt32} {truncated : Bool} (pre : LoadPre p offset s truncated)
    (words : HashStateAt s (rspOf s + BitVec.ofNat 64 offset.value) hash)
    (result : (effect p (.loadSwap offset truncated) s).Holds s t) : SwappedRegisters t hash truncated := by
  refine ⟨words.1, ?_⟩
  intro j hj
  have hj8 : j < 8 := by split at hj <;> omega
  have readable : MemReadable s (rspOf s + BitVec.ofNat 64 (offset.value + 4 * j)) 4 := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pre.read0
    · exact pre.read1
    · exact pre.read2
    · exact pre.read3
    · exact pre.read4
    · exact pre.read5
    · exact pre.read6
    · cases truncated
      · exact pre.read7
      · simp at hj
  have value : memLoad s.external (rspOf s + BitVec.ofNat 64 (offset.value + 4 * j)) 32 =
      hash[j]!.toBitVec := by
    apply memLoad32_of_loadBytes4 readable.mem
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using words.2 j hj8
  have stored := result.writes
  have wide : (.reg (wordRegister j) : Operand 64).read t =
      (bswap32 ((.mem (rspOf s + BitVec.ofNat 64 (offset.value + 4 * j)) :
        Operand 32).read s)).setWidth 64 := by
    cases truncated with
    | false =>
      simp only [effect, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, Write.AllHold] at stored
      have bound : j < 8 := hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact stored.1
      · exact stored.2.1
      · exact stored.2.2.1
      · exact stored.2.2.2.1
      · exact stored.2.2.2.2.1
      · exact stored.2.2.2.2.2.1
      · exact stored.2.2.2.2.2.2.1
      · exact stored.2.2.2.2.2.2.2
    | true =>
      simp only [effect, ↓reduceIte, List.append_nil, Write.AllHold] at stored
      have bound : j < 7 := hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact stored.1
      · exact stored.2.1
      · exact stored.2.2.1
      · exact stored.2.2.2.1
      · exact stored.2.2.2.2.1
      · exact stored.2.2.2.2.2.1
      · exact stored.2.2.2.2.2.2
  change memLoad s.external _ 32 = _ at value
  change (.reg (wordRegister j) : Operand 64).read t =
    (bswap32 (memLoad s.external _ 32)).setWidth 64 at wide
  rw [value] at wide
  have narrow := congrArg (fun v : BitVec 64 => v.setWidth 32) wide
  simpa only [Operand.setWidth_read_reg64,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq] using narrow

set_option maxHeartbeats 400000 in
theorem store_hasBytes {p : BitVec 64} {output : OutputRegister} {s t : RamState}
    {hash : Array UInt32} {truncated : Bool} (words : SwappedRegisters s hash truncated)
    (result : (effect p (.store output truncated) s).Holds s t)
    (allocated : ∀ i < (if truncated then 28 else 32),
      (t.external[(.reg output.value : Operand 64).read s + BitVec.ofNat 64 i]?).isSome) :
    (⟨((.reg output.value : Operand 64).read s).toNat, (if truncated then 28 else 32)⟩ : MemoryRegion).HasBytes
      t.external (if truncated then (serializeHash hash).extract 0 28 else serializeHash hash) := by
  have stored := result.writes
  have values : ∀ j < (if truncated then 7 else 8), memLoad t.external
      ((.reg output.value : Operand 64).read s + BitVec.ofNat 64 (4 * j)) 32 =
        bswap32 hash[j]!.toBitVec := by
    intro j hj
    have word : memLoad t.external
        ((.reg output.value : Operand 64).read s + BitVec.ofNat 64 (4 * j)) 32 =
        (.reg (wordRegister j) : Operand 32).read s := by
      cases truncated with
      | false =>
        simp only [effect, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, Write.AllHold] at stored
        have bound : j < 8 := hj
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact stored.1
        · exact stored.2.1
        · exact stored.2.2.1
        · exact stored.2.2.2.1
        · exact stored.2.2.2.2.1
        · exact stored.2.2.2.2.2.1
        · exact stored.2.2.2.2.2.2.1
        · exact stored.2.2.2.2.2.2.2
      | true =>
        simp only [effect, ↓reduceIte, List.append_nil, Write.AllHold] at stored
        have bound : j < 7 := hj
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact stored.1
        · exact stored.2.1
        · exact stored.2.2.1
        · exact stored.2.2.2.1
        · exact stored.2.2.2.2.1
        · exact stored.2.2.2.2.2.1
        · exact stored.2.2.2.2.2.2
    exact word.trans (words.2 j hj)
  have bytes := Wrapper.Hash.Serialize.bigEndian_bytes (count := if truncated then 7 else 8)
    (by cases truncated <;> exact allocated) values
  cases truncated <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · refine ⟨by simp only [MemoryRegion.HasLength, serializeHash_size, words.1], ?_⟩
    intro i
    have hi : i.val < 32 := by simpa only [serializeHash_size, words.1] using i.isLt
    change t.external[BitVec.ofNat 64 (((.reg output.value : Operand 64).read s).toNat + i.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, serializeHash_getElem]
    exact bytes i.val hi
  · have size : ((serializeHash hash).extract 0 28).size = 28 := by
      simp [serializeHash_size, words.1]
    refine ⟨by simpa only [MemoryRegion.HasLength] using size, ?_⟩
    intro i
    have hi : i.val < 28 := by simpa only [size] using i.isLt
    change t.external[BitVec.ofNat 64 (((.reg output.value : Operand 64).read s).toNat + i.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simpa only [ByteArray.getElem_extract, Nat.zero_add, serializeHash_getElem] using bytes i.val hi

end Sha2.Proofs.Common.SHA256.Serialize
