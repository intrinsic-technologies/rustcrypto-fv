import Sha2.Proofs.Wrapper.Hash.Serialize.State

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Serialize

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA256
open Sha2.Proofs.Common.SHA256.Compression

theorem variant_serializeHash_size (v : Variant) (hash : Array UInt32) (hh : hash.size = 8) :
    (v.serializeHash hash).size = v.outputBytes := by
  cases v
  · change ((Common.SHA256.serializeHash hash).extract 0 28).size = 28
    simp [ByteArray.size_extract, Common.SHA256.serializeHash_size, hh]
  · exact (Common.SHA256.serializeHash_size hash).trans (by simp only [hh, Variant.outputBytes])

theorem variant_serializeHash_getElem (v : Variant) (hash : Array UInt32) (i : Nat)
    (hi : i < (v.serializeHash hash).size) :
    (v.serializeHash hash)[i] =
      UInt8.ofNat (hash[i / 4]!.toNat / 256 ^ (3 - i % 4) % 256) := by
  cases v
  · change i < ((Common.SHA256.serializeHash hash).extract 0 28).size at hi
    change ((Common.SHA256.serializeHash hash).extract 0 28)[i] = _
    simp only [ByteArray.getElem_extract, Nat.zero_add]
    apply Common.SHA256.serializeHash_getElem
  · exact Common.SHA256.serializeHash_getElem hash i hi

variable {v : Variant}

 theorem payload [Bindings] {initial s t : RamState} {inputs : Array Input} {message : ByteArray}
    (ctx : Context initial inputs v) (input : Compressed initial s message v) (output : Wrapper.State initial t v)
    (h : (effect s v).Holds s t) :
    (outputRegion v.routine initial).HasBytes
      t.external (v.hash message) := by
  obtain ⟨hash, hh, digest⟩ := input.digest
  have source : rspOf s + 64 = stackPtr initial - 280 := by
    rw [stack_address input.rsp]
    rfl
  have destination : outputAddress s = initial.regValue .rcx :=
    outputAddress_eq input.toPreserved
  have readable : MemReadable s (rspOf s + 64) 32 := by
    rw [source]
    exact stack_readable ctx input.toState (by decide) (by decide)
  have values : ∀ j < 8,
      memLoad s.external (rspOf s + 64 + BitVec.ofNat 64 (4 * j)) 32 = hash[j]!.toBitVec := by
    intro j hj
    apply memLoad32_of_loadBytes4
    · intro k hk
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact readable.mem _ (by omega)
    · rw [source]
      exact hh.2 j hj
  have words : ∀ j < v.outputBytes / 4, memLoad t.external
      (initial.regValue .rcx + BitVec.ofNat 64 (4 * j)) 32 = bswap32 hash[j]!.toBitVec := by
    intro j hj
    have bound : j < 8 := by cases v <;> simp only [Variant.outputBytes] at hj <;> omega
    rw [← destination, ← values j bound]
    have stores := h.writes
    cases v
    · simp only [effect, List.cons_append, List.nil_append, Write.AllHold] at stores
      have hj : j < 7 := hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.1
      · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.1
      · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.1
      · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.1
      · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.1
      · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    · simp only [effect, List.cons_append, List.nil_append, Write.AllHold] at stores
      have hj : j < 8 := hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.1
      · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.1
      · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.1
      · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.1
      · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · simpa only [rspOf, Operand.read, BitVec.add_assoc, Nat.reduceMul,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using stores.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have multiple : 4 * (v.outputBytes / 4) = v.outputBytes := by cases v <;> rfl
  have bytes := bigEndian_bytes (count := v.outputBytes / 4)
    (by rw [multiple]; exact (output_readable ctx output).mem) words
  rw [← digest]
  refine ⟨?_, ?_⟩
  · change (v.serializeHash hash).size = v.outputBytes
    exact variant_serializeHash_size v hash hh.1
  · intro i
    have hi : i.val < 4 * (v.outputBytes / 4) := by
      rw [multiple, ← variant_serializeHash_size v hash hh.1]
      exact i.isLt
    change t.external[BitVec.ofNat 64 ((initial.regValue .rcx).toNat + i.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      variant_serializeHash_getElem]
    exact bytes i.val hi

end Sha2.Proofs.Wrapper.Hash.Serialize
