import Sha2.Proofs.Wrapper512.State
import Sha2.Proofs.Common.SHA512.Mathematics.Padding.Serialization
import Sha2.Proofs.Common.Instructions.Bswap
import Sha2.Proofs.Wrapper.Hash.LengthEncoding
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Finish.Serialize

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Wrapper.Hash (bswap64_storedByte)

def selectedHash (v : Variant) (hash : Array UInt64) : Array UInt64 :=
  if v = .sha384 then hash.extract 0 6 else hash

theorem selectedHash_size (v : Variant) {hash : Array UInt64} (hsize : hash.size = 8) :
    (selectedHash v hash).size = if v = .sha384 then 6 else 8 := by
  cases v with
  | sha384 =>
    simp [selectedHash, Array.size_extract, hsize]
  | sha512 => simp [selectedHash, hsize]
  | sha512_224 => simp [selectedHash, hsize]
  | sha512_256 => simp [selectedHash, hsize]

theorem selectedHash_get_sha384 {hash : Array UInt64} (hsize : hash.size = 8)
    {j : Nat} (hj : j < 6) :
    (selectedHash .sha384 hash)[j]! = hash[j]! := by
  change (hash.extract 0 6)[j]! = hash[j]!
  rw [getElem!_pos _ _ (by simp [Array.size_extract, hsize, hj]),
    Array.getElem_extract, getElem!_pos _ _ (by omega)]
  simp only [Nat.zero_add]

theorem selectedHash_get_sha512 {hash : Array UInt64} {j : Nat} :
    (selectedHash .sha512 hash)[j]! = hash[j]! := by
  change hash[j]! = hash[j]!
  rfl

theorem hasBytes_of_words {initial t : RamState} {hash : Array UInt64} {count : Nat}
    (hsize : hash.size = count)
    (allocated : ∀ i < 8 * count,
      (t.external[initial.regValue .rcx + BitVec.ofNat 64 i]?).isSome)
    (words : ∀ j < count,
      memLoad t.external (initial.regValue .rcx + BitVec.ofNat 64 (8 * j)) 64 =
        bswap64 hash[j]!.toBitVec) :
    (⟨(initial.regValue .rcx).toNat, 8 * count⟩ : MemoryRegion).HasBytes
      t.external (serializeHash hash) := by
  refine ⟨by simp only [MemoryRegion.HasLength, serializeHash_size, hsize], ?_⟩
  intro i
  have hi : i.val < 8 * count := by
    simpa only [serializeHash_size, hsize] using i.isLt
  have wordBytes :
      Bytes t.external (initial.regValue .rcx + BitVec.ofNat 64 (8 * (i.val / 8))) 8
        (storedByte (memLoad t.external
          (initial.regValue .rcx + BitVec.ofNat 64 (8 * (i.val / 8))) 64)) := by
    apply Bytes.of_memLoad (n := 64)
    intro j hj
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using
      allocated (8 * (i.val / 8) + j) (by omega)
  have byte := wordBytes (i.val % 8) (by omega)
  rw [words (i.val / 8) (by omega)] at byte
  rw [bswap64_storedByte _ (by omega)] at byte
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at byte
  have address :
      BitVec.ofNat 64 ((initial.regValue .rcx).toNat + i.val) =
        initial.regValue .rcx + BitVec.ofNat 64 i.val := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [address]
  rw [serializeHash_getElem _ i.val (by omega)]
  simpa only [show 8 * (i.val / 8) + i.val % 8 = i.val by omega,
    UInt64.toNat_toBitVec] using byte

theorem serialize_size (v : Variant) {hash : Array UInt64} (hsize : hash.size = 8) :
    (v.serialize hash).size = v.outputBytes := by
  cases v <;> simp [Variant.serialize, serializeHash_size, Array.size_extract,
    ByteArray.size_extract, hsize, Variant.outputBytes]

theorem serialize_getElem (v : Variant) {hash : Array UInt64} (hsize : hash.size = 8)
    (i : Nat) (hi : i < (v.serialize hash).size) :
    (v.serialize hash)[i] = storedByte (bswap64 hash[i / 8]!.toBitVec) (i % 8) := by
  rw [bswap64_storedByte _ (by omega), UInt64.toNat_toBitVec]
  cases v with
  | sha384 =>
    simp only [Variant.serialize] at hi ⊢
    rw [serializeHash_getElem]
    have hj : i / 8 < 6 := by
      change i < (serializeHash (hash.extract 0 6)).size at hi
      simp only [serializeHash_size, Array.size_extract, hsize] at hi
      omega
    rw [show (hash.extract 0 6)[i / 8]! = hash[i / 8]! from
      selectedHash_get_sha384 hsize hj]
  | sha512 => exact serializeHash_getElem hash i hi
  | sha512_224 =>
    simp only [Variant.serialize] at hi ⊢
    simp only [ByteArray.getElem_extract, Nat.zero_add, serializeHash_getElem]
  | sha512_256 =>
    simp only [Variant.serialize] at hi ⊢
    simp only [ByteArray.getElem_extract, Nat.zero_add, serializeHash_getElem]

set_option maxHeartbeats 1000000 in
theorem compressed_output [Bindings] {v : Variant} {form : Form} {initial s t : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs form)
    (input : Compressed v initial s (message inputs) form) (state : State v initial t form)
    {hash : Array UInt64} (hsize : hash.size = 8)
    (serialized : v.serialize hash = v.hash (message inputs))
    (words : ∀ j, 8 * (j + 1) ≤ v.outputBytes →
      memLoad t.external (initial.regValue form.outputRegister + BitVec.ofNat 64 (8 * j)) 64 =
        bswap64 hash[j]!.toBitVec)
    (tailBytes : v = .sha512_224 → ∀ i < 4,
      t.external[initial.regValue form.outputRegister + BitVec.ofNat 64 (24 + i)]? =
        some (storedByte (bswap64 hash[3]!.toBitVec) i)) :
    (v.outputRegion initial form).HasBytes t.external (v.hash (message inputs)) := by
  have region : v.outputRegion initial form =
      ⟨(initial.regValue form.outputRegister).toNat, v.outputBytes⟩ := by
    exact v.outputRegion_eq initial form
  have allocated := ctx.outputInMemory
  rw [region] at allocated
  rw [← serialized, region]
  refine ⟨serialize_size v hsize, ?_⟩
  intro i
  have hi : i.val < v.outputBytes := by
    simpa only [serialize_size v hsize] using i.isLt
  have address : BitVec.ofNat 64 ((initial.regValue form.outputRegister).toNat + i.val) =
      initial.regValue form.outputRegister + BitVec.ofNat 64 i.val := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  change t.external[BitVec.ofNat 64 ((initial.regValue form.outputRegister).toNat + i.val)]? = _
  rw [address, serialize_getElem v hsize]
  by_cases full : 8 * (i.val / 8 + 1) ≤ v.outputBytes
  · have wordBytes : Bytes t.external
        (initial.regValue form.outputRegister + BitVec.ofNat 64 (8 * (i.val / 8))) 8
        (storedByte (memLoad t.external
          (initial.regValue form.outputRegister + BitVec.ofNat 64 (8 * (i.val / 8))) 64)) := by
      apply Bytes.of_memLoad (n := 64)
      intro j hj
      have contains := memoryRegion_contains_add allocated.2.1
        (Nat.le_refl _) (Nat.le_refl _) (show 8 * (i.val / 8) + j < (v.routine form).outputBytes by
          change _ < v.outputBytes; omega)
      obtain ⟨byte, hbyte⟩ := allocated.2.2 _ contains
      apply state.allocated
      simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, hbyte] using
        (show (initial.external[initial.regValue form.outputRegister +
          BitVec.ofNat 64 (8 * (i.val / 8) + j)]?).isSome from by rw [hbyte]; rfl)
    have byte := wordBytes (i.val % 8) (by omega)
    rw [words _ full, BitVec.add_assoc, ← BitVec.ofNat_add] at byte
    simpa only [show 8 * (i.val / 8) + i.val % 8 = i.val by omega] using byte
  · have truncated : v = .sha512_224 := by
      cases v <;> simp only [Variant.outputBytes] at hi full ⊢ <;> omega
    subst v
    have div : i.val / 8 = 3 := by change i.val < 28 at hi; change ¬ _ ≤ 28 at full; omega
    have pos : 24 + i.val % 8 = i.val := by omega
    simpa only [div, pos] using tailBytes rfl (i.val % 8) (by
      change i.val < 28 at hi; omega)

end Sha2.Proofs.Wrapper512.Finish.Serialize
