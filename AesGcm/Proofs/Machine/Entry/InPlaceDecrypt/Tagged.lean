import AesGcm.Proofs.Common.Tagged
import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.Region

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem ciphertext_hasBytes {mem : Ram} {base : BitVec 64} {sealed : ByteArray}
    (h : (span base sealed.size).HasBytes mem sealed) :
    (span base (sealed.size - 16)).HasBytes mem (sealed.extract 0 (sealed.size - 16)) := by
  have hs : (sealed.extract 0 (sealed.size - 16)).size = sealed.size - 16 := by
    simp only [ByteArray.size_extract]
    omega
  refine ⟨hs, ?_⟩
  intro i
  have hi : i.val < sealed.size := by have := i.isLt; omega
  have hb := h.2 ⟨i.val, hi⟩
  dsimp only [span] at hb ⊢
  rw [hb]
  congr 1
  rw [ByteArray.getElem_extract]
  simp only [Nat.zero_add]

theorem tag_hasBytes {mem : Ram} {base : BitVec 64} {sealed : ByteArray}
    (h : (span base sealed.size).HasBytes mem sealed) (hl : 16 ≤ sealed.size)
    (hb : base.toNat + sealed.size ≤ 2^64) :
    (span (base + BitVec.ofNat 64 (sealed.size - 16)) 16).HasBytes mem
      ⟨(Vector.ofFn fun i : Fin 16 ↦ sealed[sealed.size - 16 + i.val]'(by omega)).toArray⟩ := by
  have ho : sealed.size - 16 < 2^64 := by omega
  have hsum : base.toNat + (sealed.size - 16) < 2^64 := by omega
  simp only [MemoryRegion.HasBytes, MemoryRegion.HasLength, span, AesGcm.Proofs.size_vector_byteArray]
  refine ⟨trivial, ?_⟩
  intro i
  have hi : i.val < 16 := i.isLt
  have hbytes := h.2 ⟨sealed.size - 16 + i.val, by omega⟩
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho, Nat.mod_eq_of_lt hsum, ByteArray.getElem_eq_getElem_data,
    Vector.toArray_ofFn, Array.getElem_ofFn] at ⊢
  simpa only [span, Nat.add_assoc, ByteArray.getElem_eq_getElem_data] using hbytes

theorem tag_hasBytes_of_words {before after : Ram} {source destination : BitVec 64}
    {tag : Vector UInt8 16} (hb : (span source 16).HasBytes before ⟨tag.toArray⟩)
    (hr : Readable after destination 16)
    (h0 : memLoad after destination 64 = memLoad before source 64)
    (h8 : memLoad after (destination + 8) 64 = memLoad before (source + 8) 64) :
    (span destination 16).HasBytes after ⟨tag.toArray⟩ := by
  refine ⟨by exact tag.size_toArray, ?_⟩
  intro i
  have hi : i.val < 16 := by have := i.isLt; simpa only [ByteArray.size, tag.size_toArray] using this
  have he : memByte after (destination + BitVec.ofNat 64 i.val) =
      memByte before (source + BitVec.ofNat 64 i.val) := by
    by_cases hsmall : i.val < 8
    · exact memByte_of_memLoad_eq h0 i.val hsmall
    · have hoff (a : BitVec 64) :
          a + BitVec.ofNat 64 i.val = a + 8 + BitVec.ofNat 64 (i.val - 8) := by
        change a + BitVec.ofNat 64 i.val = a + BitVec.ofNat 64 8 +
          BitVec.ofNat 64 (i.val - 8)
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        rw [show 8 + (i.val - 8) = i.val by omega]
      rw [hoff destination, hoff source]
      exact memByte_of_memLoad_eq h8 (i.val - 8) (by omega)
  have hsource := hb.2 ⟨i.val, i.isLt⟩
  simp only [span, ofNat_toNat_add] at hsource ⊢
  obtain ⟨b, htarget⟩ := Option.isSome_iff_exists.mp (hr.present i.val hi)
  change (after[destination + BitVec.ofNat 64 i.val]?).getD 0 =
    (before[source + BitVec.ofNat 64 i.val]?).getD 0 at he
  rw [htarget, hsource] at he
  exact htarget.trans (congrArg some he)

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt
