import K256.Spec.Program
import X86Proofs.Program.Entry

namespace K256.Proofs.Common

open K256.Spec.Program Prelude X86 X86.UserProcess X86Proofs

def InImage (address : BitVec 64) : Prop :=
  ∃ byte, (address, byte) ∈ Extracted.programImage

def InPageTables (address : BitVec 64) : Prop :=
  ∃ region ∈ #v[(⟨0x1000, 8⟩ : MemoryRegion), ⟨0x2000, 32⟩], region.Contains address.toNat

theorem programSections_low : SectionsLow Extracted.programSections := by
  decide +kernel

theorem imageSection_fetchByte_of_mem {sec : ImageSection} {address : BitVec 64} {byte : UInt8}
    (hlow : sec.address.toNat + sec.bytes.size ≤ 2^64)
    (hmem : (address, byte) ∈ sec.toCodeMap) : sec.fetchByte address = some byte := by
  obtain ⟨i, he⟩ := (mem_codeRange_iff sec.address sec.bytes.toList (address, byte)).mp hmem
  have hi : i.val < sec.bytes.size := by
    simpa only [chunked_toList_length] using i.isLt
  have hi64 : i.val < 2^64 := by omega
  cases he
  rw [ImageSection.fetchByte, BitVec.add_comm sec.address, BitVec.add_sub_cancel,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
  simp [Bytes.Chunked.toList, Bytes.Chunked.toListFrom, Bytes.Chunked.getD,
    Bytes.Chunked.get?, hi]

theorem textBytes_size : Extracted.textBytes.size = 174527 := by
  decide +kernel

theorem rodataBytes_size : Extracted.rodataBytes.size = 15952 := by
  decide +kernel

theorem programSections_fetchByte_of_mem {address : BitVec 64} {byte : UInt8}
    (hmem : (address, byte) ∈ Extracted.programSections.toCodeMap) :
    Extracted.programSections.fetchByte address = some byte := by
  simp only [ImageSections.toCodeMap, Extracted.programSections, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.mem_append] at hmem
  rcases hmem with ht | hr
  · have hf := imageSection_fetchByte_of_mem (by decide +kernel) ht
    change (ImageSection.fetchByte ⟨Extracted.textAddress, Extracted.textBytes⟩ address).or
      _ = some byte
    rw [hf]
    rfl
  · have hf := imageSection_fetchByte_of_mem (by decide +kernel) hr
    obtain ⟨i, hi, he⟩ := exists_of_mem_codeRange hr
    have hi' : i < 15952 := by simpa only [chunked_toList_length, rodataBytes_size] using hi
    change address = Extracted.rodataAddress + BitVec.ofNat 64 i at he
    have ha : address.toNat = 2097152 + i := by
      rw [he, BitVec.toNat_add, BitVec.toNat_ofNat]
      change (2097152 + i % 18446744073709551616) % 18446744073709551616 = _
      omega
    have hn : (⟨Extracted.textAddress, Extracted.textBytes⟩ : ImageSection).fetchByte address =
        none := by
      unfold ImageSection.fetchByte Bytes.Chunked.get?
      have hb : ¬ (address - Extracted.textAddress).toNat < Extracted.textBytes.size := by
        rw [textBytes_size, BitVec.toNat_sub,
          show Extracted.textAddress.toNat = 1048576 from rfl]
        omega
      simp only [hb, ↓reduceIte]
    change (ImageSection.fetchByte ⟨Extracted.textAddress, Extracted.textBytes⟩ address).or
      ((ImageSection.fetchByte ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩ address).or none) = _
    rw [hn, hf]
    rfl

theorem inProgram_of_inImage {address : BitVec 64} (h : InImage address) : InProgram address :=
  let ⟨byte, hmem⟩ := h
  ⟨byte, programSections_fetchByte_of_mem hmem⟩

theorem not_inImage_of_not_inProgram {address : BitVec 64} (h : ¬ InProgram address) :
    ¬ InImage address :=
  fun hi ↦ h (inProgram_of_inImage hi)

theorem not_inPageTables_of_disjoint {address : BitVec 64}
    (h : ¬ pageTables.Contains address.toNat) : ¬ InPageTables address := by
  rintro ⟨region, hr, hc⟩
  apply h
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl <;>
    simp only [MemoryRegion.Contains, pageTables] at hc ⊢ <;> omega

theorem programLoaded_codeIn {s : Machine.RamState} (h : ProgramLoaded s) :
    CodeIn Extracted.programImage s :=
  CodeIn.of_loaded (fun _ _ hmem => h _ _ (programSections_fetchByte_of_mem hmem))
    programSections_low.codeLow

end K256.Proofs.Common
