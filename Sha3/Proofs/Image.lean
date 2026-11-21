import Sha3.Spec.Program
import X86Proofs.Program.Entry

namespace Sha3.Proofs

open Sha3.Spec.Program Prelude X86

theorem chunked_getElem?_toList_of_get? {data : Bytes.Chunked} {index : Nat} {byte : UInt8}
    (h : data.get? index = some byte) : data.toList[index]? = some byte := by
  have hi : index < data.size := by
    by_cases hi : index < data.size
    · exact hi
    · simp only [Bytes.Chunked.get?, ite_eq_right hi, reduceCtorEq] at h
  simp only [Bytes.Chunked.toList, Bytes.Chunked.toListFrom, List.getElem?_map,
    List.getElem?_range' hi, Nat.one_mul, Nat.zero_add, Option.map_some,
    Bytes.Chunked.getD, h, Option.getD_some]

theorem codeRange_mem_of_getElem? {bytes : List UInt8} {index : Nat} {byte : UInt8}
    (h : bytes[index]? = some byte) (base : BitVec 64) :
    (base + BitVec.ofNat 64 index, byte) ∈ UserProcess.codeRange base bytes := by
  induction bytes generalizing base index with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at h
  | cons head tail ih =>
    cases index with
    | zero =>
      have heq : head = byte := Option.some.inj h
      subst byte
      change (base + 0, head) ∈ UserProcess.codeRange base (head :: tail)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, UserProcess.codeRange,
        List.mem_cons, true_or]
    | succ index =>
      have ht : tail[index]? = some byte := h
      have hm := ih ht (base + 1)
      apply List.mem_cons_of_mem
      simpa only [BitVec.ofNat_eq_ofNat, Nat.succ_eq_add_one, BitVec.ofNat_add,
        BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 index) (BitVec.ofNat 64 1)] using hm

theorem imageSection_mem_toCodeMap_of_fetchByte {part : ImageSection}
    {address : BitVec 64} {byte : UInt8} (h : part.fetchByte address = some byte) :
    (address, byte) ∈ part.toCodeMap := by
  have hm := codeRange_mem_of_getElem? (chunked_getElem?_toList_of_get? h) part.address
  simpa only [ImageSection.toCodeMap, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.add_comm part.address, BitVec.sub_add_cancel] using hm

theorem imageSections_mem_toCodeMap_of_fetchByte {sections : ImageSections}
    {address : BitVec 64} {byte : UInt8} (h : sections.fetchByte address = some byte) :
    (address, byte) ∈ sections.toCodeMap := by
  induction sections with
  | nil => simp only [ImageSections.fetchByte, reduceCtorEq] at h
  | cons part rest ih =>
    rcases Option.or_eq_some_iff.mp h with hsection | ⟨_, hrest⟩
    · exact List.mem_flatMap.mpr ⟨part, List.mem_cons_self,
        imageSection_mem_toCodeMap_of_fetchByte hsection⟩
    · rcases List.mem_flatMap.mp (ih hrest) with ⟨found, hfound, hbyte⟩
      exact List.mem_flatMap.mpr ⟨found, List.mem_cons_of_mem _ hfound, hbyte⟩

theorem programLoaded_fetchByte {s : Machine.RamState} (loaded : ProgramLoaded s)
    {address : BitVec 64} {byte : UInt8}
    (h : Extracted.programSections.fetchByte address = some byte) :
    s.external[address]? = some byte :=
  loaded address byte (imageSections_mem_toCodeMap_of_fetchByte h)

theorem sha3_224_firstByte : Extracted.programSections.fetchByte sha3_224_digest_slices.entryAddress = some 0x55 := by
  decide +kernel

theorem sha3_256_firstByte : Extracted.programSections.fetchByte sha3_256_digest_slices.entryAddress = some 0x55 := by
  decide +kernel

theorem sha3_384_firstByte : Extracted.programSections.fetchByte sha3_384_digest_slices.entryAddress = some 0x55 := by
  decide +kernel

theorem sha3_512_firstByte : Extracted.programSections.fetchByte sha3_512_digest_slices.entryAddress = some 0x55 := by
  decide +kernel

theorem programSections_low :
    ∀ part ∈ Extracted.programSections,
      part.address.toNat + part.bytes.size ≤ userAddressLimit := by
  decide +kernel

def wrapperPrologue (stackLowByte : UInt8) : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53,
    0x48, 0x81, 0xec, stackLowByte, 0x01, 0x00, 0x00]

theorem sha3_224_prologueBytes : Extracted.textBytes.toListFrom 0x3df0 17 = wrapperPrologue 0x18 := by
  decide +kernel

theorem sha3_256_prologueBytes : Extracted.textBytes.toListFrom 0x45a0 17 = wrapperPrologue 0x18 := by
  decide +kernel

theorem sha3_384_prologueBytes : Extracted.textBytes.toListFrom 0x4dd0 17 = wrapperPrologue 0x38 := by
  decide +kernel

theorem sha3_512_prologueBytes : Extracted.textBytes.toListFrom 0x56e0 17 = wrapperPrologue 0x58 := by
  decide +kernel

theorem textSlice_subset_programImage {offset len : Nat} {bytes : List UInt8}
    (hbound : offset + len ≤ Extracted.textBytes.size)
    (hslice : Extracted.textBytes.toListFrom offset len = bytes) :
    ∀ x ∈ UserProcess.codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes,
      x ∈ Extracted.programImage := by
  rw [← hslice, ← X86Proofs.chunked_toList_slice _ _ _ hbound]
  intro x hx
  exact List.mem_flatMap.mpr ⟨⟨Extracted.textAddress, Extracted.textBytes⟩,
    List.mem_cons_self, X86Proofs.codeRange_slice_subset _ _ offset len x hx⟩

theorem programLoaded_textSlice {s : Machine.RamState} (loaded : ProgramLoaded s)
    {offset len : Nat} {bytes : List UInt8}
    (hbound : offset + len ≤ Extracted.textBytes.size)
    (hslice : Extracted.textBytes.toListFrom offset len = bytes) :
    X86Proofs.CodeIn
      (UserProcess.codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) s :=
  (X86Proofs.CodeIn.of_loaded loaded
    (X86Proofs.SectionsLow.codeLow programSections_low)).mono
      (textSlice_subset_programImage hbound hslice)

end Sha3.Proofs
