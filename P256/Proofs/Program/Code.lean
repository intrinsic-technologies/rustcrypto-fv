import P256.Proofs.Program.Entry
import X86Proofs.Program.Execution

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem programText_slice {s : RamState}
    (h : CodeIn Extracted.programSections.toCodeMap s)
    (offset : Nat) (bytes : List UInt8)
    (hsize : offset + bytes.length ≤ 118431)
    (hbytes : Extracted.textBytes.toListFrom offset bytes.length = bytes) :
    CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) s := by
  have hs := h.slice_of_section
    (sec := ⟨Extracted.textAddress, Extracted.textBytes⟩)
    (by simp [Extracted.programSections]) offset bytes.length
    (by simpa only [textBytes_size] using hsize)
  simpa only [hbytes] using hs

theorem boundary_ne_program {boundary : ReturnBoundary}
    (h : ¬ InProgram boundary.rip) {address : BitVec 64}
    (ha : InProgram address) : address ≠ boundary.rip :=
  fun he => h (he ▸ ha)

theorem inProgram_of_textOffset (offset : Nat) (h : offset < 118431) :
    InProgram (Extracted.textAddress + BitVec.ofNat 64 offset) := by
  let address := Extracted.textAddress + BitVec.ofNat 64 offset
  have hi : offset < Extracted.textBytes.toList.length := by
    simpa only [chunked_toList_length, textBytes_size] using h
  refine ⟨Extracted.textBytes.toList[offset], programSections_fetchByte_of_mem ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨Extracted.textAddress, Extracted.textBytes⟩,
    by simp [Extracted.programSections], ?_⟩
  exact (mem_codeRange_iff _ _ _).mpr ⟨⟨offset, hi⟩, rfl⟩

theorem imageSection_fetch_low {sec : ImageSection} {a : BitVec 64} {byte : UInt8}
    (hlow : sec.address.toNat + sec.bytes.size ≤ 2^32)
    (hf : sec.fetchByte a = some byte) : a.toNat < 2^32 := by
  have hoff : (a-sec.address).toNat < sec.bytes.size := by
    unfold ImageSection.fetchByte Bytes.Chunked.get? at hf
    split at hf
    · assumption
    · contradiction
  rw [BitVec.toNat_sub] at hoff
  have := a.isLt
  have := sec.address.isLt
  omega

theorem inProgram_low {a : BitVec 64} (h : InProgram a) : a.toNat < 2^32 := by
  obtain ⟨byte, hb⟩ := h
  change ((⟨Extracted.textAddress, Extracted.textBytes⟩ : ImageSection).fetchByte a).or
    (((⟨Extracted.rodataAddress, Extracted.rodataBytes⟩ : ImageSection).fetchByte a).or none) =
      some byte at hb
  cases ht : (⟨Extracted.textAddress, Extracted.textBytes⟩ : ImageSection).fetchByte a with
  | some v => exact imageSection_fetch_low (by decide +kernel) ht
  | none =>
    simp only [ht, Option.or_none, Option.none_or] at hb
    exact imageSection_fetch_low (by decide +kernel) hb

end P256.Proofs.Program
