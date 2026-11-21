import Sha2.Proofs.Program
import X86Proofs.Program.Entry
import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Program.Execution

set_option autoImplicit false

open Sha2.Proofs.Program

namespace Sha2.Proofs.Common.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha2.Spec.Program

theorem supportedMachine_readyToStep [bindings : Bindings] {s : RamState}
    (h : SupportedMachine bindings s) : ReadyToStep s :=
  ReadyToStep.of_supported h.supported h.smrr h.writeBack
    (DecoderFeatures.of_supported h.supported h.leadingZeroCount)

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

theorem textBytes_size : Extracted.textBytes.size = 71757 := by
  decide +kernel

theorem rodataBytes_size : Extracted.rodataBytes.size = 680 := by
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
    have hi' : i < 680 := by simpa only [chunked_toList_length, rodataBytes_size] using hi
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

theorem programLoaded_codeIn {s : RamState} (h : ProgramLoaded s) :
    CodeIn Extracted.programSections.toCodeMap s :=
  CodeIn.of_loaded h programSections_low.codeLow

theorem stackPtr_eq_regValue_rsp (s : RamState) : stackPtr s = s.regValue .rsp := rfl

theorem stack_region_end (s : RamState) (reserve : Nat) :
    (Stack.region s reserve).start + (Stack.region s reserve).size =
      (stackPtr s).toNat + 8 := by
  change (s.regValue .rsp).toNat - reserve +
    ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - reserve)) =
      (s.regValue .rsp).toNat + 8
  omega

theorem memoryRegion_contains_add {region : MemoryRegion} {addr : BitVec 64} {len i : Nat}
    (hbound : region.Bounded) (hstart : region.start ≤ addr.toNat)
    (hend : addr.toNat + len ≤ region.start + region.size) (hi : i < len) :
    region.Contains (addr + BitVec.ofNat 64 i).toNat := by
  have hb : region.start + region.size < 2^32 := hbound
  have ha : (addr + BitVec.ofNat 64 i).toNat = addr.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2^64 by omega), Nat.mod_eq_of_lt (by omega)]
  rw [ha]
  exact ⟨by omega, by omega⟩

theorem memoryRegion_memReadable {s : RamState} {region : MemoryRegion}
    {addr : BitVec 64} {len : Nat} (hbound : region.Bounded)
    (hmem : region.Allocated s.external) (hstart : region.start ≤ addr.toNat)
    (hend : addr.toNat + len ≤ region.start + region.size) : MemReadable s addr len := by
  refine ⟨by have : region.start + region.size < 2^32 := hbound; omega, ?_⟩
  intro i hi
  obtain ⟨byte, hb⟩ := hmem _ (memoryRegion_contains_add hbound hstart hend hi)
  simp only [hb, Option.isSome_some]

end Sha2.Proofs.Common.Machine
