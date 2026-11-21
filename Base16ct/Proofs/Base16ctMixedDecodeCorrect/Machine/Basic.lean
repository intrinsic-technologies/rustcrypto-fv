import Base16ct.Spec.Program
import Base16ct.Proofs.Copied.Md5.Proofs.Machine
import Base16ct.Proofs.Copied.Md5.Proofs.Block.Execution
namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem programSections_low : SectionsLow Extracted.programSections := by
  decide +kernel

theorem entryReady [bindings : Bindings] {s : RamState}
    (hBindings : MachineRamUnitStrideDecodable bindings s)
    (hMachine : SupportedIntegerMachineState bindings.processor s)
    (hLoaded : ProgramLoaded s) : EntryReady Extracted.programImage s :=
  EntryReady.of_sections hMachine hBindings.smrr hBindings.memoryType
    hBindings.leadingZeroCount hLoaded programSections_low

theorem program_text_slice {s : RamState} (hCode : CodeIn Extracted.programImage s)
    (offset count : Nat) (h : offset + count ≤ Extracted.textBytes.size) :
    CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset)
      (Extracted.textBytes.toListFrom offset count)) s :=
  hCode.slice_of_section
    (sec := ⟨Extracted.textAddress, Extracted.textBytes⟩)
    (by simp [Extracted.programSections]) offset count h

theorem text_address_in_program (offset : Nat) (h : offset < Extracted.textBytes.size) :
    InProgram (Extracted.textAddress + BitVec.ofNat 64 offset) := by
  have hLength : offset < Extracted.textBytes.toList.length := by
    rwa [chunked_toList_length]
  refine ⟨Extracted.textBytes.toList[offset], ?_⟩
  change _ ∈ Extracted.programSections.flatMap ImageSection.toCodeMap
  apply List.mem_flatMap.mpr
  refine ⟨⟨Extracted.textAddress, Extracted.textBytes⟩,
    by simp [Extracted.programSections], ?_⟩
  exact mem_codeRange _ _ offset hLength

theorem text_address_ne_return {boundary : ReturnBoundary} (hOutside : ¬ InProgram boundary.rip)
    (offset : Nat) (h : offset < Extracted.textBytes.size) :
    Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip := by
  intro hEq
  exact hOutside (hEq ▸ text_address_in_program offset h)

def OutsideMixed (address : BitVec 64) : Prop :=
  address.toNat < 0x1001c0 ∨ 0x10030c ≤ address.toNat

theorem outsideMixed_ne {address pc : BitVec 64} (h : OutsideMixed address)
    (hLow : 0x1001c0 ≤ pc.toNat) (hHigh : pc.toNat < 0x10030c) : pc ≠ address := by
  intro hEq
  subst pc
  unfold OutsideMixed at h
  omega

theorem outsideMixed_of_not_inProgram {address : BitVec 64}
    (h : ¬ InProgram address) : OutsideMixed address := by
  apply Classical.byContradiction
  intro hOutside
  have hLow : 0x1001c0 ≤ address.toNat := by unfold OutsideMixed at hOutside; omega
  have hHigh : address.toNat < 0x10030c := by unfold OutsideMixed at hOutside; omega
  have hSize : 0x30c ≤ Extracted.textBytes.size := by decide +kernel
  have hOffset : address.toNat - 0x100000 < Extracted.textBytes.size := by omega
  have hAddress : Extracted.textAddress + BitVec.ofNat 64 (address.toNat - 0x100000) =
      address := by
    change BitVec.ofNat 64 0x100000 + BitVec.ofNat 64 (address.toNat - 0x100000) = address
    rw [← BitVec.ofNat_add,
      show 0x100000 + (address.toNat - 0x100000) = address.toNat by omega,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact h (hAddress ▸ text_address_in_program _ hOffset)

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
