import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Decrypt.Frame
import ChaCha20Poly1305.Spec.Program
import ChaCha20Poly1305.Proofs.Common.Refine.Lemma.SysVEntry

namespace ChaCha20Poly1305.Proofs.Decrypt

open X86 X86.Machine X86.UserProcess X86Proofs Prelude
open ChaCha20Poly1305.Spec.Program

private theorem fetch_of_mem {sec : ImageSection} {x : BitVec 64 × UInt8}
    (hbound : sec.bytes.size ≤ 2^64)
    (h : x ∈ sec.toCodeMap) : sec.fetchByte x.1 = some x.2 := by
  obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).1 h
  have hi : i.val < sec.bytes.size := Nat.lt_of_lt_of_le i.isLt (Nat.le_of_eq (chunked_toList_length _))
  have hi' : i.val < 2^64 := Nat.lt_of_lt_of_le hi hbound
  change sec.bytes.get? ((sec.address + BitVec.ofNat 64 i.val - sec.address).toNat) = _
  rw [show sec.address + BitVec.ofNat 64 i.val - sec.address = BitVec.ofNat 64 i.val by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi']
  simp [Bytes.Chunked.toList, Bytes.Chunked.toListFrom, Bytes.Chunked.getD, Bytes.Chunked.get?, hi]

theorem loaded_text {x : BitVec 64 × UInt8} (hx : x ∈ Lifted.fnCode) :
    Extracted.programSections.fetchByte x.1 = some x.2 := by
  change x ∈ [Lifted.textSection].flatMap ImageSection.toCodeMap at hx
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
  have ht := fetch_of_mem (sec := Lifted.textSection) (by decide) hx
  change (Lifted.textSection.fetchByte x.1).or _ = some x.2
  rw [ht]; rfl

private theorem fetch_rodata {x : BitVec 64 × UInt8} (hx : x ∈ Lifted.rodataSection.toCodeMap) :
    Extracted.programSections.fetchByte x.1 = some x.2 := by
  have hr := fetch_of_mem (sec := Lifted.rodataSection) (by decide) hx
  obtain ⟨i, hi, he⟩ := exists_of_mem_codeRange hx
  have hi' : i < 0x100000 := Nat.lt_of_lt_of_le hi
    (Nat.le_trans (Nat.le_of_eq (chunked_toList_length _)) (by decide))
  have ht : Lifted.textSection.fetchByte x.1 = none := by
    change Extracted.textBytes.get? (x.1 - 0x100000).toNat = none
    have hstart : x.1 = 0x200000 + BitVec.ofNat 64 i := he
    have hn : ((x.1 - 0x100000).toNat) ≥ 0x100000 := by rw [hstart]; bv_omega
    have hsize : Extracted.textBytes.size ≤ 0x100000 := by decide
    simp only [Bytes.Chunked.get?, ite_eq_right (Nat.not_lt.mpr (Nat.le_trans hsize hn))]
  change (Lifted.textSection.fetchByte x.1).or ((Lifted.rodataSection.fetchByte x.1).or none) = _
  rw [ht, hr]; rfl

theorem fetch_image {x : BitVec 64 × UInt8} (h : x ∈ Extracted.programSections.toCodeMap) :
    Extracted.programSections.fetchByte x.1 = some x.2 := by
  change x ∈ [Lifted.textSection, Lifted.rodataSection].flatMap ImageSection.toCodeMap at h
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at h
  rcases h with h | h
  · apply loaded_text
    change x ∈ [Lifted.textSection].flatMap ImageSection.toCodeMap
    simp [h]
  · exact fetch_rodata h

theorem callEntry [b : Bindings] {s : RamState} {inputs : List ByteArray}
    (bindings : MachineRamUnitStrideDecodable b s)
    (machine : SupportedIntegerMachineState b.processor s)
    (h : ValidCall decrypt s inputs) : EntryReady Lifted.fnCode s :=
  EntryReady.of_sections machine bindings.smrr bindings.memoryType bindings.leadingZeroCount
    (fun a v ha => h.programLoaded a v (loaded_text ha))
    (show SectionsLow Lifted.sections by decide)

theorem callBoundary [b : Bindings] {s : RamState} {inputs : List ByteArray}
    (hready : EntryReady Lifted.fnCode s) (h : ValidCall decrypt s inputs) :
    nearReturn64Boundary s = .ok (returnBoundary s) ∧
    CFG.ReturnOutside (returnBoundary s) Lifted.fnCode := by
  obtain ⟨ret, hslot, _, hout⟩ := h.returnAddress
  have hs := h.stackAvailable
  let r := Stack.region s decrypt.minStackBytes
  have hb : r.Bounded := hs.1
  have ha : r.Allocated s.external := hs.2.1
  have hr : Refine.Readable s.external (s.regValue .rsp) 8 :=
    Refine.Readable.of_allocated hb ha (by simp [r, Stack.region]) (by
      simp [r, Stack.region, Stack.returnAddressBytes]; omega)
  constructor
  · apply nearReturn64Boundary_eq s hready.ready.dataReady hready.ready.cpu.ss
    exact ⟨hr.low, hr.present⟩
  · intro x hx he
    apply hout
    have hret := Refine.memLoad_returnSlot hslot
    change x.1 = memLoad s.external (s.regValue .rsp) 64 at he
    rw [hret] at he
    exact he ▸ ⟨x.2, loaded_text hx⟩

abbrev Forbidden (a : BitVec 64) := InProgram a ∨ pageTables.Contains a.toNat

theorem tables_forbidden (a : BitVec 64) (h : ¬ PageTableEntriesApart a.toNat 1) :
    Forbidden a := by
  right
  change 0x1000 ≤ a.toNat ∧ a.toNat < 0x1000 + 0x1020
  simp only [PageTableEntriesApart] at h
  omega

theorem code_forbidden (x : BitVec 64 × UInt8) (h : x ∈ Lifted.fnCode) : Forbidden x.1 :=
  .inl ⟨_, loaded_text h⟩

theorem callPre {s : RamState} {inputs : List ByteArray} (h : ValidCall decrypt s inputs)
    {ret : BitVec 64} (hret : (Stack.returnSlot s).Word64At s.external ret)
    (hretLow : ret.toNat < userAddressLimit) (hretOutside : ¬ InProgram ret) :
    Lifted.Decrypt.Pre Lifted.fnCode (Refine.Activation.ofEntry s decrypt.minStackBytes ret) s := by
  have hs : Lifted.rodataSection ∈ Extracted.programSections := by
    exact List.Mem.tail _ (.head _)
  apply Refine.FrameInfo.Pre.of_sysV (forbidden := Forbidden) h.atEntryPoint h.stackAvailable
    (by decide) _ code_forbidden tables_forbidden (Refine.memLoad_returnSlot hret) hretLow
  · exact fun x hx e => hretOutside (e ▸ ⟨_, loaded_text hx⟩)
  · exact Lifted.Decrypt.callSlots_loaded hs fun x hx => h.programLoaded _ _ (fetch_image hx)
  · intro _ a hlo hhi
    obtain ⟨b, hb⟩ := Lifted.Decrypt.callSlots_span hs a hlo hhi
    exact .inl ⟨b, fetch_image hb⟩
  · exact h.directionFlagUnset
  · exact h.separation.2.2 _ (by simp [writtenRegions])

end ChaCha20Poly1305.Proofs.Decrypt
