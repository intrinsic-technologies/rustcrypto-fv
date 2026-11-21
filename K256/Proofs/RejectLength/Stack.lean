import K256.Proofs.LIR.SignatureFromSlice.Frame
import K256.Spec.Program
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.SignatureSlice

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift K256.Proofs.Refine

private theorem storeOk_of_text {mem : Ram} {address instruction : BitVec 64}
    {bytes instructionBytes : Nat}
    (hw : Writable Extracted.programImage mem address bytes)
    (hstart : LIR.textSection.address.toNat ≤ instruction.toNat)
    (hend : instruction.toNat + instructionBytes ≤
      LIR.textSection.address.toNat + LIR.textSection.bytes.size) :
    StoreOk Extracted.programImage mem address bytes instruction instructionBytes := by
  refine ⟨hw.readable.low, hw.readable.present, hw.tables, ?_, hw.notCode⟩
  intro i hi j hj he
  have hs : LIR.textSection ∈ Extracted.programSections := .head _
  have h64 : LIR.textSection.address.toNat + LIR.textSection.bytes.size ≤ 2 ^ 64 := by
    decide +kernel
  have ha : (instruction + BitVec.ofNat 64 j).toNat = instruction.toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  obtain ⟨b, hb⟩ := exists_mem_toCodeMap hs (show LIR.textSection.address.toNat ≤
    (instruction + BitVec.ofNat 64 j).toNat by omega)
    (show (instruction + BitVec.ofNat 64 j).toNat <
        LIR.textSection.address.toNat + LIR.textSection.bytes.size by omega)
  exact hw.notCode _ hb i hi he.symm

theorem rejectStack {s : RamState} {ret : BitVec 64}
    (hstack : Stack.Valid s signatureFromSlice.minStackBytes)
    (hframe : LIR.SignatureFromSlice.Pre Extracted.programImage
      (Activation.ofEntry s signatureFromSlice.minStackBytes ret) s) :
    let sp := s.regValue .rsp
    let bx := s.regValue .rbx
    let save := memStore s.external (sp - 8) bx
    let empty := memStore save (sp - 72) (0 : BitVec 64)
    StoreOk Extracted.programImage s.external (sp - 8) 8 0x102450 1 ∧
    StoreOk Extracted.programImage save (sp - 72) 8 0x1024d6 9 ∧
    LoadOk empty (sp - 72) 8 ∧ memLoad empty (sp - 72) 64 = 0 ∧
    LoadOk empty (sp - 8) 8 ∧ memLoad empty (sp - 8) 64 = bx ∧
    LoadOk empty sp 8 ∧ memLoad empty sp 64 = ret ∧
    RamWriteFrame s.external empty [Stack.region s signatureFromSlice.minStackBytes] := by
  intro sp bx save empty
  have hwindow : Writable Extracted.programImage s.external (sp - 656) 656 :=
    hframe.window (by decide)
  have hsave : Writable Extracted.programImage s.external (sp - 8) 8 :=
    hwindow.of_offsets (addr_sub sp 8) (addr_sub sp 656) (by decide)
  have hempty : Writable Extracted.programImage s.external (sp - 72) 8 :=
    hwindow.of_offsets (addr_sub sp 72) (addr_sub sp 656) (by decide)
  have hslot : Readable s.external sp 8 := hframe.slot
  have hroom : 784 ≤ sp.toNat := hstack.2.2.1
  have within (offset : Nat) (hmin : 8 ≤ offset) (hmax : offset ≤ 784) :
      InRegions [Stack.region s signatureFromSlice.minStackBytes] (sp - BitVec.ofNat 64 offset) 8 := by
    have ho : (BitVec.ofNat 64 offset).toNat = offset := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have ha : (sp - BitVec.ofNat 64 offset).toNat = sp.toNat - offset := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ho]; omega), ho]
    refine ⟨_, List.mem_cons_self, ?_⟩
    change sp.toNat - 784 ≤ _ ∧ _ + 8 ≤
      sp.toNat - 784 + (sp.toNat + 8 - (sp.toNat - 784)) ∧ _ + 8 ≤ 2 ^ 64
    rw [ha]
    have := hslot.low
    omega
  have hwrite : RamWriteFrame s.external empty [Stack.region s signatureFromSlice.minStackBytes] :=
    ((RamWriteFrame.refl _ _).memStore bx (within 8 (by decide) (by decide))).memStore
      (0 : BitVec 64) (within 72 (by decide) (by decide))
  have hsaveRead := hsave.readable.of_frame hwrite
  have hemptyRead := hempty.readable.of_frame hwrite
  have hretRead := hslot.of_frame hwrite
  have hemptySave : RangeApart (sp - 72) 8 (sp - 8) 8 :=
    RangeApart.of_offsets (addr_sub sp 72) (addr_sub sp 8) (by decide)
  have hemptyRet : RangeApart (sp - 72) 8 sp 8 :=
    RangeApart.of_offsets (addr_sub sp 72) (addr_self sp) (by decide)
  have hsaveRet : RangeApart (sp - 8) 8 sp 8 :=
    RangeApart.of_offsets (addr_sub sp 8) (addr_self sp) (by decide)
  refine ⟨storeOk_of_text hsave (by decide) (by decide +kernel),
    storeOk_of_text (hempty.memStore (sp - 8) bx) (by decide) (by decide +kernel),
    ⟨hemptyRead.low, hemptyRead.present⟩,
    memLoad_memStore_same save _ _ (by decide) (by decide),
    ⟨hsaveRead.low, hsaveRead.present⟩, ?_,
    ⟨hretRead.low, hretRead.present⟩, ?_, hwrite⟩
  · rw [memLoad_memStore_of_rangeApart save _ _ _ _ hemptySave]
    exact memLoad_memStore_same s.external _ _ (by decide) (by decide)
  · rw [memLoad_memStore_of_rangeApart save _ _ _ _ hemptyRet]
    rw [memLoad_memStore_of_rangeApart s.external _ _ _ _ hsaveRet]
    exact hframe.ret

end K256.Proofs.SignatureSlice
