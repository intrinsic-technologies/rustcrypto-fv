import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Call
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.KeySchedule
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Initialization
import AesGcm.Proofs.Machine.Runtime.Root.Program

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open AesGcm.Spec.Program Prelude X86 X86.Machine X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

private theorem stack_region_contains {initial : RamState} {x : Nat}
    (hx : (Stack.region initial aes128gcmEncryptInPlace.minStackBytes).Contains x) :
    (Stack.region initial aes128gcmEncryptInPlace.minStackBytes 16).Contains x := by
  simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains] at hx ⊢
  omega

private theorem reaches_core_of_entry {initial : RamState} {key : Vector UInt8 16}
    {capacity : Nat}
    (hentry : initial.RIP = aes128gcmEncryptInPlace.entryAddress)
    (hstack : Stack.Valid initial aes128gcmEncryptInPlace.minStackBytes)
    (hkeyApart : (keyRegion initial 16).Disjoint
      (Stack.region initial aes128gcmEncryptInPlace.minStackBytes 16))
    (hstackAvoids : (Stack.region initial aes128gcmEncryptInPlace.minStackBytes 16).Avoids
      (fun a => InProgram a ∨ pageTables.Contains a.toNat))
    (hloaded : ProgramLoaded initial) (hdf : DirectionFlagUnset initial)
    (hreturn : ValidReturnAddress initial)
    (hkey : ValidInput (keyRegion initial 16) initial.external ⟨key.toArray⟩)
    (hcapacity : ValidStackArgument initial capacity) :
    ∃ ret, LIR.Aes128gcmEncryptInPlace.frameInfo.Pre Extracted.programImage
      (entryActivation initial ret) initial ∧
      ∃ args mem, (LIR.program.sem (dialect Extracted.programImage)).Reaches
        ⟨LIR.lifted.locationOf .l101380 initial, []⟩ ⟨⟨.l1013c8, args, mem⟩, []⟩ ∧
        initializationPost Extracted.programImage key (entryActivation initial ret) args mem := by
  obtain ⟨ret, hword, hlow, hout⟩ := hreturn
  let fr := entryActivation initial ret
  let loc := LIR.lifted.locationOf .l101380 initial
  have hsection : LIR.rodataSection ∈ Extracted.programSections :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have hframe : LIR.Aes128gcmEncryptInPlace.frameInfo.Pre Extracted.programImage fr initial := by
    refine FrameInfo.Pre.of_sysV (m := LIR.Aes128gcmEncryptInPlace.frameInfo)
      (forbidden := fun a => InProgram a ∨ pageTables.Contains a.toNat)
      hentry hstack (by decide)
      (fun a ha => hstackAvoids a (stack_region_contains ha))
      (fun x hx => Or.inl ⟨x.2, hx⟩) (fun _ h => Or.inr (not_pageTableEntriesApart_frames h))
      (memLoad_returnSlot hword) hlow ?_
      (LIR.Aes128gcmEncryptInPlace.callSlots_loaded hsection (fun x hx => hloaded x.1 x.2 hx))
      (fun _ a ha hb => Or.inl (LIR.Aes128gcmEncryptInPlace.callSlots_span hsection a ha hb)) hdf
    intro x hx heq
    exact hout ⟨x.2, heq ▸ hx⟩
  have hread : Readable fr.original fr.rdi 16 := by
    have hr := Readable.of_hasBytes hkey.2.2 hkey.2.1
    simpa only [fr, entryActivation, Activation.ofEntry, keyRegion, registerRegion, ByteArray.size,
      Vector.size_toArray, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hr
  have hsep : (callStack fr).Disjoint (span fr.rdi 16) := by
    intro x hx hk
    have hregion : callStack fr = Stack.region initial aes128gcmEncryptInPlace.minStackBytes := by
      simp only [fr, callStack, Stack.region, Activation.ofEntry_low_toNat,
        Stack.returnAddressBytes] <;> rfl
    exact hkeyApart x hk (stack_region_contains (hregion ▸ hx))
  have hargRead : Readable fr.original (fr.rsp + 8) 8 := by
    change Readable initial.external (initial.regValue .rsp + BitVec.ofNat 64 8) 8
    rw [← ofNat_toNat_add]
    exact readable_of_word64At hcapacity.2 hcapacity.1
  obtain ⟨⟨label, args, mem⟩, hk, rfl, hatoms, hrbp, htypes, hwrites, hsched⟩ :=
    keySchedule_reaches Extracted.programImage fnCode_sub_programImage key fr loc.arguments
      (hframe.entryAtoms LIR.lifted .l101380) (GPRsTyped.locationOf _ _ _) hread hkey.2.2 hsep
  obtain ⟨⟨label, args', mem'⟩, hi, rfl, hinit⟩ :=
    initialization_reaches Extracted.programImage fnCode_sub_programImage key fr args mem
      hatoms hrbp htypes hsched hwrites hargRead
  exact ⟨ret, hframe, args', mem', hk.trans hi, hinit⟩

theorem reaches_core {initial : RamState} {key : Vector UInt8 16} {nonce : Vector UInt8 12}
    {aad bytes : ByteArray} {capacity : Nat}
    (hCall : ValidCall initial key nonce aad bytes capacity) :
    ∃ ret, LIR.Aes128gcmEncryptInPlace.frameInfo.Pre Extracted.programImage
      (entryActivation initial ret) initial ∧
      ∃ args mem, (LIR.program.sem (dialect Extracted.programImage)).Reaches
        ⟨LIR.lifted.locationOf .l101380 initial, []⟩ ⟨⟨.l1013c8, args, mem⟩, []⟩ ∧
        initializationPost Extracted.programImage key (entryActivation initial ret) args mem := by
  rcases hCall with h | ⟨_, h⟩ <;>
    exact reaches_core_of_entry h.entry h.stack
      (h.separation.1 _ List.mem_cons_self) (h.separation.2.2.2 _ List.mem_cons_self)
      h.programLoaded h.directionFlagUnset h.returnAddress h.keyInMemory h.capacityArgumentOnStack

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
