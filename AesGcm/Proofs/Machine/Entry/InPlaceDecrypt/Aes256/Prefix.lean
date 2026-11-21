import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Initialization
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.KeySchedule
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.ValidCall
import AesGcm.Proofs.Machine.Runtime.Root.Program

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Aes256

open AesGcm.Spec AesGcm.Spec.Program Prelude X86 X86.Machine X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem entryFrame {initial : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData sealed : ByteArray}
    (hCall : InPlace.ValidCall aes256gcmDecryptInPlace initial key nonce associatedData sealed
      sealed.size sealed.size) :
    ∃ ret, LIR.Aes256gcmDecryptInPlace.frameInfo.Pre Extracted.programImage
      (Activation.ofEntry initial aes256gcmDecryptInPlace.minStackBytes ret) initial := by
  obtain ⟨ret, hword, hlow, hout⟩ := hCall.returnAddress
  have hsection : LIR.rodataSection ∈ Extracted.programSections :=
    List.mem_cons_of_mem _ List.mem_cons_self
  refine ⟨ret, FrameInfo.Pre.of_sysV (m := LIR.Aes256gcmDecryptInPlace.frameInfo)
    (forbidden := fun a => InProgram a ∨ pageTables.Contains a.toNat)
    hCall.entry hCall.stack (by decide) (hCall.separation.2.2.2 _ List.mem_cons_self)
    (fun x hx => Or.inl ⟨x.2, hx⟩) (fun _ h => Or.inr (not_pageTableEntriesApart_frames h))
    (memLoad_returnSlot hword) hlow ?_
    (LIR.Aes256gcmDecryptInPlace.callSlots_loaded hsection (fun x hx => hCall.programLoaded x.1 x.2 hx))
    (fun _ a ha hb => Or.inl (LIR.Aes256gcmDecryptInPlace.callSlots_span hsection a ha hb))
    hCall.directionFlagUnset⟩
  intro x hx heq
  exact hout ⟨x.2, heq ▸ hx⟩

theorem reaches_length_check {initial : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData sealed : ByteArray} {ret : BitVec 64}
    (hCall : InPlace.ValidCall aes256gcmDecryptInPlace initial key nonce associatedData sealed
      sealed.size sealed.size)
    (hframe : LIR.Aes256gcmDecryptInPlace.frameInfo.Pre Extracted.programImage
      (Activation.ofEntry initial aes256gcmDecryptInPlace.minStackBytes ret) initial) :
    ∃ args mem, (LIR.program.sem (dialect Extracted.programImage)).Reaches
      ⟨LIR.lifted.locationOf .l101520 initial, []⟩ ⟨⟨.l101560, args, mem⟩, []⟩ ∧
      initializationPost true Extracted.programImage key
        (Activation.ofEntry initial aes256gcmDecryptInPlace.minStackBytes ret) args mem := by
  let fr := Activation.ofEntry initial aes256gcmDecryptInPlace.minStackBytes ret
  let loc := LIR.lifted.locationOf .l101520 initial
  have hatoms := hframe.entryAtoms LIR.lifted .l101520
  have hread : Readable fr.original fr.rdi 32 := by
    have hr := Readable.of_hasBytes hCall.keyInMemory.2.2 hCall.keyInMemory.2.1
    simpa only [fr, keyRegion, registerRegion, Activation.ofEntry, ByteArray.size,
      Vector.size_toArray, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hr
  have hsep : (callStack fr).Disjoint (span fr.rdi 32) := by
    have hs := hCall.separation.1 (keyRegion initial 32) (by simp)
    intro x hx hk
    apply hs x hk
    simpa only [fr, callStack, Stack.region, Activation.ofEntry_low_toNat, Stack.returnAddressBytes,
      show (Activation.ofEntry initial aes256gcmDecryptInPlace.minStackBytes ret).rsp =
        initial.regValue .rsp from rfl]
      using hx
  obtain ⟨⟨klabel, kargs, kmem⟩, hk, rfl, katoms, krbp, ktypes, kframe, ksched⟩ :=
    keySchedule_reaches true Extracted.programImage fnCode_sub_programImage key fr loc.arguments
      hatoms (GPRsTyped.locationOf _ _ _) hread hCall.keyInMemory.2.2 hsep
  obtain ⟨⟨label, args, mem⟩, hi, rfl, hinit⟩ :=
    initialization_reaches true Extracted.programImage fnCode_sub_programImage key fr kargs kmem
      katoms krbp ktypes ksched kframe
  exact ⟨args, mem, hk.trans hi, hinit⟩

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Aes256
