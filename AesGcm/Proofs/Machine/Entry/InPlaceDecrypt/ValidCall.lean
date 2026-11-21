import AesGcm.Proofs.Machine.LIR.Aes128gcmDecryptInPlace.Frame
import AesGcm.Spec.Program

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt

open AesGcm.Spec.Program Prelude X86 X86.Machine X86Proofs X86Proofs.Lift X86Proofs.Refine

theorem entryFrame {initial : RamState} {key : Vector UInt8 16} {nonce : Vector UInt8 12}
    {associatedData sealed : ByteArray}
    (hCall : InPlace.ValidCall aes128gcmDecryptInPlace initial key nonce associatedData sealed
      sealed.size sealed.size) :
    ∃ ret, LIR.Aes128gcmDecryptInPlace.frameInfo.Pre Extracted.programImage
      (Activation.ofEntry initial aes128gcmDecryptInPlace.minStackBytes ret) initial := by
  obtain ⟨ret, hword, hlow, hout⟩ := hCall.returnAddress
  have hsection : LIR.rodataSection ∈ Extracted.programSections :=
    List.mem_cons_of_mem _ List.mem_cons_self
  refine ⟨ret, FrameInfo.Pre.of_sysV (m := LIR.Aes128gcmDecryptInPlace.frameInfo)
    (forbidden := fun a => InProgram a ∨ pageTables.Contains a.toNat)
    hCall.entry hCall.stack (by decide) (hCall.separation.2.2.2 _ List.mem_cons_self)
    (fun x hx => Or.inl ⟨x.2, hx⟩) (fun _ h => Or.inr (not_pageTableEntriesApart_frames h))
    (memLoad_returnSlot hword) hlow ?_
    (LIR.Aes128gcmDecryptInPlace.callSlots_loaded hsection (fun x hx => hCall.programLoaded x.1 x.2 hx))
    (fun _ a ha hb => Or.inl (LIR.Aes128gcmDecryptInPlace.callSlots_span hsection a ha hb))
    hCall.directionFlagUnset⟩
  intro x hx heq
  exact hout ⟨x.2, heq ▸ hx⟩

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt
