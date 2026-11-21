import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Initialization
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.KeySchedule
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.ValidCall
import AesGcm.Proofs.Machine.Runtime.Root.Program

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt

open AesGcm.Spec AesGcm.Spec.Program Prelude X86 X86.Machine X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem reaches_length_check {initial : RamState} {key : Vector UInt8 16} {nonce : Vector UInt8 12}
    {associatedData sealed : ByteArray} {ret : BitVec 64}
    (hCall : InPlace.ValidCall aes128gcmDecryptInPlace initial key nonce associatedData sealed
      sealed.size sealed.size)
    (hframe : LIR.Aes128gcmDecryptInPlace.frameInfo.Pre Extracted.programImage
      (Activation.ofEntry initial aes128gcmDecryptInPlace.minStackBytes ret) initial) :
    ∃ args mem, (LIR.program.sem (dialect Extracted.programImage)).Reaches
      ⟨LIR.lifted.locationOf .l101240 initial, []⟩ ⟨⟨.l101280, args, mem⟩, []⟩ ∧
      initializationPost false Extracted.programImage key
        (Activation.ofEntry initial aes128gcmDecryptInPlace.minStackBytes ret) args mem := by
  let fr := Activation.ofEntry initial aes128gcmDecryptInPlace.minStackBytes ret
  let loc := LIR.lifted.locationOf .l101240 initial
  have hatoms := hframe.entryAtoms LIR.lifted .l101240
  have hread : Readable fr.original fr.rdi 16 := by
    have hr := Readable.of_hasBytes hCall.keyInMemory.2.2 hCall.keyInMemory.2.1
    simpa only [fr, keyRegion, registerRegion, Activation.ofEntry, ByteArray.size,
      Vector.size_toArray, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hr
  have hsep : (callStack fr).Disjoint (span fr.rdi 16) := by
    have hs := hCall.separation.1 (keyRegion initial 16) (by simp)
    intro x hx hk
    apply hs x hk
    simpa only [fr, callStack, Stack.region, Activation.ofEntry_low_toNat, Stack.returnAddressBytes,
      show (Activation.ofEntry initial aes128gcmDecryptInPlace.minStackBytes ret).rsp =
        initial.regValue .rsp from rfl]
      using hx
  obtain ⟨⟨klabel, kargs, kmem⟩, hk, rfl, katoms, krbp, ktypes, kframe, ksched⟩ :=
    keySchedule_reaches false Extracted.programImage fnCode_sub_programImage key fr loc.arguments
      hatoms (GPRsTyped.locationOf _ _ _) hread hCall.keyInMemory.2.2 hsep
  obtain ⟨⟨label, args, mem⟩, hi, rfl, hinit⟩ :=
    initialization_reaches false Extracted.programImage fnCode_sub_programImage key fr kargs kmem
      katoms krbp ktypes ksched kframe
  exact ⟨args, mem, hk.trans hi, hinit⟩

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt
