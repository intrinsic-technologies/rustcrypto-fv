import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.CoreExec
import AesGcm.Proofs.Machine.Core.Decrypt

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt

open AesGcm.Spec AesGcm.Spec.Program Prelude X86 X86.Machine X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine

theorem exec_with_tag {initial : RamState} {key : Vector UInt8 16} {nonce : Vector UInt8 12}
    {associatedData sealed : ByteArray} {ret : BitVec 64}
    (hCall : InPlace.ValidCall aes128gcmDecryptInPlace initial key nonce associatedData sealed
      sealed.size sealed.size)
    (_hframe : LIR.Aes128gcmDecryptInPlace.frameInfo.Pre Extracted.programImage
      (Activation.ofEntry initial aes128gcmDecryptInPlace.minStackBytes ret) initial)
    (args : Values Value Reg.count) (mem : Ram)
    (hInit : initializationPost false Extracted.programImage key
      (Activation.ofEntry initial aes128gcmDecryptInPlace.minStackBytes ret) args mem)
    (hsize : 16 ≤ sealed.size) :
    ∃ output, LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l101280, args, mem⟩, []⟩ output ∧
      resultPost Extracted.programImage (Activation.ofEntry initial aes128gcmDecryptInPlace.minStackBytes ret)
        (sealed.size - 16) (GCM.authenticPlaintextOfCiphertextWithTag .aes128 key nonce associatedData sealed) output := by
  apply core_exec hCall args mem hInit hsize
  exact Core.decrypt_call false _ Runtime.fnCode_sub_programImage key nonce associatedData _ _ _ _

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt
