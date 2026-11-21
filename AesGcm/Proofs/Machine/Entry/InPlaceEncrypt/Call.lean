import AesGcm.Spec.Program
import AesGcm.Proofs.Machine.LIR.Aes128gcmEncryptInPlace.Frame

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open AesGcm.Spec.Program Prelude X86 X86.Machine X86Proofs.Refine

def ValidCall (initial : RamState) (key : Vector UInt8 16) (nonce : Vector UInt8 12)
    (aad bytes : ByteArray) (capacity : Nat) : Prop :=
  InPlace.ValidCapacityCall aes128gcmEncryptInPlace initial key nonce aad bytes capacity ∨
    bytes = ByteArray.empty ∧
    InPlace.ValidOverCapacityCall aes128gcmEncryptInPlace initial key nonce aad capacity

abbrev entryActivation (initial : RamState) (ret : BitVec 64) :=
  Activation.ofEntry initial aes128gcmEncryptInPlace.minStackBytes ret

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
