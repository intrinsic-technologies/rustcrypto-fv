import AesGcm.Proofs.Machine.GcmContext
import AesGcm.Spec.GCM

namespace AesGcm.Proofs.Machine.Core

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def BufferIn (mem : Ram) (descriptor source destination : BitVec 64) (bytes : ByteArray) : Prop :=
  Readable mem descriptor 24 ∧ memLoad mem descriptor 64 = source ∧
    memLoad mem (descriptor + 8) 64 = destination ∧
    (memLoad mem (descriptor + 16) 64).toNat = bytes.size ∧
    Readable mem source bytes.size ∧ (span source bytes.size).HasBytes mem bytes ∧
    (source = destination ∨ (span source bytes.size).Disjoint (span destination bytes.size))

def InputsIn (use256 : Bool) (key : Vector UInt8 (AES16.variant use256).keyBytes)
    (nonce : Vector UInt8 12) (associatedData : ByteArray)
    (mem : Ram) (context noncePtr aadPtr aadLength : BitVec 64) : Prop :=
  GcmContext.ContextIn (AES16.variant use256) key context mem ∧
    Readable mem context (GcmContext.size (AES16.variant use256)) ∧
    Readable mem noncePtr 12 ∧ (span noncePtr 12).HasBytes mem ⟨nonce.toArray⟩ ∧
    Readable mem aadPtr associatedData.size ∧ (span aadPtr associatedData.size).HasBytes mem associatedData ∧
    aadLength.toNat = associatedData.size

end AesGcm.Proofs.Machine.Core
