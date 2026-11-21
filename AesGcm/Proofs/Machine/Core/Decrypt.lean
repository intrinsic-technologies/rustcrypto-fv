import AesGcm.Proofs.Machine.Core.Decrypt.Execution
import AesGcm.Proofs.Machine.CTR.Main

namespace AesGcm.Proofs.Machine.Core

open X86.UserProcess

theorem decrypt_call (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (nonce : Vector UInt8 12)
    (associatedData ciphertext : ByteArray) (tag : Vector UInt8 16)
    (source destination : BitVec 64) :
    DecryptCall use256 code key nonce associatedData ciphertext tag source destination := by
  apply decrypt_call_of_ctr use256 code hcode key nonce associatedData ciphertext tag source destination
  intro _ _
  exact CTR.crypt_call use256 code hcode key

end AesGcm.Proofs.Machine.Core
