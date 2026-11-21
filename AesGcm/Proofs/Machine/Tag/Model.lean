import AesGcm.Proofs.Common.Detached

namespace AesGcm.Proofs.Machine.Tag

def authenticationTagFromMask (h mask : Vector UInt8 16)
    (associatedData ciphertext : ByteArray) : Vector UInt8 16 :=
  let a := AesGcm.Spec.GCM.bitsOfByteArray associatedData
  let c := AesGcm.Spec.GCM.bitsOfByteArray ciphertext
  let v := 128 * ((8 * associatedData.size + 127) / 128) - 8 * associatedData.size
  let u := 128 * ((8 * ciphertext.size + 127) / 128) - 8 * ciphertext.size
  let s := Standards.NIST.GCM.GHASH (Standards.NIST.GCM.bitsOfBytes h)
    (Standards.NIST.GCM.blocks (a ++ Standards.NIST.GCM.zeros v ++ c ++
      Standards.NIST.GCM.zeros u ++ Standards.NIST.GCM.integerToString 64 (8 * associatedData.size) ++
      Standards.NIST.GCM.integerToString 64 (8 * ciphertext.size)))
  Standards.NIST.GCM.bytesOfBits (Standards.NIST.GCM.xor s (Standards.NIST.GCM.bitsOfBytes mask))

private theorem fullTag (CIPH : Vector Bool 128 → Vector Bool 128)
    (icb s : Vector Bool 128) :
    Standards.NIST.GCM.MSB (128 : Fin 129).val
        ((Standards.NIST.GCM.GCTR CIPH icb s).cast
          (by decide : 128 = (128 : Fin 129).val + (128 - (128 : Fin 129).val))) =
      Standards.NIST.GCM.xor s (CIPH icb) := by
  apply Vector.ext
  intro i hi
  change i < 128 at hi
  simp [Standards.NIST.GCM.MSB, Standards.NIST.GCM.GCTR,
    Standards.NIST.GCM.xor, Nat.mod_eq_of_lt hi, Nat.repeat]

set_option maxRecDepth 2048 in
theorem authenticationTagFromMask_eq_standard
    (CIPH : Vector Bool 128 → Vector Bool 128) (IV : Vector Bool n)
    (h mask : Vector UInt8 16) (associatedData ciphertext : ByteArray)
    (hh : Standards.NIST.GCM.bitsOfBytes h = CIPH (Standards.NIST.GCM.zeros 128))
    (hm : Standards.NIST.GCM.bitsOfBytes mask =
      CIPH (Standards.NIST.GCM.preCounterBlock CIPH IV)) :
    authenticationTagFromMask h mask associatedData ciphertext =
      Standards.NIST.GCM.bytesOfBits (k := 16)
        (Standards.NIST.GCM.authenticationTag CIPH 128 IV
          (AesGcm.Spec.GCM.bitsOfByteArray associatedData)
          (AesGcm.Spec.GCM.bitsOfByteArray ciphertext)) := by
  unfold authenticationTagFromMask
  rw [hh, hm]
  unfold Standards.NIST.GCM.authenticationTag
  simp only [fullTag]

end AesGcm.Proofs.Machine.Tag
