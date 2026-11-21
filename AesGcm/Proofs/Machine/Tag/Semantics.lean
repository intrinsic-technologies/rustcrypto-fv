import AesGcm.Proofs.Machine.Tag.Model

namespace AesGcm.Proofs.Machine.Tag
open Standards.NIST.GCM
open AesGcm.Spec.GCM

theorem preCounterBlock_nonce96 (cipher : Vector Bool 128 → Vector Bool 128)
    (nonce : Vector UInt8 12) :
    preCounterBlock cipher (bitsOfBytes nonce) = bitsOfBytes nonce ++ zeros 31 ++ #v[true] := by
  simp only [preCounterBlock, ↓reduceDIte, Vector.cast_rfl]

theorem bitsOfBytes_nonce96_counter_one (cipher : Vector Bool 128 → Vector Bool 128)
    (nonce : Vector UInt8 12) :
    bitsOfBytes (nonce ++ (#v[0, 0, 0, 1] : Vector UInt8 4)) = preCounterBlock cipher (bitsOfBytes nonce) := by
  rw [preCounterBlock_nonce96]
  have happend : bitsOfBytes (nonce ++ (#v[0, 0, 0, 1] : Vector UInt8 4)) =
      bitsOfBytes nonce ++ bitsOfBytes (#v[0, 0, 0, 1] : Vector UInt8 4) := by
    apply Vector.ext
    intro i hi
    by_cases h : i < 96
    · rw [Vector.getElem_append_left h]
      simp only [bitsOfBytes, Vector.getElem_ofFn]
      rw [Vector.getElem_append_left (by omega)]
    · rw [Vector.getElem_append_right (by omega) (by omega : 96 ≤ i)]
      simp only [bitsOfBytes, Vector.getElem_ofFn]
      rw [Vector.getElem_append_right (by omega) (by omega : 12 ≤ i / 8)]
      have hd : i / 8 - 12 = (i - 96) / 8 := by omega
      have hm : i % 8 = (i - 96) % 8 := by omega
      simp only [hd, hm]
  rw [happend]
  have hs : bitsOfBytes (#v[0, 0, 0, 1] : Vector UInt8 4) = zeros 31 ++ #v[true] := by
    decide +kernel
  rw [hs, Vector.append_assoc]
  rfl

theorem ciphertextAndTag_eq_some (variant : Standards.NIST.AES.Variant)
    (key : Vector UInt8 variant.keyBytes) (nonce : Vector UInt8 12)
    (associatedData plaintext ciphertext : ByteArray) (h mask : Vector UInt8 16)
    (hlengths : lengthsSupported associatedData.size plaintext.size = true)
    (hciphertext : ciphertext = byteArrayOfBits
      (GCTR (forwardCipher variant key)
        (inc 32 (preCounterBlock (forwardCipher variant key) (bitsOfBytes nonce)))
        (bitsOfByteArray plaintext)))
    (hh : bitsOfBytes h = forwardCipher variant key (zeros 128))
    (hm : bitsOfBytes mask = forwardCipher variant key
      (preCounterBlock (forwardCipher variant key) (bitsOfBytes nonce))) :
    ciphertextAndTag variant key nonce associatedData plaintext =
      some (ciphertext, authenticationTagFromMask h mask associatedData ciphertext) := by
  subst ciphertext
  rw [authenticationTagFromMask_eq_standard _ _ _ _ _ _ hh hm]
  simp only [ciphertextAndTag, hlengths, ↓reduceIte, GCM_AE]
  apply congrArg some
  apply Prod.ext
  · rfl
  apply congrArg (bytesOfBits (k := 16))
  have hc := AesGcm.Proofs.bitsOfByteArray_byteArrayOfBits
    (GCTR (forwardCipher variant key)
      (inc 32 (preCounterBlock (forwardCipher variant key) (bitsOfBytes nonce)))
      (bitsOfByteArray plaintext))
  have hc' (n m : Nat) (bits : Vector Bool n) (he : n = m) :
      authenticationTag (forwardCipher variant key) 128 (bitsOfBytes nonce)
        (bitsOfByteArray associatedData) (bits.cast he) =
      authenticationTag (forwardCipher variant key) 128 (bitsOfBytes nonce)
        (bitsOfByteArray associatedData) bits := by
    cases he
    rfl
  conv => lhs; rw [← hc, hc']

theorem authenticPlaintext_eq_tag (variant : Standards.NIST.AES.Variant)
    (key : Vector UInt8 variant.keyBytes) (nonce : Vector UInt8 12)
    (associatedData ciphertext : ByteArray) (tag h mask : Vector UInt8 16)
    (hh : bitsOfBytes h = forwardCipher variant key (zeros 128))
    (hm : bitsOfBytes mask = forwardCipher variant key
      (preCounterBlock (forwardCipher variant key) (bitsOfBytes nonce))) :
    authenticPlaintext variant key nonce associatedData ciphertext tag =
      if lengthsSupported associatedData.size ciphertext.size then
        if tag = authenticationTagFromMask h mask associatedData ciphertext then
          some (byteArrayOfBits (GCTR (forwardCipher variant key)
            (inc 32 (preCounterBlock (forwardCipher variant key) (bitsOfBytes nonce)))
            (bitsOfByteArray ciphertext)))
        else none
      else none := by
  rw [authenticationTagFromMask_eq_standard _ _ _ _ _ _ hh hm]
  exact AesGcm.Proofs.authenticPlaintext_eq variant key nonce associatedData ciphertext tag

end AesGcm.Proofs.Machine.Tag
