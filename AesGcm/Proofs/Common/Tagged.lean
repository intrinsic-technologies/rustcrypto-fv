import AesGcm.Spec.GCM

namespace AesGcm.Proofs

theorem size_vector_byteArray (v : Vector UInt8 n) : (⟨v.toArray⟩ : ByteArray).size = n :=
  v.size_toArray

theorem extract_ciphertext_append_tag (ciphertext : ByteArray) (tag : Vector UInt8 16) :
    (ciphertext ++ ⟨tag.toArray⟩).extract 0
      ((ciphertext ++ ⟨tag.toArray⟩).size - 16) = ciphertext := by
  apply ByteArray.extract_append_eq_left
  simp only [ByteArray.size_append, size_vector_byteArray, Nat.add_sub_cancel]

theorem tag_of_ciphertext_append_tag (ciphertext : ByteArray) (tag : Vector UInt8 16) :
    (Vector.ofFn fun i : Fin 16 =>
      (ciphertext ++ ⟨tag.toArray⟩)[(ciphertext ++ ⟨tag.toArray⟩).size - 16 + i.val]'(by
        simp only [ByteArray.size_append, size_vector_byteArray, Nat.add_sub_cancel]
        omega)) = tag := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, ByteArray.size_append, size_vector_byteArray,
    Nat.add_sub_cancel]
  rw [ByteArray.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left, ByteArray.getElem_eq_getElem_data,
    Vector.getElem_toArray]

theorem ciphertext_tag_reconstruction (sealed : ByteArray) (h : 16 ≤ sealed.size) :
    sealed.extract 0 (sealed.size - 16) ++
      ⟨(Vector.ofFn fun i : Fin 16 =>
        sealed[sealed.size - 16 + i.val]'(by omega)).toArray⟩ = sealed := by
  apply ByteArray.ext_getElem
  · simp only [ByteArray.size_append, ByteArray.size_extract, size_vector_byteArray]
    omega
  · intro i hi hi'
    by_cases hfront : i < sealed.size - 16
    · rw [ByteArray.getElem_append_left]
      · simpa only [Nat.zero_add] using ByteArray.getElem_extract (i := i) (b := sealed)
          (start := 0) (stop := sealed.size - 16) (by simp only [ByteArray.size_extract]; omega)
    · rw [ByteArray.getElem_append_right]
      · simp only [ByteArray.size_extract, Nat.sub_zero,
          ByteArray.getElem_eq_getElem_data, Vector.toArray_ofFn, Array.getElem_ofFn]
        congr 1
        omega
      · simp only [ByteArray.size_extract]
        omega

open AesGcm.Spec

theorem authenticPlaintextOfCiphertextWithTag_append
    (variant : Standards.NIST.AES.Variant) (key : Vector UInt8 variant.keyBytes)
    (nonce : Vector UInt8 12) (associatedData ciphertext : ByteArray) (tag : Vector UInt8 16) :
    GCM.authenticPlaintextOfCiphertextWithTag variant key nonce associatedData
        (ciphertext ++ ⟨tag.toArray⟩) =
      GCM.authenticPlaintext variant key nonce associatedData ciphertext tag := by
  unfold GCM.authenticPlaintextOfCiphertextWithTag
  rw [dite_eq_left (by simp only [ByteArray.size_append, size_vector_byteArray]; omega)]
  rw [extract_ciphertext_append_tag, tag_of_ciphertext_append_tag]

theorem authenticPlaintextOfCiphertextWithTag_eq_some_iff
    {variant : Standards.NIST.AES.Variant} {key : Vector UInt8 variant.keyBytes}
    {nonce : Vector UInt8 12} {associatedData plaintext sealed : ByteArray} :
    GCM.authenticPlaintextOfCiphertextWithTag variant key nonce associatedData sealed =
        some plaintext ↔
      ∃ ciphertext tag, sealed = ciphertext ++ ⟨tag.toArray⟩ ∧
        GCM.authenticPlaintext variant key nonce associatedData ciphertext tag = some plaintext := by
  constructor
  · intro h
    unfold GCM.authenticPlaintextOfCiphertextWithTag at h
    split at h
    next hsize =>
      exact ⟨_, _, (ciphertext_tag_reconstruction sealed hsize).symm, h⟩
    next hsize => contradiction
  · rintro ⟨ciphertext, tag, rfl, h⟩
    rw [authenticPlaintextOfCiphertextWithTag_append]
    exact h

end AesGcm.Proofs
