import AesGcm.Spec.GCM
import Init.Data.Vector.Lemmas

namespace AesGcm.Proofs

open AesGcm.Spec
open AesGcm.Spec.GCM
open Standards.NIST.GCM

theorem gctr_involutive (CIPH : Vector Bool 128 → Vector Bool 128) (ICB : Vector Bool 128)
    (X : Vector Bool n) : GCTR CIPH ICB (GCTR CIPH ICB X) = X := by
  apply Vector.ext
  intro i hi
  simp [GCTR]

private def byteOfBits (bits : Vector Bool 8) : UInt8 :=
  ((List.finRange 8).foldl (fun (byte : Nat) (b : Fin 8) => 2 * byte + (bits[b.val]).toNat) 0).toUInt8

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem byteOfBits_bitsOfByte (byte : UInt8) :
    byteOfBits (Vector.ofFn fun j : Fin 8 => byte.toNat.testBit (7 - j.val)) = byte := by
  have h : ∀ b : Fin 256,
      byteOfBits (Vector.ofFn fun j : Fin 8 => b.val.testBit (7 - j.val)) =
        b.val.toUInt8 := by
    decide +kernel
  simpa using h ⟨byte.toNat, byte.toNat_lt⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem getBit_byteOfBits (bits : Vector Bool 8) (i : Fin 8) :
    (byteOfBits bits).toNat.testBit (7 - i.val) = bits[i.val] := by
  have h : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, ∀ j : Fin 8,
      (byteOfBits #v[b0,b1,b2,b3,b4,b5,b6,b7]).toNat.testBit (7 - j.val) =
        (#v[b0,b1,b2,b3,b4,b5,b6,b7] : Vector Bool 8)[j.val] := by
    decide +kernel
  have heq : bits = #v[bits[0],bits[1],bits[2],bits[3],bits[4],bits[5],bits[6],bits[7]] := by
    apply Vector.ext
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  conv => lhs; rw [heq]
  rw [h _ _ _ _ _ _ _ _ i]
  simp only [← heq]

theorem bitsOfBytes_bytesOfBits (bits : Vector Bool (8 * k)) :
    bitsOfBytes (bytesOfBits bits) = bits := by
  apply Vector.ext
  intro i hi
  simp only [bitsOfBytes, bytesOfBits, Vector.getElem_ofFn]
  change (byteOfBits (Vector.ofFn fun b : Fin 8 => bits[8 * (i / 8) + b.val]'(by omega))).toNat.testBit (7 - i % 8) = bits[i]
  rw [getBit_byteOfBits _ ⟨i % 8, by omega⟩]
  simp only [Vector.getElem_ofFn]
  congr 1
  omega

theorem bytesOfBits_bitsOfBytes (bytes : Vector UInt8 k) :
    bytesOfBits (bitsOfBytes bytes) = bytes := by
  apply Vector.ext
  intro i hi
  simp only [bytesOfBits, bitsOfBytes, Vector.getElem_ofFn]
  have hdiv (j : Fin 8) : (8 * i + j.val) / 8 = i := by omega
  have hmod (j : Fin 8) : (8 * i + j.val) % 8 = j.val := by omega
  simp only [hdiv, hmod]
  exact byteOfBits_bitsOfByte bytes[i]

theorem byteArrayOfBits_size (bits : Vector Bool (8 * k)) :
    (byteArrayOfBits bits).size = k := by
  simp [byteArrayOfBits, ByteArray.size]

theorem byteArrayOfBits_bitsOfByteArray (bytes : ByteArray) :
    byteArrayOfBits (bitsOfByteArray bytes) = bytes := by
  apply ByteArray.ext
  exact congrArg Vector.toArray (bytesOfBits_bitsOfBytes ⟨bytes.data, rfl⟩)

theorem bitsOfByteArray_byteArrayOfBits (bits : Vector Bool (8 * k)) :
    (bitsOfByteArray (byteArrayOfBits bits)).cast
      (by rw [byteArrayOfBits_size]) = bits := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_cast]
  simpa [bitsOfByteArray, byteArrayOfBits, Standards.NIST.GCM.bitsOfBytes] using
    congrArg (fun v : Vector Bool (8 * k) => v[i]) (bitsOfBytes_bytesOfBits bits)

private theorem gctr_cast (CIPH : Vector Bool 128 → Vector Bool 128) (ICB : Vector Bool 128)
    (X : Vector Bool n) (h : n = m) :
    GCTR CIPH ICB (X.cast h) = (GCTR CIPH ICB X).cast h := by
  cases h
  rfl

private theorem byteArrayOfBits_cast (bits : Vector Bool (8 * k)) (h : 8 * k = 8 * l) :
    byteArrayOfBits (bits.cast h) = byteArrayOfBits bits := by
  have : k = l := by omega
  subst l
  rfl

private def crypt (CIPH : Vector Bool 128 → Vector Bool 128) (ICB : Vector Bool 128)
    (bytes : ByteArray) : ByteArray := byteArrayOfBits (GCTR CIPH ICB (bitsOfByteArray bytes))

private theorem crypt_size (CIPH : Vector Bool 128 → Vector Bool 128) (ICB : Vector Bool 128)
    (bytes : ByteArray) : (crypt CIPH ICB bytes).size = bytes.size :=
  byteArrayOfBits_size _

private theorem crypt_byteArrayOfBits (CIPH : Vector Bool 128 → Vector Bool 128)
    (ICB : Vector Bool 128) (bits : Vector Bool (8 * k)) :
    crypt CIPH ICB (byteArrayOfBits bits) = byteArrayOfBits (GCTR CIPH ICB bits) := by
  have h := congrArg (fun b : Vector Bool (8 * k) => byteArrayOfBits (GCTR CIPH ICB b))
    (bitsOfByteArray_byteArrayOfBits bits)
  simpa only [gctr_cast, byteArrayOfBits_cast, crypt] using h

private theorem crypt_involutive (CIPH : Vector Bool 128 → Vector Bool 128)
    (ICB : Vector Bool 128) (bytes : ByteArray) :
    crypt CIPH ICB (crypt CIPH ICB bytes) = bytes := by
  change crypt CIPH ICB (byteArrayOfBits _) = bytes
  rw [crypt_byteArrayOfBits, gctr_involutive, byteArrayOfBits_bitsOfByteArray]

private def tagFor (CIPH : Vector Bool 128 → Vector Bool 128) (IV : Vector Bool 96)
    (associatedData ciphertext : ByteArray) : Vector UInt8 16 :=
  bytesOfBits (k := 16) (authenticationTag CIPH 128 IV (GCM.bitsOfByteArray associatedData)
    (GCM.bitsOfByteArray ciphertext))

private theorem authenticationTag_cast (CIPH : Vector Bool 128 → Vector Bool 128)
    (t : Fin 129) (IV : Vector Bool ivLen) (A : Vector Bool aLen)
    (C : Vector Bool n) (h : n = m) :
    authenticationTag CIPH t IV A (C.cast h) = authenticationTag CIPH t IV A C := by
  cases h
  rfl

private theorem tagFor_byteArrayOfBits (CIPH : Vector Bool 128 → Vector Bool 128)
    (IV : Vector Bool 96) (associatedData : ByteArray) (bits : Vector Bool (8 * k)) :
    tagFor CIPH IV associatedData (GCM.byteArrayOfBits bits) =
      bytesOfBits (k := 16) (authenticationTag CIPH 128 IV (GCM.bitsOfByteArray associatedData) bits) := by
  have h := congrArg (fun b : Vector Bool (8 * k) =>
    bytesOfBits (k := 16) (authenticationTag CIPH 128 IV (GCM.bitsOfByteArray associatedData) b))
    (bitsOfByteArray_byteArrayOfBits bits)
  simpa only [authenticationTag_cast, tagFor] using h

private theorem bitsOfBytes_eq_iff (bytes : Vector UInt8 k) (bits : Vector Bool (8 * k)) :
    bitsOfBytes bytes = bits ↔ bytes = bytesOfBits bits := by
  constructor
  · intro h
    rw [← h, bytesOfBits_bitsOfBytes]
  · intro h
    rw [h, bitsOfBytes_bytesOfBits]

private theorem ciphertextAndTag_eq (variant : Standards.NIST.AES.Variant)
    (key : Vector UInt8 variant.keyBytes) (nonce : Vector UInt8 12)
    (associatedData plaintext : ByteArray) :
    GCM.ciphertextAndTag variant key nonce associatedData plaintext =
      if GCM.lengthsSupported associatedData.size plaintext.size then
        some (crypt (GCM.forwardCipher variant key)
          (inc 32 (preCounterBlock (GCM.forwardCipher variant key) (bitsOfBytes nonce))) plaintext,
          tagFor (GCM.forwardCipher variant key) (bitsOfBytes nonce) associatedData
            (crypt (GCM.forwardCipher variant key)
              (inc 32 (preCounterBlock (GCM.forwardCipher variant key) (bitsOfBytes nonce))) plaintext))
      else none := by
  simp only [GCM.ciphertextAndTag, GCM_AE, crypt, tagFor_byteArrayOfBits]

theorem authenticPlaintext_eq (variant : Standards.NIST.AES.Variant)
    (key : Vector UInt8 variant.keyBytes) (nonce : Vector UInt8 12)
    (associatedData ciphertext : ByteArray) (tag : Vector UInt8 16) :
    GCM.authenticPlaintext variant key nonce associatedData ciphertext tag =
      if GCM.lengthsSupported associatedData.size ciphertext.size then
        if tag = tagFor (GCM.forwardCipher variant key) (bitsOfBytes nonce) associatedData ciphertext then
          some (crypt (GCM.forwardCipher variant key)
            (inc 32 (preCounterBlock (GCM.forwardCipher variant key) (bitsOfBytes nonce))) ciphertext)
        else none
      else none := by
  have ht : (128 : Fin 129).val = 128 := rfl
  simp only [GCM.authenticPlaintext, GCM_AD, GCM.supportedLengths, Nat.reduceMul,
    BEq.rfl, decide_eq_true_eq, Fin.isValue, ht, and_comm, true_and, Vector.cast_rfl,
    bitsOfBytes_eq_iff (k := 16), dite_eq_ite, GCM.lengthsSupported, Bool.and_eq_true]
  rw [← tagFor]
  split
  next hl => split <;> rfl
  next hl => rfl

theorem authenticPlaintext_eq_some_iff
    {variant : Standards.NIST.AES.Variant} {key : Vector UInt8 variant.keyBytes}
    {nonce : Vector UInt8 12} {associatedData plaintext ciphertext : ByteArray}
    {tag : Vector UInt8 16} :
    GCM.authenticPlaintext variant key nonce associatedData ciphertext tag = some plaintext ↔
      GCM.ciphertextAndTag variant key nonce associatedData plaintext = some (ciphertext, tag) := by
  rw [authenticPlaintext_eq, ciphertextAndTag_eq]
  constructor
  · intro h
    split at h
    next hl =>
      split at h
      next ht =>
        have hp := Option.some.inj h
        subst plaintext
        simp only [crypt_size, hl, ↓reduceIte, crypt_involutive, ht]
      next ht => contradiction
    next hl => contradiction
  · intro h
    split at h
    next hl =>
      obtain ⟨hc, ht⟩ := Prod.mk.inj (Option.some.inj h)
      subst ciphertext
      simp only [crypt_size, hl, ↓reduceIte, crypt_involutive, ht]
    next hl => contradiction

end AesGcm.Proofs
