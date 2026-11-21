import Sha1.Proofs.Buffered.Finalize.Digest.Blocks

namespace Sha1.Proofs.Buffered.Finalize.Digest

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86Proofs
open Standards.NIST Standards.NIST.SHA1 Standards.NIST.SHA2
open Sha1.Proofs.Wrapper.Absorb

theorem bytesToBits_append' (a b : ByteArray) :
    bytesToBits (a ++ b) = bytesToBits a ++ bytesToBits b := by
  simp only [bytesToBits, ByteArray.data_append, Array.flatMap_append]

theorem bytesToBits_padZeros (n : Nat) :
    bytesToBits (padZeros n) = Array.replicate (8 * n) false := by
  apply Array.ext
  · rw [Compress.Parser.bytesToBits_size, size_padZeros, Array.size_replicate]
  · intro i hi hi'
    rw [Compress.Parser.bytesToBits_getElem, Array.getElem_replicate]
    have hin : i / 8 < n := by
      rw [Compress.Parser.bytesToBits_size, size_padZeros] at hi; omega
    rw [getElem?_pos (padZeros n) (i / 8) (by rw [size_padZeros]; exact hin)]
    simp only [Option.getD_some]
    simp only [ByteArray.getElem_eq_getElem_data, padZeros, Array.getElem_replicate]
    exact BitVec.getMsbD_zero

theorem bytesToBits_marker' :
    bytesToBits (⟨#[128]⟩ : ByteArray) = #[true] ++ Array.replicate 7 false := by
  decide +kernel

theorem bytesToBits_lengthBlockBytes (message : ByteArray) :
    bytesToBits (lengthBlockBytes message) =
      (wordToBits (BitVec.ofNat 64 (bytesToBits message).size)).toArray := by
  rw [Compress.Parser.bytesToBits_size]
  apply Array.ext
  · rw [Compress.Parser.bytesToBits_size, size_lengthBlockBytes, Vector.size_toArray]
  · intro i hi hi'
    have hi8 : i < 64 := by simpa using hi'
    rw [Compress.Parser.bytesToBits_getElem]
    rw [getElem?_pos (lengthBlockBytes message) (i / 8)
      (by rw [size_lengthBlockBytes]; omega)]
    simp only [Option.getD_some, Vector.getElem_toArray, wordToBits, Vector.getElem_ofFn]
    simp only [ByteArray.getElem_eq_getElem_data, lengthBlockBytes, Array.getElem_ofFn,
      UInt8.toBitVec_ofBitVec, lengthWord]
    rw [BitVec.getMsbD_setWidth, BitVec.getMsbD_ushiftRight]
    simp only [show 8 - 64 ≤ i % 8 by omega, show i % 8 + 64 - 8 < 64 by omega,
      show ¬ i % 8 + 64 - 8 < 8 * (7 - i / 8) by omega,
      show i % 8 + 64 - 8 - 8 * (7 - i / 8) = i by omega, decide_true, decide_false,
      Bool.not_false, Bool.true_and]

theorem padZeros_append (a b : Nat) : padZeros a ++ padZeros b = padZeros (a + b) := by
  apply ByteArray.ext
  simp only [ByteArray.data_append, padZeros, Array.replicate_append_replicate]

def paddedMessage (message : ByteArray) : ByteArray :=
  message ++ ⟨#[128]⟩ ++ padZeros ((55 + 64 - message.size % 64) % 64) ++
    lengthBlockBytes message

theorem bytesToBits_paddedMessage (message : ByteArray) :
    bytesToBits (paddedMessage message) = SHA256.pad (bytesToBits message) := by
  have hk : (448 + 512 - ((bytesToBits message).size + 1) % 512) % 512 =
      7 + 8 * ((55 + 64 - message.size % 64) % 64) := by
    rw [Compress.Parser.bytesToBits_size]
    omega
  simp only [paddedMessage, bytesToBits_append', bytesToBits_marker', bytesToBits_padZeros,
    bytesToBits_lengthBlockBytes, SHA256.pad, hk]
  simp only [Array.append_assoc]
  rw [← Array.append_assoc (xs := Array.replicate 7 false), Array.replicate_append_replicate]

theorem firstBlock_extract (message : ByteArray) (h : message.size % 64 < 56) :
    (firstBlock message).extract 0 56 =
      tailBytes message ++ ⟨#[128]⟩ ++ padZeros (55 - message.size % 64) := by
  unfold firstBlock
  rw [show 63 - message.size % 64 = (55 - message.size % 64) + 8 by omega,
    ← padZeros_append, ← ByteArray.append_assoc]
  apply ByteArray.extract_append_eq_left
  rw [ByteArray.size_append, ByteArray.size_append, size_tailBytes, size_padZeros]
  change 56 = message.size % 64 + 1 + (55 - message.size % 64)
  omega

theorem paddedMessage_short (message : ByteArray) (h : message.size % 64 < 56) :
    paddedMessage message = fullBytes message ++ lastBlock message := by
  simp only [lastBlock, h, ↓reduceIte]
  rw [firstBlock_extract message h]
  unfold paddedMessage
  rw [show (55 + 64 - message.size % 64) % 64 = 55 - message.size % 64 by omega]
  simp only [← ByteArray.append_assoc, fullBytes_append_tailBytes]

theorem paddedMessage_long (message : ByteArray) (h : 56 ≤ message.size % 64) :
    paddedMessage message = fullBytes message ++ firstBlock message ++ lastBlock message := by
  have h' : ¬ message.size % 64 < 56 := by omega
  simp only [lastBlock, h', ↓reduceIte]
  rw [firstBlock]
  unfold paddedMessage
  rw [show (55 + 64 - message.size % 64) % 64 = (63 - message.size % 64) + 56 by omega,
    ← padZeros_append]
  simp only [← ByteArray.append_assoc, fullBytes_append_tailBytes]

theorem resultBytes_eq (message : ByteArray) :
    Kind.digestCopy.resultBytes message =
      Sha1.Proofs.Wrapper.Hash.Serialize.stateBytes
        (compressBlocks SHA1.initialHashValue (paddedMessage message)) := by
  simp only [Kind.resultBytes, ← bytesToBits_paddedMessage]
  rfl

theorem resultBytes_short (message : ByteArray) (h : message.size % 64 < 56) :
    Kind.digestCopy.resultBytes message =
      Sha1.Proofs.Wrapper.Hash.Serialize.stateBytes
        (compressBlocks (absorbedHash message) (lastBlock message)) := by
  rw [resultBytes_eq, paddedMessage_short message h,
    compressBlocks_append _ _ _ (fullBytes_aligned message)]
  rfl

theorem resultBytes_long (message : ByteArray) (h : 56 ≤ message.size % 64) :
    Kind.digestCopy.resultBytes message =
      Sha1.Proofs.Wrapper.Hash.Serialize.stateBytes
        (compressBlocks (compressBlocks (absorbedHash message) (firstBlock message))
          (lastBlock message)) := by
  rw [resultBytes_eq, paddedMessage_long message h,
    compressBlocks_append _ _ _ (by
      rw [ByteArray.size_append, size_firstBlock, size_fullBytes]
      omega),
    compressBlocks_append _ _ _ (fullBytes_aligned message)]
  rfl

end Sha1.Proofs.Buffered.Finalize.Digest
