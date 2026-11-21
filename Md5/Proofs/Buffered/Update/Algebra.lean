import Md5.Proofs.Buffered.Invariant

namespace Md5.Proofs.Buffered

open Md5.Spec

theorem fullBytes_append_aligned (a b : ByteArray) (ha : a.size % 64 = 0) :
    fullBytes (a ++ b) = a ++ fullBytes b := by
  have hcut : (a.size + b.size) / 64 * 64 = a.size + b.size / 64 * 64 := by omega
  simp only [fullBytes, ByteArray.size_append, hcut, ByteArray.extract_append]
  simp only [Nat.zero_sub, Nat.add_sub_cancel_left]
  rw [show a.size + b.size / 64 * 64 = max (a.size + b.size / 64 * 64) a.size by omega,
    ByteArray.extract_zero_max_size]

theorem tailBytes_append_aligned (a b : ByteArray) (ha : a.size % 64 = 0) :
    tailBytes (a ++ b) = tailBytes b := by
  have hcut : (a.size + b.size) / 64 * 64 = a.size + b.size / 64 * 64 := by omega
  simp only [tailBytes, ByteArray.size_append, hcut, ByteArray.extract_append_size_add]

theorem fullBytes_append (message input : ByteArray) :
    fullBytes (message ++ input) =
      fullBytes message ++ fullBytes (tailBytes message ++ input) := by
  conv => lhs; rw [← fullBytes_append_tailBytes message, ByteArray.append_assoc]
  exact fullBytes_append_aligned _ _ (fullBytes_aligned message)

theorem tailBytes_append (message input : ByteArray) :
    tailBytes (message ++ input) = tailBytes (tailBytes message ++ input) := by
  conv => lhs; rw [← fullBytes_append_tailBytes message, ByteArray.append_assoc]
  exact tailBytes_append_aligned _ _ (fullBytes_aligned message)

theorem absorbedBuffer_append (message input : ByteArray) :
    absorbedBuffer (message ++ input) =
      Standards.RFC.MD5.processBlocks (absorbedBuffer message)
        (Standards.RFC.MD5.wordsOfBytes (fullBytes (tailBytes message ++ input))) := by
  rw [absorbedBuffer, fullBytes_append,
    RFC1321.processBlocks_wordsOfBytes_append _ _ _ (fullBytes_aligned message)]
  rfl

theorem fullBytes_of_size_lt (input : ByteArray) (h : input.size < 64) :
    fullBytes input = ByteArray.empty := by
  simp only [fullBytes, Nat.div_eq_of_lt h, Nat.zero_mul, ByteArray.extract_same]

theorem tailBytes_of_size_lt (input : ByteArray) (h : input.size < 64) :
    tailBytes input = input := by
  simp only [tailBytes, Nat.div_eq_of_lt h, Nat.zero_mul, ByteArray.extract_zero_size]

theorem absorbedBuffer_append_short (message input : ByteArray)
    (h : message.size % 64 + input.size < 64) :
    absorbedBuffer (message ++ input) = absorbedBuffer message := by
  have htail : (tailBytes message ++ input).size < 64 := by
    simpa only [ByteArray.size_append, size_tailBytes] using h
  rw [absorbedBuffer_append, fullBytes_of_size_lt _ htail]
  exact RFC1321.processBlocks_empty _

theorem tailBytes_append_short (message input : ByteArray)
    (h : message.size % 64 + input.size < 64) :
    tailBytes (message ++ input) = tailBytes message ++ input := by
  rw [tailBytes_append]
  apply tailBytes_of_size_lt
  simpa only [ByteArray.size_append, size_tailBytes] using h

theorem fullBytes_of_aligned (input : ByteArray) (h : input.size % 64 = 0) :
    fullBytes input = input := by
  have hcut : input.size / 64 * 64 = input.size := by omega
  simp only [fullBytes, hcut, ByteArray.extract_zero_size]

theorem tailBytes_of_aligned (input : ByteArray) (h : input.size % 64 = 0) :
    tailBytes input = ByteArray.empty := by
  have hcut : input.size / 64 * 64 = input.size := by omega
  simp only [tailBytes, hcut, ByteArray.extract_same]

theorem absorbedBuffer_append_aligned (message input : ByteArray)
    (h : message.size % 64 = 0) :
    absorbedBuffer (message ++ input) =
      Standards.RFC.MD5.processBlocks (absorbedBuffer message)
        (Standards.RFC.MD5.wordsOfBytes (fullBytes input)) := by
  rw [absorbedBuffer_append, tailBytes_of_aligned _ h, ByteArray.empty_append]

def updateBlock (message input : ByteArray) : ByteArray :=
  tailBytes message ++ input.extract 0 (64 - message.size % 64)

def updateRemainder (message input : ByteArray) : ByteArray :=
  input.extract (64 - message.size % 64) input.size

theorem updateBlock_append_updateRemainder (message input : ByteArray)
    (h : 64 - message.size % 64 ≤ input.size) :
    updateBlock message input ++ updateRemainder message input = tailBytes message ++ input := by
  simp only [updateBlock, updateRemainder, ByteArray.append_assoc,
    ByteArray.extract_append_extract, Nat.zero_min, Nat.max_eq_right h,
    ByteArray.extract_zero_size]

theorem size_updateBlock (message input : ByteArray)
    (h : 64 - message.size % 64 ≤ input.size) :
    (updateBlock message input).size = 64 := by
  simp only [updateBlock, ByteArray.size_append, size_tailBytes, ByteArray.size_extract]
  omega

theorem size_updateRemainder (message input : ByteArray) :
    (updateRemainder message input).size = input.size - (64 - message.size % 64) := by
  simp only [updateRemainder, ByteArray.size_extract, Nat.min_self]

theorem absorbedBuffer_append_fill (message input : ByteArray)
    (h : 64 - message.size % 64 ≤ input.size) :
    absorbedBuffer (message ++ input) =
      Standards.RFC.MD5.processBlocks
        (Standards.RFC.MD5.processBlocks (absorbedBuffer message)
          (Standards.RFC.MD5.wordsOfBytes (updateBlock message input)))
        (Standards.RFC.MD5.wordsOfBytes (fullBytes (updateRemainder message input))) := by
  have haligned : (updateBlock message input).size % 64 = 0 := by
    rw [size_updateBlock _ _ h]
  rw [absorbedBuffer_append, ← updateBlock_append_updateRemainder _ _ h,
    fullBytes_append_aligned _ _ haligned,
    RFC1321.processBlocks_wordsOfBytes_append _ _ _ haligned]

theorem tailBytes_append_fill (message input : ByteArray)
    (h : 64 - message.size % 64 ≤ input.size) :
    tailBytes (message ++ input) = tailBytes (updateRemainder message input) := by
  have haligned : (updateBlock message input).size % 64 = 0 := by
    rw [size_updateBlock _ _ h]
  rw [tailBytes_append, ← updateBlock_append_updateRemainder _ _ h,
    tailBytes_append_aligned _ _ haligned]

theorem blockCount_append_short (message input : ByteArray)
    (h : message.size % 64 + input.size < 64) :
    (message ++ input).size / 64 = message.size / 64 := by
  rw [ByteArray.size_append]
  omega

theorem position_append_short (message input : ByteArray)
    (h : message.size % 64 + input.size < 64) :
    (message ++ input).size % 64 = message.size % 64 + input.size := by
  rw [ByteArray.size_append]
  omega

theorem blockCount_append_aligned (message input : ByteArray)
    (h : message.size % 64 = 0) :
    (message ++ input).size / 64 = message.size / 64 + input.size / 64 := by
  rw [ByteArray.size_append]
  omega

theorem position_append_aligned (message input : ByteArray)
    (h : message.size % 64 = 0) :
    (message ++ input).size % 64 = input.size % 64 := by
  rw [ByteArray.size_append]
  omega

theorem blockCount_append_fill (message input : ByteArray)
    (h : 64 - message.size % 64 ≤ input.size) :
    (message ++ input).size / 64 =
      message.size / 64 + 1 + (updateRemainder message input).size / 64 := by
  rw [ByteArray.size_append, size_updateRemainder]
  omega

theorem position_append_fill (message input : ByteArray)
    (h : 64 - message.size % 64 ≤ input.size) :
    (message ++ input).size % 64 = (updateRemainder message input).size % 64 := by
  rw [ByteArray.size_append, size_updateRemainder]
  omega

theorem tailBytes_extract_suffix (input : ByteArray) (offset : Nat)
    (hoff : offset ≤ input.size) :
    tailBytes (input.extract offset input.size) =
      input.extract (offset + (input.size - offset) / 64 * 64) input.size := by
  simp only [tailBytes, ByteArray.size_extract, Nat.min_self, ByteArray.extract_extract]
  congr 1
  omega

theorem size_tailBytes_extract_suffix (input : ByteArray) (offset : Nat) :
    (tailBytes (input.extract offset input.size)).size = (input.size - offset) % 64 := by
  rw [size_tailBytes]
  simp only [ByteArray.size_extract, Nat.min_self]

end Md5.Proofs.Buffered
