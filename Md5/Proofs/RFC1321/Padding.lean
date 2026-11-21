import Standards.RFC.MD5
import Md5.Proofs.RFC1321.Processing
import Init.Data.Array.Lemmas
import Init.Data.Array.Extract
import Init.Data.Vector.Lemmas
import Init.Data.ByteArray.Lemmas

namespace Md5.Proofs.RFC1321

open Standards.RFC.MD5

theorem size_bitsOfBytes (bytes : ByteArray) : (bitsOfBytes bytes).size = bytes.size * 8 := by
  simp only [bitsOfBytes, Array.size_flatMap, Array.size_ofFn, Array.map_const',
    Array.sum_replicate_nat, ByteArray.size_data]

theorem size_bytesOfBits (bits : Array Bool) : (bytesOfBits bits).size = bits.size / 8 := by
  simp only [bytesOfBits, ByteArray.size, Array.size_ofFn]

theorem bitsOfBytes_append (a b : ByteArray) :
    bitsOfBytes (a ++ b) = bitsOfBytes a ++ bitsOfBytes b := by
  simp [bitsOfBytes, ByteArray.data_append, Array.flatMap_append]

theorem getElem_bitsOfBytes (bytes : ByteArray) (i : Nat)
    (hi : i < (bitsOfBytes bytes).size) :
    (bitsOfBytes bytes)[i] =
      (bytes[i / 8]'(by rw [size_bitsOfBytes] at hi; omega)).toNat.testBit (7 - i % 8) := by
  have hi' : i < bytes.size * 8 := by simpa only [size_bitsOfBytes] using hi
  change ((Vector.mk bytes.data rfl).flatMap
    (fun byte ↦ Vector.ofFn (fun j : Fin 8 ↦ byte.toNat.testBit (7 - j.val))))[i] = _
  rw [Vector.getElem_flatMap hi', Vector.getElem_ofFn]
  rfl

theorem extract_bitsOfBytes_byte (bytes : ByteArray) (i : Nat) (hi : i < bytes.size) :
    (bitsOfBytes bytes).extract (8 * i) (8 * i + 8) =
      Array.ofFn (fun j : Fin 8 ↦ bytes[i].toNat.testBit (7 - j.val)) := by
  apply Array.ext
  · simp only [Array.size_extract, size_bitsOfBytes, Array.size_ofFn]
    omega
  · intro j hj hj'
    simp only [Array.getElem_extract, Array.getElem_ofFn, getElem_bitsOfBytes]
    have hj8 : j < 8 := by simpa only [Array.size_ofFn] using hj'
    simp only [show (8 * i + j) / 8 = i by omega, show (8 * i + j) % 8 = j by omega]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem foldl_bitsOfByte : ∀ byte : UInt8,
    (Array.ofFn (fun i : Fin 8 ↦ byte.toNat.testBit (7 - i.val))).foldl
      (fun acc bit ↦ 2 * acc + if bit then 1 else 0) (0 : UInt8) = byte := by
  have h : ∀ b : Fin 256,
      (Array.ofFn (fun i : Fin 8 ↦ (UInt8.ofNat b.val).toNat.testBit (7 - i.val))).foldl
        (fun acc bit ↦ 2 * acc + if bit then 1 else 0) (0 : UInt8) = UInt8.ofNat b.val := by
    decide +kernel
  intro byte
  simpa using h ⟨byte.toNat, byte.toNat_lt⟩

theorem bytesOfBits_bitsOfBytes (bytes : ByteArray) : bytesOfBits (bitsOfBytes bytes) = bytes := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [bytesOfBits, Array.size_ofFn, size_bitsOfBytes, ByteArray.size_data]
    omega
  · intro i hi hi'
    simp only [bytesOfBits, Array.getElem_ofFn]
    rw [extract_bitsOfBytes_byte bytes i hi', foldl_bitsOfByte]
    rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem foldl_getBit_of_size_eight (bits : Array Bool) (hs : bits.size = 8)
    (i : Nat) (hi : i < 8) :
    (bits.foldl (fun acc bit ↦ 2 * acc + if bit then 1 else 0) (0 : UInt8)).toNat.testBit
      (7 - i) = bits[i]'(by omega) := by
  have h : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, ∀ j : Fin 8,
      (#[b0, b1, b2, b3, b4, b5, b6, b7].foldl
        (fun acc bit ↦ 2 * acc + if bit then 1 else 0) (0 : UInt8)).toNat.testBit (7 - j.val) =
      #[b0, b1, b2, b3, b4, b5, b6, b7][j.val] := by
    decide +kernel
  have heq : bits = #[bits[0], bits[1], bits[2], bits[3], bits[4], bits[5], bits[6], bits[7]] := by
    apply Array.ext
    · exact hs
    · intro j hj hj'
      have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  conv => lhs; rw [heq]
  rw [h _ _ _ _ _ _ _ _ ⟨i, hi⟩]
  simp only [← heq]

theorem bitsOfBytes_bytesOfBits (bits : Array Bool) (hs : bits.size % 8 = 0) :
    bitsOfBytes (bytesOfBits bits) = bits := by
  apply Array.ext
  · rw [size_bitsOfBytes, size_bytesOfBits]
    omega
  · intro i hi hi'
    rw [getElem_bitsOfBytes]
    simp only [bytesOfBits, ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn]
    rw [foldl_getBit_of_size_eight _ (by simp only [Array.size_extract]; omega)
      (i % 8) (by omega), Array.getElem_extract]
    congr 1
    omega

def paddingZeroBytes (n : Nat) : Nat := ((55 - (n : Int)) % 64).toNat

def paddingBytes (n : Nat) : ByteArray := ⟨#[128] ++ Array.replicate (paddingZeroBytes n) 0⟩

def lengthBytes (n : Nat) : ByteArray :=
  ⟨(bytesOfWord (BitVec.ofNat 32 (n * 8 % 2 ^ 64)) ++
    bytesOfWord (BitVec.ofNat 32 ((n * 8 % 2 ^ 64) / 2 ^ 32))).toArray⟩

def paddedBytes (input : ByteArray) : ByteArray :=
  input ++ paddingBytes input.size ++ lengthBytes input.size

theorem paddingZeroBytes_lt (n : Nat) : paddingZeroBytes n < 64 := by
  unfold paddingZeroBytes
  omega

theorem paddingZeroBytes_mod (n : Nat) : (n + 1 + paddingZeroBytes n) % 64 = 56 := by
  unfold paddingZeroBytes
  omega

theorem paddingZeroBytes_eq (n : Nat) :
    paddingZeroBytes n = if n % 64 < 56 then 55 - n % 64 else 119 - n % 64 := by
  unfold paddingZeroBytes
  split <;> omega

theorem paddingZeroBytes_bits (n : Nat) :
    ((447 - (n * 8 : Nat) : Int) % 512).toNat = 7 + paddingZeroBytes n * 8 := by
  unfold paddingZeroBytes
  omega

theorem bitsOfByte_zero :
    Array.ofFn (fun i : Fin 8 ↦ (0 : UInt8).toNat.testBit (7 - i.val)) =
      Array.replicate 8 false := by
  decide +kernel

theorem bitsOfByte_padding :
    Array.ofFn (fun i : Fin 8 ↦ (128 : UInt8).toNat.testBit (7 - i.val)) =
      #[true] ++ Array.replicate 7 false := by
  decide +kernel

theorem bitsOfBytes_paddingBytes (n : Nat) :
    bitsOfBytes (paddingBytes n) = #[true] ++ Array.replicate (7 + paddingZeroBytes n * 8) false := by
  simp only [paddingBytes, bitsOfBytes, Array.flatMap_append, Array.flatMap_singleton,
    Array.flatMap_replicate, bitsOfByte_padding, bitsOfByte_zero,
    Array.flatten_replicate_replicate, Array.append_assoc, Array.replicate_append_replicate]

theorem appendPaddingBits_bitsOfBytes (input : ByteArray) :
    appendPaddingBits (bitsOfBytes input) = bitsOfBytes (input ++ paddingBytes input.size) := by
  simp only [appendPaddingBits, size_bitsOfBytes, paddingZeroBytes_bits, bitsOfBytes_append,
    bitsOfBytes_paddingBytes, Array.push_eq_append, Array.append_assoc]

theorem appendLength_bitsOfBytes (n : Nat) (input : ByteArray) :
    appendLength (n * 8) (bitsOfBytes input) = bitsOfBytes (input ++ lengthBytes n) := by
  simp only [appendLength, lengthBytes, bitsOfBytes_append]

theorem paddedBytes_bitsOfBytes (input : ByteArray) :
    appendLength (bitsOfBytes input).size (appendPaddingBits (bitsOfBytes input)) =
      bitsOfBytes (paddedBytes input) := by
  rw [size_bitsOfBytes, appendPaddingBits_bitsOfBytes, appendLength_bitsOfBytes]
  rfl

theorem messageDigest_bitsOfBytes (input : ByteArray) :
    messageDigest (bitsOfBytes input) =
      (processBlocks Buffer.initial (wordsOfBytes (paddedBytes input))).toBytes := by
  simp only [messageDigest, paddedBytes_bitsOfBytes, bytesOfBits_bitsOfBytes]

theorem size_paddingBytes (n : Nat) : (paddingBytes n).size = 1 + paddingZeroBytes n := by
  simp only [paddingBytes, ByteArray.size, Array.size_append, Array.size_singleton,
    Array.size_replicate]

theorem size_lengthBytes (n : Nat) : (lengthBytes n).size = 8 := by
  simp only [lengthBytes, ByteArray.size, Vector.size_toArray]

theorem getElem_lengthBytes (n i : Nat) (hi : i < 8) :
    (lengthBytes n)[i]'(by rw [size_lengthBytes]; exact hi) =
      ((n * 8 % 2 ^ 64) / 2 ^ (8 * i)).toUInt8 := by
  change (bytesOfWord (BitVec.ofNat 32 (n * 8 % 2 ^ 64)) ++
    bytesOfWord (BitVec.ofNat 32 ((n * 8 % 2 ^ 64) / 2 ^ 32)))[i] = _
  rw [Vector.getElem_append]
  have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hiCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [bytesOfWord, Vector.getElem_ofFn, BitVec.toNat_ushiftRight,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reduceMul, Nat.reducePow,
      Nat.reduceLT, Nat.reduceSub, ↓reduceDIte] <;>
    apply UInt8.toNat_inj.mp <;>
    simp only [UInt8.toNat_ofNat', Nat.reducePow, Nat.toUInt8] <;> omega

theorem size_paddedBytes (input : ByteArray) :
    (paddedBytes input).size = input.size + 1 + paddingZeroBytes input.size + 8 := by
  simp only [paddedBytes, ByteArray.size_append, size_paddingBytes, size_lengthBytes]
  omega

theorem size_paddedBytes_mod (input : ByteArray) : (paddedBytes input).size % 64 = 0 := by
  rw [size_paddedBytes]
  have := paddingZeroBytes_mod input.size
  omega

theorem size_paddedBytes_div (input : ByteArray) :
    (paddedBytes input).size / 64 = input.size / 64 +
      if input.size % 64 < 56 then 1 else 2 := by
  rw [size_paddedBytes, paddingZeroBytes_eq]
  split <;> omega

theorem getElem_paddingBytes_zero (n : Nat) :
    (paddingBytes n)[0]'(by rw [size_paddingBytes]; omega) = 128 := by
  simp [paddingBytes, ByteArray.getElem_eq_getElem_data]

theorem getElem_paddingBytes_succ (n i : Nat) (hi : i < paddingZeroBytes n) :
    (paddingBytes n)[i + 1]'(by rw [size_paddingBytes]; omega) = 0 := by
  simp [paddingBytes, ByteArray.getElem_eq_getElem_data]

theorem paddingZeroBytes_add_aligned (a b : Nat) (ha : a % 64 = 0) :
    paddingZeroBytes (a + b) = paddingZeroBytes b := by
  unfold paddingZeroBytes
  omega

theorem paddedBytes_append (pre tail : ByteArray) :
    paddedBytes (pre ++ tail) = pre ++
      (tail ++ paddingBytes (pre.size + tail.size) ++ lengthBytes (pre.size + tail.size)) := by
  simp only [paddedBytes, ByteArray.size_append, ByteArray.append_assoc]

def paddedTail (input : ByteArray) : ByteArray :=
  input.extract (input.size / 64 * 64) input.size ++
    paddingBytes input.size ++ lengthBytes input.size

theorem paddedBytes_eq_prefix_append_paddedTail (input : ByteArray) :
    paddedBytes input = input.extract 0 (input.size / 64 * 64) ++ paddedTail input := by
  unfold paddedBytes paddedTail
  rw [← ByteArray.append_assoc, ← ByteArray.append_assoc,
    ByteArray.extract_append_extract]
  simp only [Nat.zero_min, Nat.max_eq_right (by omega : input.size / 64 * 64 ≤ input.size),
    ByteArray.extract_zero_size]

theorem size_paddedTail (input : ByteArray) :
    (paddedTail input).size = if input.size % 64 < 56 then 64 else 128 := by
  simp only [paddedTail, ByteArray.size_append, ByteArray.size_extract,
    Nat.min_self, size_paddingBytes, size_lengthBytes, paddingZeroBytes_eq]
  split <;> omega

theorem getElem_paddedBytes_input (input : ByteArray) (i : Nat) (hi : i < input.size) :
    (paddedBytes input)[i]'(by rw [size_paddedBytes]; omega) = input[i] := by
  unfold paddedBytes
  rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append]; omega),
    ByteArray.getElem_append_left hi]

theorem getElem_paddedBytes_padding (input : ByteArray) :
    (paddedBytes input)[input.size]'(by rw [size_paddedBytes]; omega) = 128 := by
  unfold paddedBytes
  rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append, size_paddingBytes]; omega),
    ByteArray.getElem_append_right (by omega)]
  simpa only [Nat.sub_self] using getElem_paddingBytes_zero input.size

theorem getElem_paddedBytes_zero (input : ByteArray) (i : Nat)
    (hi : i < paddingZeroBytes input.size) :
    (paddedBytes input)[input.size + 1 + i]'(by rw [size_paddedBytes]; omega) = 0 := by
  unfold paddedBytes
  rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append, size_paddingBytes]; omega),
    ByteArray.getElem_append_right (by omega)]
  simpa only [show input.size + 1 + i - input.size = i + 1 by omega] using
    getElem_paddingBytes_succ input.size i hi

theorem getElem_paddedBytes_length (input : ByteArray) (i : Nat) (hi : i < 8) :
    (paddedBytes input)[input.size + 1 + paddingZeroBytes input.size + i]'
        (by rw [size_paddedBytes]; omega) =
      ((input.size * 8 % 2 ^ 64) / 2 ^ (8 * i)).toUInt8 := by
  unfold paddedBytes
  rw [ByteArray.getElem_append_right
    (by rw [ByteArray.size_append, size_paddingBytes]; omega)]
  have h : input.size + 1 + paddingZeroBytes input.size + i -
      (input ++ paddingBytes input.size).size = i := by
    rw [ByteArray.size_append, size_paddingBytes]
    omega
  simp only [h, getElem_lengthBytes input.size i hi]

theorem paddedBytes_append_aligned (a b : ByteArray) (ha : a.size % 64 = 0) :
    paddedBytes (a ++ b) = a ++
      (b ++ paddingBytes b.size ++ lengthBytes (a.size + b.size)) := by
  rw [paddedBytes_append]
  simp only [paddingBytes, paddingZeroBytes_add_aligned a.size b.size ha]

theorem messageDigest_bitsOfBytes_append (a b : ByteArray) (ha : a.size % 64 = 0) :
    messageDigest (bitsOfBytes (a ++ b)) =
      (processBlocks (processBlocks Buffer.initial (wordsOfBytes a))
        (wordsOfBytes (b ++ paddingBytes b.size ++ lengthBytes (a.size + b.size)))).toBytes := by
  rw [messageDigest_bitsOfBytes, paddedBytes_append_aligned a b ha,
    processBlocks_wordsOfBytes_append Buffer.initial a _ ha]

theorem bitLength_eq_blocks_remainder (n : Nat) :
    n * 8 = n / 64 * 512 + n % 64 * 8 := by
  omega

theorem messageDigest_bitsOfBytes_completeBlocks (input : ByteArray) :
    messageDigest (bitsOfBytes input) =
      (processBlocks
        (processBlocks Buffer.initial (wordsOfBytes (input.extract 0 (input.size / 64 * 64))))
        (wordsOfBytes (paddedTail input))).toBytes := by
  rw [messageDigest_bitsOfBytes, paddedBytes_eq_prefix_append_paddedTail,
    processBlocks_wordsOfBytes_append]
  simp only [ByteArray.size_extract]
  omega

end Md5.Proofs.RFC1321
