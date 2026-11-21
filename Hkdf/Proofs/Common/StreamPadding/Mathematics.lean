import Hkdf.Proofs.Common.SHA256.Mathematics.Padding.Tail
import Hkdf.Proofs.Common.Instructions.Bswap
import Hkdf.Proofs.Common.Encoding.PointEncoding
import Hkdf.Spec.Program
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.SHA256 Hkdf.Proofs.Common.Instructions Hkdf.Proofs.NIST

def paddedBuffer (message : ByteArray) : ByteArray :=
  remainderBytes message ++ ⟨#[128]⟩ ++ ⟨Array.replicate (63 - message.size % 64) 0⟩

def finalPrefix (message : ByteArray) : ByteArray :=
  if message.size % 64 < 56 then
    remainderBytes message ++ ⟨#[128]⟩ ++ ⟨Array.replicate (55 - message.size % 64) 0⟩
  else ⟨Array.replicate 56 0⟩

def finalBlock (message : ByteArray) : ByteArray :=
  finalPrefix message ++ NIST.Encoding.natToOctets 8 (8 * message.size)

theorem paddedBuffer_prefix (message : ByteArray) (small : message.size % 64 < 56) :
    (paddedBuffer message).extract 0 56 = finalPrefix message := by
  have count : 63 - message.size % 64 = (55 - message.size % 64) + 8 := by omega
  have split : (⟨Array.replicate (63 - message.size % 64) 0⟩ : ByteArray) =
      ⟨Array.replicate (55 - message.size % 64) 0⟩ ++ ⟨Array.replicate 8 0⟩ := by
    apply ByteArray.ext
    simp only [ByteArray.data_append, Array.replicate_append_replicate, count]
  have size : (finalPrefix message).size = 56 := by
    simp only [finalPrefix, small, ite_true, ByteArray.size_append, remainderBytes_size]
    simp only [ByteArray.size, Array.size_replicate]
    change message.size % 64 + 1 + (55 - message.size % 64) = 56
    omega
  have padded : paddedBuffer message = finalPrefix message ++ ⟨Array.replicate 8 0⟩ := by
    simp only [paddedBuffer, finalPrefix, small, ite_true, split, ByteArray.append_assoc]
  rw [padded]
  exact ByteArray.extract_append_eq_left size.symm

theorem paddedBuffer_size (message : ByteArray) : (paddedBuffer message).size = 64 := by
  simp only [paddedBuffer, ByteArray.size_append, remainderBytes_size]
  simp only [ByteArray.size, Array.size_replicate]
  change message.size % 64 + 1 + (63 - message.size % 64) = 64
  omega

theorem padded_bytes {s : RamState} {message : ByteArray} {base : BitVec 64}
    (tail : (⟨base.toNat, message.size % 64⟩ : MemoryRegion).HasBytes
      s.external (remainderBytes message))
    (marker : s.external[base + BitVec.ofNat 64 (message.size % 64)]? = some 128)
    (zero : ∀ i < 63 - message.size % 64,
      s.external[base + BitVec.ofNat 64 (message.size % 64 + 1 + i)]? = some 0) :
    (⟨base.toNat, 64⟩ : MemoryRegion).HasBytes s.external (paddedBuffer message) := by
  refine ⟨paddedBuffer_size message, ?_⟩
  intro i
  have hi : i.val < 64 := by simpa only [paddedBuffer_size] using i.isLt
  have remSize := remainderBytes_size message
  change s.external[BitVec.ofNat 64 (base.toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  by_cases before : i.val < message.size % 64
  · have byte := tail.2 ⟨i.val, by omega⟩
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
    rw [byte]
    apply congrArg some
    simp only [paddedBuffer]
    rw [ByteArray.getElem_append_left (by simp only [ByteArray.size_append, remSize]; change _ < message.size % 64 + 1; omega),
      ByteArray.getElem_append_left (by omega)]
  · by_cases eq : i.val = message.size % 64
    · rw [show s.external[base + BitVec.ofNat 64 i.val]? = some 128 by simpa only [eq] using marker]
      apply congrArg some
      simp only [paddedBuffer]
      rw [ByteArray.getElem_append_left (by simp only [ByteArray.size_append, remSize]; change _ < message.size % 64 + 1; omega),
        ByteArray.getElem_append_right (by omega)]
      simp only [eq, remSize, Nat.sub_self]
      rfl
    · have after : message.size % 64 + 1 ≤ i.val := by omega
      have byte := zero (i.val - (message.size % 64 + 1)) (by omega)
      rw [Nat.add_sub_of_le after] at byte
      rw [byte]
      apply congrArg some
      simp only [paddedBuffer]
      rw [ByteArray.getElem_append_right (by simp only [ByteArray.size_append, remSize]; change message.size % 64 + 1 ≤ _; omega)]
      simp [ByteArray.getElem_eq_getElem_data]

theorem tail_zero_count (tail : Nat) (bound : tail < 64) :
    BitVec.ofNat 64 tail ^^^ 63 = BitVec.ofNat 64 (63 - tail) := by
  have computed : ∀ tail : Fin 64,
      BitVec.ofNat 64 tail.val ^^^ 63 = BitVec.ofNat 64 (63 - tail.val) := by
    decide +kernel
  exact computed ⟨tail, bound⟩

theorem tail_shift_or_blocks (n : Nat) :
    (((BitVec.ofNat 32 (n % 64)) <<< 3).setWidth 64 |||
      ((BitVec.ofNat 64 (n / 64)) <<< 9)) = BitVec.ofNat 64 (8 * n) := by
  have remBound : n % 64 < 64 := Nat.mod_lt _ (by decide)
  have low : ((BitVec.ofNat 32 (n % 64)) <<< 3).setWidth 64 =
      BitVec.ofNat 64 (8 * (n % 64)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.reducePow]
    omega
  rw [low]
  have high : ((BitVec.ofNat 64 (n / 64)) <<< 9) =
      BitVec.ofNat 64 (512 * (n / 64)) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    simp only [BitVec.twoPow, BitVec.ofNat_mul, Nat.mul_comm]
    rfl
  rw [high, ← BitVec.ofNat_or]
  have join := Nat.two_pow_add_eq_or_of_lt (i := 9) (b := 8 * (n % 64)) (by omega) (n / 64)
  rw [Nat.or_comm, ← join]
  congr 1
  omega

theorem bswap64_ofNat_storedByte (value : Nat) {i : Nat} (hi : i < 8) :
    storedByte (bswap64 (BitVec.ofNat 64 value)) i =
      (NIST.Encoding.natToOctets 8 value)[i]'(by
        simpa only [Common.Encoding.natToOctets_size] using hi) := by
  rw [storedByte_eq_extract, bswap64_byte _ _ hi, ← storedByte_eq_extract,
    ByteArray.getElem_eq_getElem_data, Common.Encoding.natToOctets_getElem 8 value i hi]
  apply UInt8.toNat.inj
  simp only [storedByte, UInt8.toNat_ofNat', BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_mod]
  have split : 2^64 = 2^(8*(7-i)) * 2^(64-8*(7-i)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [split, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _
    (Nat.pow_dvd_pow 2 (show 8 ≤ 64-8*(7-i) by omega))]
  rw [show 256^(7-i) = 2^(8*(7-i)) by rw [Nat.pow_mul]]

end Hkdf.Proofs.Common.StreamPadding
