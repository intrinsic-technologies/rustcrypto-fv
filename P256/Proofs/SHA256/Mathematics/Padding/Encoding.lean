import P256.Proofs.SHA256.Interface
import Standards.SECG.ECC.Encoding
import Init.Data.ByteArray.Lemmas
import Init.Data.Nat.Bitwise.Lemmas

set_option autoImplicit false

namespace P256.Proofs.SHA256

theorem wordToBits_ofNat (width value : Nat) :
    (Standards.NIST.SHA2.wordToBits (BitVec.ofNat width value)).toArray =
      (Array.range width).map (fun i => value.testBit (width - 1 - i)) := by
  apply Array.ext
  · simp
  · intro i hi hi'
    have hiw : i < width := by simpa only [Array.size_map, Array.size_range] using hi'
    simp [Standards.NIST.SHA2.wordToBits, BitVec.getMsbD, BitVec.getLsbD,
      Nat.testBit_mod_two_pow, show width - 1 - i < width by omega]

theorem bytesToBits_size (input : ByteArray) :
    (Standards.NIST.SHA2.bytesToBits input).size = 8 * input.size := by
  change (((⟨input.data, rfl⟩ : Vector UInt8 input.size).flatMap
    (fun x => Standards.NIST.SHA2.wordToBits x.toBitVec)).toArray).size = _
  rw [Vector.size_toArray, Nat.mul_comm]

theorem bytesToBits_getElem! (input : ByteArray) (i : Nat) (hi : i < 8 * input.size) :
    (Standards.NIST.SHA2.bytesToBits input)[i]! = input.data[i / 8]!.toNat.testBit (7 - i % 8) := by
  have hi' : i < input.size * 8 := by omega
  have hdiv : i / 8 < input.data.size := by change i / 8 < input.size; omega
  change (((⟨input.data, rfl⟩ : Vector UInt8 input.size).flatMap
    (fun x => Standards.NIST.SHA2.wordToBits x.toBitVec)).toArray)[i]! = _
  rw [getElem!_pos _ i (by simpa only [Vector.size_toArray] using hi'),
    Vector.getElem_toArray, Vector.getElem_flatMap, getElem!_pos input.data (i / 8) hdiv]
  simp [Standards.NIST.SHA2.wordToBits, BitVec.getMsbD, BitVec.getLsbD]

theorem bytesToBits_getElem (input : ByteArray) (i : Nat)
    (hi : i < (Standards.NIST.SHA2.bytesToBits input).size) :
    (Standards.NIST.SHA2.bytesToBits input)[i] = input.data[i / 8]!.toNat.testBit (7 - i % 8) := by
  rw [← getElem!_pos _ i hi]
  exact bytesToBits_getElem! input i (by rwa [bytesToBits_size] at hi)

theorem bytesToBits_append (a b : ByteArray) :
    Standards.NIST.SHA2.bytesToBits (a ++ b) = Standards.NIST.SHA2.bytesToBits a ++ Standards.NIST.SHA2.bytesToBits b := by
  apply Array.ext
  · simp only [bytesToBits_size, ByteArray.size_append, Array.size_append, Nat.mul_add]
  · intro i hi hi'
    rw [bytesToBits_getElem]
    have hiab : i < 8 * (a.size + b.size) := by
      simpa only [bytesToBits_size, ByteArray.size_append] using hi
    by_cases hia : i < 8 * a.size
    · rw [Array.getElem_append_left (by rwa [bytesToBits_size]), bytesToBits_getElem]
      have hdiv : i / 8 < a.size := by omega
      simp [ByteArray.data_append, hdiv, show i / 8 < a.size + b.size by omega]
    · rw [Array.getElem_append_right (by simpa only [bytesToBits_size] using Nat.le_of_not_gt hia),
        bytesToBits_getElem, bytesToBits_size]
      have hdiv : a.size ≤ i / 8 := by omega
      have hdiv' : i / 8 < a.size + b.size := by omega
      have hindex : (i - 8 * a.size) / 8 = i / 8 - a.size := by omega
      have hmod : (i - 8 * a.size) % 8 = i % 8 := by omega
      simp [ByteArray.data_append, hdiv, hdiv', hindex, hmod, show i / 8 - a.size < b.size by omega]

theorem bytesToBits_extract (input : ByteArray) (start stop : Nat) :
    Standards.NIST.SHA2.bytesToBits (input.extract start stop) =
      (Standards.NIST.SHA2.bytesToBits input).extract (8 * start) (8 * stop) := by
  apply Array.ext
  · simp only [bytesToBits_size, ByteArray.size_extract, Array.size_extract]
    omega
  · intro i hi hi'
    rw [bytesToBits_getElem, Array.getElem_extract, bytesToBits_getElem]
    have his : i < 8 * (min stop input.size - start) := by
      simpa only [bytesToBits_size, ByteArray.size_extract] using hi
    have hdiv : i / 8 < min stop input.size - start := by omega
    have hindex : (8 * start + i) / 8 = start + i / 8 := by omega
    have hmod : (8 * start + i) % 8 = i % 8 := by omega
    simp [ByteArray.data_extract, hdiv, hindex, hmod,
      show start + i / 8 < input.size by omega]

theorem bytesToBits_replicate_zero (n : Nat) :
    Standards.NIST.SHA2.bytesToBits ⟨Array.replicate n 0⟩ = Array.replicate (8 * n) false := by
  apply Array.ext
  · simp [bytesToBits_size, ByteArray.size]
  · intro i hi hi'
    rw [bytesToBits_getElem]
    have hdiv : i / 8 < n := by
      simp only [bytesToBits_size, ByteArray.size, Array.size_replicate] at hi
      omega
    simp [hdiv]

theorem bytesToBits_paddingMarker :
    Standards.NIST.SHA2.bytesToBits ⟨#[128]⟩ = #[true] ++ Array.replicate 7 false := by
  decide +kernel

theorem bytesToBits_natToOctets (length value : Nat) :
    Standards.NIST.SHA2.bytesToBits (Standards.SECG.ECC.Encoding.natToOctets length value) =
      (Array.range (8 * length)).map (fun i => value.testBit (8 * length - 1 - i)) := by
  apply Array.ext
  · simp [bytesToBits_size, Standards.SECG.ECC.Encoding.natToOctets, ByteArray.size]
  · intro i hi hi'
    rw [bytesToBits_getElem]
    have hil : i < 8 * length := by
      simpa only [Array.size_map, Array.size_range] using hi'
    have hdiv : i / 8 < length := by omega
    have helem : (Standards.SECG.ECC.Encoding.natToOctets length value).data[i / 8]! =
        UInt8.ofNat (value / 256 ^ (length - 1 - i / 8) % 256) := by
      simp [Standards.SECG.ECC.Encoding.natToOctets, hdiv]
    rw [helem]
    simp only [Array.getElem_map, Array.getElem_range, UInt8.toNat_ofNat', Nat.mod_mod]
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul,
      Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    rw [decide_eq_true (show 7 - i % 8 < 8 by omega), Bool.true_and]
    congr 1
    omega

end P256.Proofs.SHA256
