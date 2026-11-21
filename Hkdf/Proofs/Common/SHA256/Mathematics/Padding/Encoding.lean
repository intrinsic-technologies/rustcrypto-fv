import Hkdf.Proofs.NIST.SHA256
import Init.Data.ByteArray.Lemmas
import Init.Data.Nat.Bitwise.Lemmas

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256
open Hkdf.Proofs.NIST

theorem octetsToBits_size (input : ByteArray) :
    (Encoding.octetsToBits input).size = 8 * input.size := by
  simp only [Encoding.octetsToBits, Array.size_map, Array.size_range]

theorem octetsToBits_getElem! (input : ByteArray) (i : Nat) (hi : i < 8 * input.size) :
    (Encoding.octetsToBits input)[i]! = input.data[i / 8]!.toNat.testBit (7 - i % 8) := by
  simp [Encoding.octetsToBits, hi]

theorem octetsToBits_getElem (input : ByteArray) (i : Nat)
    (hi : i < (Encoding.octetsToBits input).size) :
    (Encoding.octetsToBits input)[i] = input.data[i / 8]!.toNat.testBit (7 - i % 8) := by
  rw [← getElem!_pos _ i hi]
  exact octetsToBits_getElem! input i (by rwa [octetsToBits_size] at hi)

theorem octetsToBits_append (a b : ByteArray) :
    Encoding.octetsToBits (a ++ b) = Encoding.octetsToBits a ++ Encoding.octetsToBits b := by
  apply Array.ext
  · simp only [octetsToBits_size, ByteArray.size_append, Array.size_append, Nat.mul_add]
  · intro i hi hi'
    rw [octetsToBits_getElem]
    have hiab : i < 8 * (a.size + b.size) := by
      simpa only [octetsToBits_size, ByteArray.size_append] using hi
    by_cases hia : i < 8 * a.size
    · rw [Array.getElem_append_left (by rwa [octetsToBits_size]), octetsToBits_getElem]
      have hdiv : i / 8 < a.size := by omega
      simp [ByteArray.data_append, hdiv, show i / 8 < a.size + b.size by omega]
    · rw [Array.getElem_append_right (by simpa only [octetsToBits_size] using Nat.le_of_not_gt hia),
        octetsToBits_getElem, octetsToBits_size]
      have hdiv : a.size ≤ i / 8 := by omega
      have hdiv' : i / 8 < a.size + b.size := by omega
      have hindex : (i - 8 * a.size) / 8 = i / 8 - a.size := by omega
      have hmod : (i - 8 * a.size) % 8 = i % 8 := by omega
      simp [ByteArray.data_append, hdiv, hdiv', hindex, hmod, show i / 8 - a.size < b.size by omega]

theorem octetsToBits_extract (input : ByteArray) (start stop : Nat) :
    Encoding.octetsToBits (input.extract start stop) =
      (Encoding.octetsToBits input).extract (8 * start) (8 * stop) := by
  apply Array.ext
  · simp only [octetsToBits_size, ByteArray.size_extract, Array.size_extract]
    omega
  · intro i hi hi'
    rw [octetsToBits_getElem, Array.getElem_extract, octetsToBits_getElem]
    have his : i < 8 * (min stop input.size - start) := by
      simpa only [octetsToBits_size, ByteArray.size_extract] using hi
    have hdiv : i / 8 < min stop input.size - start := by omega
    have hindex : (8 * start + i) / 8 = start + i / 8 := by omega
    have hmod : (8 * start + i) % 8 = i % 8 := by omega
    simp [ByteArray.data_extract, hdiv, hindex, hmod,
      show start + i / 8 < input.size by omega]

theorem octetsToBits_replicate_zero (n : Nat) :
    Encoding.octetsToBits ⟨Array.replicate n 0⟩ = Array.replicate (8 * n) false := by
  apply Array.ext
  · simp [octetsToBits_size, ByteArray.size]
  · intro i hi hi'
    rw [octetsToBits_getElem]
    have hdiv : i / 8 < n := by
      simp only [octetsToBits_size, ByteArray.size, Array.size_replicate] at hi
      omega
    simp [hdiv]

theorem octetsToBits_paddingMarker :
    Encoding.octetsToBits ⟨#[128]⟩ = #[true] ++ Array.replicate 7 false := by
  decide +kernel

theorem octetsToBits_natToOctets (length value : Nat) :
    Encoding.octetsToBits (Encoding.natToOctets length value) =
      (Array.range (8 * length)).map (fun i => value.testBit (8 * length - 1 - i)) := by
  apply Array.ext
  · simp [octetsToBits_size, Encoding.natToOctets, ByteArray.size]
  · intro i hi hi'
    rw [octetsToBits_getElem]
    have hil : i < 8 * length := by
      simpa only [Array.size_map, Array.size_range] using hi'
    have hdiv : i / 8 < length := by omega
    have helem : (Encoding.natToOctets length value).data[i / 8]! =
        UInt8.ofNat (value / 256 ^ (length - 1 - i / 8) % 256) := by
      simp [Encoding.natToOctets, hdiv]
    rw [helem]
    simp only [Array.getElem_map, Array.getElem_range, UInt8.toNat_ofNat', Nat.mod_mod]
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul,
      Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    rw [decide_eq_true (show 7 - i % 8 < 8 by omega), Bool.true_and]
    congr 1
    omega

end Hkdf.Proofs.Common.SHA256
