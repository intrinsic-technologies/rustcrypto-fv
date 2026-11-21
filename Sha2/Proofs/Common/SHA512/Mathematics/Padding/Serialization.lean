import Sha2.Proofs.Common.SHA512.Mathematics.Padding.Compression
import Sha2.Proofs.Common.Encoding.PointEncoding

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512
open Sha2.Proofs.NIST

open Sha2.Proofs.Common.Encoding (natToOctets_size)

theorem serializeHash_empty : serializeHash #[] = ByteArray.empty := rfl

theorem serializeHash_push (hash : Array UInt64) (word : UInt64) :
    serializeHash (hash.push word) = serializeHash hash ++ Encoding.natToOctets 8 word.toNat := by
  simp only [serializeHash, Array.foldl_push]

private theorem array_push_induction {α : Type} (P : Array α → Prop)
    (empty : P #[]) (push : ∀ xs x, P xs → P (xs.push x)) (xs : Array α) : P xs := by
  have reverse (items : List α) : P items.reverse.toArray := by
    induction items with
    | nil => exact empty
    | cons x items ih =>
        simpa [List.reverse_cons, Array.push, List.concat_eq_append] using
          push items.reverse.toArray x ih
  simpa using reverse xs.toList.reverse

theorem serializeHash_size (hash : Array UInt64) : (serializeHash hash).size = 8 * hash.size := by
  induction hash using array_push_induction with
  | empty => rfl
  | push hash word ih =>
      rw [serializeHash_push, ByteArray.size_append, natToOctets_size, ih, Array.size_push]
      omega

theorem serializeHash_getElem (hash : Array UInt64) (i : Nat)
    (hi : i < (serializeHash hash).size) :
    (serializeHash hash)[i] =
      UInt8.ofNat (hash[i / 8]!.toNat / 256 ^ (7 - i % 8) % 256) := by
  induction hash using array_push_induction generalizing i with
  | empty => simp only [serializeHash_size, Array.size_empty, Nat.mul_zero] at hi; omega
  | push hash word ih =>
      have hib : i < 8 * (hash.size + 1) := by
        simpa only [serializeHash_size, Array.size_push] using hi
      simp only [serializeHash_push] at hi ⊢
      by_cases hlt : i < 8 * hash.size
      · rw [ByteArray.getElem_append_left (by rwa [serializeHash_size])]
        rw [ih i (by rwa [serializeHash_size])]
        have hdiv : i / 8 < hash.size := by omega
        simp [hdiv, show i / 8 < hash.size + 1 by omega, Array.getElem_push_lt]
      · have ht : i - (serializeHash hash).size < 8 := by rw [serializeHash_size]; omega
        rw [ByteArray.getElem_append_right (by rw [serializeHash_size]; omega),
          ByteArray.getElem_eq_getElem_data,
          Sha2.Proofs.Common.Encoding.natToOctets_getElem 8 word.toNat _ ht, serializeHash_size]
        have hdiv : i / 8 = hash.size := by omega
        have hmod : i - 8 * hash.size = i % 8 := by omega
        simp [hdiv, hmod]

theorem serializeHash_getElem? (hash : Array UInt64) (i : Nat) :
    (serializeHash hash)[i]? =
      if i < 8 * hash.size then
        some (UInt8.ofNat (hash[i / 8]!.toNat / 256 ^ (7 - i % 8) % 256))
      else none := by
  by_cases hi : i < 8 * hash.size
  · simp only [hi, ↓reduceIte, getElem?_pos (serializeHash hash) i (by rwa [serializeHash_size]), serializeHash_getElem]
  · simp only [hi, ↓reduceIte, getElem?_neg (serializeHash hash) i (by rwa [serializeHash_size])]

end Sha2.Proofs.Common.SHA512
