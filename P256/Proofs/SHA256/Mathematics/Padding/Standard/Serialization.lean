import P256.Proofs.SHA256.Interface
import Standards.SECG.ECC.Encoding
import Init.Data.ByteArray.Lemmas

set_option autoImplicit false

namespace P256.Proofs.SHA256

def serializeHash (hash : Array UInt32) : ByteArray :=
  hash.foldl (fun output word => output ++ Standards.SECG.ECC.Encoding.natToOctets 4 word.toNat) ByteArray.empty

theorem serializeHash_push (hash : Array UInt32) (word : UInt32) :
    serializeHash (hash.push word) = serializeHash hash ++ Standards.SECG.ECC.Encoding.natToOctets 4 word.toNat := by
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

theorem serializeHash_size (hash : Array UInt32) : (serializeHash hash).size = 4 * hash.size := by
  induction hash using array_push_induction with
  | empty => rfl
  | push hash word ih =>
      rw [serializeHash_push, ByteArray.size_append, show (Standards.SECG.ECC.Encoding.natToOctets 4 word.toNat).size = 4 by
        simp [Standards.SECG.ECC.Encoding.natToOctets, ByteArray.size], ih, Array.size_push]
      omega

theorem serializeHash_getElem (hash : Array UInt32) (i : Nat)
    (hi : i < (serializeHash hash).size) :
    (serializeHash hash)[i] =
      UInt8.ofNat (hash[i / 4]!.toNat / 256 ^ (3 - i % 4) % 256) := by
  induction hash using array_push_induction generalizing i with
  | empty => simp only [serializeHash_size, Array.size_empty, Nat.mul_zero] at hi; omega
  | push hash word ih =>
      have hib : i < 4 * (hash.size + 1) := by
        simpa only [serializeHash_size, Array.size_push] using hi
      simp only [serializeHash_push] at hi ⊢
      by_cases hlt : i < 4 * hash.size
      · rw [ByteArray.getElem_append_left (by rwa [serializeHash_size])]
        rw [ih i (by rwa [serializeHash_size])]
        have hdiv : i / 4 < hash.size := by omega
        simp [hdiv, show i / 4 < hash.size + 1 by omega, Array.getElem_push_lt]
      · have ht : i - (serializeHash hash).size < 4 := by rw [serializeHash_size]; omega
        rw [ByteArray.getElem_append_right (by rw [serializeHash_size]; omega),
          ByteArray.getElem_eq_getElem_data,
          show (Standards.SECG.ECC.Encoding.natToOctets 4 word.toNat).data[i - (serializeHash hash).size]'(by simpa [Standards.SECG.ECC.Encoding.natToOctets] using ht) =
            UInt8.ofNat (word.toNat / 256 ^ (3 - (i - (serializeHash hash).size)) % 256) by
          simp [Standards.SECG.ECC.Encoding.natToOctets], serializeHash_size]
        have hdiv : i / 4 = hash.size := by omega
        have hmod : i - 4 * hash.size = i % 4 := by omega
        simp [hdiv, hmod]

end P256.Proofs.SHA256
