import Base16ct.Spec

set_option autoImplicit false

namespace Base16ct.Proofs.Base16ctUpperEncodeCorrect

open Standards.RFC.BaseEncodings
open Base16ct.Spec.Program

def encodeByte (b : UInt8) : List UInt8 :=
  [Alphabet.base16Upper.character (b.toNat / 16),
   Alphabet.base16Upper.character (b.toNat % 16)]

def encodedBytes (input : List UInt8) : List UInt8 :=
  input.flatMap encodeByte

theorem encodedBytes_nil : encodedBytes [] = [] := rfl

theorem encodedBytes_cons (b : UInt8) (input : List UInt8) :
    encodedBytes (b :: input) = encodeByte b ++ encodedBytes input := by
  simp only [encodedBytes, List.flatMap_cons]

theorem encodedBytes_append (left right : List UInt8) :
    encodedBytes (left ++ right) = encodedBytes left ++ encodedBytes right := by
  simp only [encodedBytes, List.flatMap_append]

theorem encodeByte_length (b : UInt8) : (encodeByte b).length = 2 := rfl

theorem encodedBytes_length (input : List UInt8) :
    (encodedBytes input).length = 2 * input.length := by
  induction input with
  | nil => rfl
  | cons b input ih =>
    simp only [encodedBytes_cons, List.length_append, encodeByte_length, ih, List.length_cons]
    omega

theorem ofBits_high (b : UInt8) :
    ofBits 4 (fun j => b.toNat.testBit (7 - j)) = b.toNat / 16 := by
  have h : ∀ n : Fin 256, ofBits 4 (fun j => n.val.testBit (7 - j)) = n.val / 16 := by
    decide +kernel
  exact h ⟨b.toNat, b.toNat_lt⟩

theorem ofBits_low (b : UInt8) :
    ofBits 4 (fun j => b.toNat.testBit (3 - j)) = b.toNat % 16 := by
  have h : ∀ n : Fin 256, ofBits 4 (fun j => n.val.testBit (3 - j)) = n.val % 16 := by
    decide +kernel
  exact h ⟨b.toNat, b.toNat_lt⟩

theorem streamBit_cons_shift (b : Nat) (values : List Nat) (position : Nat) :
    streamBit 8 (b :: values) (8 + position) = streamBit 8 values position := by
  unfold streamBit
  have hd : (8 + position) / 8 = position / 8 + 1 := by omega
  have hm : (8 + position) % 8 = position % 8 := by omega
  rw [hd, hm, List.getD_cons_succ]

theorem regroup_cons (b : UInt8) (input : List UInt8) (count : Nat) :
    regroup 8 4 ((b :: input).map UInt8.toNat) (2 + count) =
      [b.toNat / 16, b.toNat % 16] ++ regroup 8 4 (input.map UInt8.toNat) count := by
  simp only [regroup, List.map_cons, List.range_add, List.map_append, List.map_map]
  change
    [ofBits 4 (fun j => b.toNat.testBit (7 - j)),
     ofBits 4 (fun j => b.toNat.testBit (3 - j))] ++ _ = _
  rw [ofBits_high, ofBits_low]
  congr 1
  apply List.map_congr_left
  intro i hi
  change ofBits 4 (fun j => streamBit 8 (b.toNat :: input.map UInt8.toNat)
      (4 * (2 + i) + j)) =
    ofBits 4 (fun j => streamBit 8 (input.map UInt8.toNat) (4 * i + j))
  apply congrArg (ofBits 4)
  funext j
  change streamBit 8 (b.toNat :: input.map UInt8.toNat) (4 * (2 + i) + j) =
    streamBit 8 (input.map UInt8.toNat) (4 * i + j)
  rw [show 4 * (2 + i) + j = 8 + (4 * i + j) by omega, streamBit_cons_shift]

theorem regroup_nibbles (input : List UInt8) :
    regroup 8 4 (input.map UInt8.toNat) (2 * input.length) =
      input.flatMap (fun b => [b.toNat / 16, b.toNat % 16]) := by
  induction input with
  | nil => rfl
  | cons b input ih =>
    rw [List.length_cons, show 2 * (input.length + 1) = 2 + 2 * input.length by omega]
    rw [regroup_cons, ih, List.flatMap_cons]

theorem base16Upper_encodedLength (n : Nat) :
    Alphabet.base16Upper.encodedLength n = 2 * n := by
  change (8 * n + 4 - 1) / 4 = 2 * n
  omega

theorem encode_eq_encodedBytes (input : List UInt8) :
    (encode .base16Upper .unpadded input.toByteArray).data.toList = encodedBytes input := by
  simp only [encode, List.size_toByteArray, base16Upper_encodedLength,
    List.toList_data_toByteArray, List.replicate_zero,
    List.append_nil, List.toList_toArray]
  change (regroup 8 4 (input.map UInt8.toNat) (2 * input.length)).map
    Alphabet.base16Upper.character = encodedBytes input
  rw [regroup_nibbles, List.map_flatMap]
  rfl

theorem upperEncoder_eq_encodedBytes (input : ByteArray) :
    Base16ct.Spec.Base16.upperEncoder input =
      (encodedBytes input.data.toList).toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [Base16ct.Spec.Base16.upperEncoder, encode, base16Upper_encodedLength,
    List.replicate_zero, List.append_nil, List.toList_toArray,
    List.toList_data_toByteArray]
  change (regroup 8 4 (input.data.toList.map UInt8.toNat)
    (2 * input.data.toList.length)).map Alphabet.base16Upper.character =
      encodedBytes input.data.toList
  rw [regroup_nibbles, List.map_flatMap]
  rfl

theorem encode_length (input : List UInt8) :
    (encode .base16Upper .unpadded input.toByteArray).data.toList.length = 2 * input.length := by
  rw [encode_eq_encodedBytes, encodedBytes_length]

theorem character_eq (n : Nat) (h : n < 16) :
    Alphabet.base16Upper.character n = UInt8.ofNat (n + if n < 10 then 48 else 55) := by
  have hn : ∀ i : Fin 16, Alphabet.base16Upper.character i.val =
      UInt8.ofNat (i.val + if i.val < 10 then 48 else 55) := by
    decide +kernel
  exact hn ⟨n, h⟩

theorem character_toNat (n : Nat) (h : n < 16) :
    (Alphabet.base16Upper.character n).toNat = n + if n < 10 then 48 else 55 := by
  have hn : ∀ i : Fin 16, (Alphabet.base16Upper.character i.val).toNat =
      i.val + if i.val < 10 then 48 else 55 := by
    decide +kernel
  exact hn ⟨n, h⟩

theorem encodeByte_eq (b : UInt8) :
    encodeByte b =
      [UInt8.ofNat (b.toNat / 16 + if b.toNat / 16 < 10 then 48 else 55),
       UInt8.ofNat (b.toNat % 16 + if b.toNat % 16 < 10 then 48 else 55)] := by
  have hb := b.toNat_lt
  simp only [encodeByte, character_eq _ (show b.toNat / 16 < 16 by omega),
    character_eq _ (show b.toNat % 16 < 16 by omega)]

theorem encodedBytes_getElem_even (input : List UInt8) (i : Nat) (h : i < input.length) :
    (encodedBytes input)[2 * i]'(by rw [encodedBytes_length]; omega) =
      Alphabet.base16Upper.character (input[i].toNat / 16) := by
  induction input generalizing i with
  | nil => simp only [List.length_nil] at h; omega
  | cons b input ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi : i < input.length := by simp only [List.length_cons] at h; omega
      simpa only [encodedBytes_cons, encodeByte, List.cons_append, List.nil_append,
        Nat.mul_succ, List.getElem_cons_succ] using ih i hi

theorem encodedBytes_getElem_odd (input : List UInt8) (i : Nat) (h : i < input.length) :
    (encodedBytes input)[2 * i + 1]'(by rw [encodedBytes_length]; omega) =
      Alphabet.base16Upper.character (input[i].toNat % 16) := by
  induction input generalizing i with
  | nil => simp only [List.length_nil] at h; omega
  | cons b input ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi : i < input.length := by simp only [List.length_cons] at h; omega
      simpa only [encodedBytes_cons, encodeByte, List.cons_append, List.nil_append,
        Nat.mul_succ, Nat.add_assoc, List.getElem_cons_succ] using ih i hi

theorem encodedBytes_getD_even (input : List UInt8) (i : Nat) (h : i < input.length) :
    (encodedBytes input).getD (2 * i) 0 =
      Alphabet.base16Upper.character ((input.getD i 0).toNat / 16) := by
  have hi : 2 * i < (encodedBytes input).length := by rw [encodedBytes_length]; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
    List.getElem?_eq_getElem hi, Option.getD_some]
  exact encodedBytes_getElem_even input i h

theorem encodedBytes_getD_odd (input : List UInt8) (i : Nat) (h : i < input.length) :
    (encodedBytes input).getD (2 * i + 1) 0 =
      Alphabet.base16Upper.character ((input.getD i 0).toNat % 16) := by
  have hi : 2 * i + 1 < (encodedBytes input).length := by rw [encodedBytes_length]; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
    List.getElem?_eq_getElem hi, Option.getD_some]
  exact encodedBytes_getElem_odd input i h

end Base16ct.Proofs.Base16ctUpperEncodeCorrect
