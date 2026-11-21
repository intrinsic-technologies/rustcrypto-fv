import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Compatibility

namespace Base16ct.Proofs.Base16ctLowerDecodeCorrect

open Standards.RFC.BaseEncodings
open Base16ct.Proofs.Base16ctUpperDecodeCorrect

theorem lowerValue_eq (c : UInt8) :
    Alphabet.base16Lower.value? c = RFC4648.valueOfCharacter [.lower] c := by
  change RFC4648.Alphabet.lower.table.idxOf? c = _
  simp only [RFC4648.valueOfCharacter, List.findSome?]
  cases RFC4648.Alphabet.lower.table.idxOf? c <;> rfl

theorem lowerValue_lt {c : UInt8} {n : Nat}
    (h : Alphabet.base16Lower.value? c = some n) : n < 16 := by
  have hn := (List.idxOf?_eq_some_iff.mp h).choose
  exact hn

theorem lowerEncodedLength_iff (n : Nat) :
    Alphabet.base16Lower.encodedLength (4 * n / 8) = n ↔ n % 2 = 0 := by
  change (8 * (4 * n / 8) + 4 - 1) / 4 = n ↔ n % 2 = 0
  omega

theorem lowerPadBitsZero {values : List Nat} (h : values.length % 2 = 0) :
    padBitsZero Alphabet.base16Lower values = true := by
  have hz : 4 * values.length - 8 * (4 * values.length / 8) = 0 := by omega
  change (List.range (4 * values.length - 8 * (4 * values.length / 8))).all _ = true
  rw [hz]
  rfl

theorem lowerStreamBit_pair_shift (high low : Nat) (rest : List Nat) (i j : Nat) :
    streamBit 4 (high :: low :: rest) (8 * (i + 1) + j) =
      streamBit 4 rest (8 * i + j) := by
  have hd : (8 * (i + 1) + j) / 4 = (8 * i + j) / 4 + 2 := by omega
  have hm : (8 * (i + 1) + j) % 4 = (8 * i + j) % 4 := by omega
  simp only [streamBit, hd, hm, List.getD_cons_succ]

theorem lowerOfBits_pair {high low : Nat} (hh : high < 16) (hl : low < 16)
    (rest : List Nat) :
    ofBits 8 (fun j => streamBit 4 (high :: low :: rest) j) = 16 * high + low := by
  simp only [ofBits, List.range_succ, List.range_zero, List.foldl_append,
    List.foldl_cons, List.foldl_nil, streamBit, Nat.reduceDiv, Nat.reduceMod,
    Nat.reduceSub, List.getD_cons_zero, List.getD_cons_succ, Nat.toNat_testBit,
    Nat.reducePow]
  omega

theorem lowerRegroup_pair {high low : Nat} (hh : high < 16) (hl : low < 16)
    (rest : List Nat) (count : Nat) :
    regroup 4 8 (high :: low :: rest) (count + 1) =
      (16 * high + low) :: regroup 4 8 rest count := by
  simp only [regroup, List.range_succ_eq_map, List.map_cons, Nat.mul_zero,
    Nat.zero_add, lowerOfBits_pair hh hl, List.map_map]
  apply congrArg (List.cons (16 * high + low))
  apply List.map_congr_left
  intro i hi
  apply congrArg (ofBits 8)
  funext j
  exact lowerStreamBit_pair_shift high low rest i j

def lowerDecodeValues (values : List Nat) : Option (List UInt8) :=
  if values.length % 2 = 0 then
    some ((regroup 4 8 values (values.length / 2)).map UInt8.ofNat)
  else none

theorem lowerDecodeValues_pair {high low : Nat} (hh : high < 16) (hl : low < 16)
    (rest : List Nat) :
    lowerDecodeValues (high :: low :: rest) =
      (lowerDecodeValues rest).map (UInt8.ofNat (16 * high + low) :: ·) := by
  have he : (rest.length + 1 + 1) % 2 = 0 ↔ rest.length % 2 = 0 := by omega
  have hc : (rest.length + 1 + 1) / 2 = rest.length / 2 + 1 := by omega
  simp only [lowerDecodeValues, List.length_cons, he, hc]
  split
  · rw [lowerRegroup_pair hh hl]
    rfl
  · rfl

theorem lowerDecodeValues_model (input : List UInt8) :
    (input.mapM Alphabet.base16Lower.value?).bind lowerDecodeValues =
      RFC4648.decode [.lower] input := by
  induction input using RFC4648.decode.induct with
  | case1 => rfl
  | case2 high low rest ih =>
    simp only [List.mapM_cons, RFC4648.decode, ← lowerValue_eq]
    cases hh : Alphabet.base16Lower.value? high with
    | none => rfl
    | some h =>
      cases hl : Alphabet.base16Lower.value? low with
      | none => rfl
      | some l =>
        rw [← ih]
        cases ht : rest.mapM Alphabet.base16Lower.value? with
        | none => rfl
        | some values =>
          simp only [bind, Option.bind_some, pure]
          rw [lowerDecodeValues_pair (lowerValue_lt hh) (lowerValue_lt hl)]
          cases lowerDecodeValues values <;> rfl
  | case3 c =>
    simp only [List.mapM_cons, List.mapM_nil]
    cases Alphabet.base16Lower.value? c <;> rfl

theorem lowerCharacterValues_eq (input : List UInt8) :
    characterValues Alphabet.base16Lower .unpadded input.toByteArray =
      (input.mapM Alphabet.base16Lower.value?).bind
        (fun values => if values.length % 2 = 0 then some values else none) := by
  simp only [characterValues, removePadding, List.toList_data_toByteArray,
    Option.bind_some, bind]
  congr 1
  funext values
  change (if Alphabet.base16Lower.encodedLength (4 * values.length / 8) = values.length
    then some values else none) = _
  simp only [lowerEncodedLength_iff]

theorem lowerDecoder_eq_model (input : List UInt8) :
    (Base16ct.Spec.Base16.lowerDecoder input.toByteArray).map (fun b => b.data.toList) =
      RFC4648.decode [.lower] input := by
  rw [← lowerDecodeValues_model]
  simp only [Base16ct.Spec.Base16.lowerDecoder, decode, lowerCharacterValues_eq]
  cases hv : input.mapM Alphabet.base16Lower.value? with
  | none => rfl
  | some values =>
    simp only [Option.bind_some, bind]
    by_cases he : values.length % 2 = 0
    · simp only [he, ite_true, Option.bind_some, lowerPadBitsZero he,
        lowerDecodeValues, Option.map_some, octetsOf]
      have hc : 4 * values.length / 8 = values.length / 2 := by omega
      change some ((regroup 4 8 values (4 * values.length / 8)).map UInt8.ofNat) = _
      rw [hc]
    · simp only [he, ite_false, Option.bind_none, Option.map_none, lowerDecodeValues]

 theorem decodeInto_eq_pair (decoder : ByteArray → Option ByteArray)
    (alphabets : List RFC4648.Alphabet) (input : List UInt8) (capacity : Nat)
    (hdecoder : (decoder input.toByteArray).map (fun b => b.data.toList) =
      RFC4648.decode alphabets input) :
    Base16ct.Spec.Base16.decodeInto decoder input.toByteArray capacity =
      (pairDecodeResult alphabets input capacity).map List.toByteArray := by
  unfold Base16ct.Spec.Base16.decodeInto Base16ct.Spec.Base16.decodedLength pairDecodeResult
  simp only [List.size_toByteArray]
  by_cases he : input.length % 2 = 0
  · simp only [he, ite_true, ne_eq, not_true_eq_false, false_or]
    by_cases hc : capacity < input.length / 2
    · simp only [hc, ite_true, Except.map]
    · simp only [hc, ite_false]
      rw [← hdecoder]
      cases hd : decoder input.toByteArray with
      | none => rfl
      | some output =>
        simp only [Option.map_some, Except.map]
        congr 1
        apply ByteArray.ext
        simp only [List.data_toByteArray, Array.toArray_toList]
  · simp only [he, ite_false, ne_eq, not_false_eq_true, true_or, ite_true, Except.map]

end Base16ct.Proofs.Base16ctLowerDecodeCorrect
