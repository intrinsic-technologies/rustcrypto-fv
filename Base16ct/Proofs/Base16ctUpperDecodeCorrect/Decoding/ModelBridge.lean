import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Model

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

open Standards.RFC.BaseEncodings

theorem upperValue_eq (c : UInt8) :
    Alphabet.base16Upper.value? c = RFC4648.valueOfCharacter [.upper] c := by
  change RFC4648.Alphabet.upper.table.idxOf? c = _
  simp only [RFC4648.valueOfCharacter, List.findSome?]
  cases RFC4648.Alphabet.upper.table.idxOf? c <;> rfl

theorem upperValue_lt {c : UInt8} {n : Nat}
    (h : Alphabet.base16Upper.value? c = some n) : n < 16 := by
  have hn := (List.idxOf?_eq_some_iff.mp h).choose
  exact hn

theorem upperEncodedLength_iff (n : Nat) :
    Alphabet.base16Upper.encodedLength (4 * n / 8) = n ↔ n % 2 = 0 := by
  change (8 * (4 * n / 8) + 4 - 1) / 4 = n ↔ n % 2 = 0
  omega

theorem upperPadBitsZero {values : List Nat} (h : values.length % 2 = 0) :
    padBitsZero Alphabet.base16Upper values = true := by
  have hz : 4 * values.length - 8 * (4 * values.length / 8) = 0 := by omega
  change (List.range (4 * values.length - 8 * (4 * values.length / 8))).all _ = true
  rw [hz]
  rfl

theorem upperStreamBit_pair_shift (high low : Nat) (rest : List Nat) (i j : Nat) :
    streamBit 4 (high :: low :: rest) (8 * (i + 1) + j) =
      streamBit 4 rest (8 * i + j) := by
  have hd : (8 * (i + 1) + j) / 4 = (8 * i + j) / 4 + 2 := by omega
  have hm : (8 * (i + 1) + j) % 4 = (8 * i + j) % 4 := by omega
  simp only [streamBit, hd, hm, List.getD_cons_succ]

theorem upperOfBits_pair {high low : Nat} (hh : high < 16) (hl : low < 16)
    (rest : List Nat) :
    ofBits 8 (fun j => streamBit 4 (high :: low :: rest) j) = 16 * high + low := by
  simp only [ofBits, List.range_succ, List.range_zero, List.foldl_append,
    List.foldl_cons, List.foldl_nil, streamBit, Nat.reduceDiv, Nat.reduceMod,
    Nat.reduceSub, List.getD_cons_zero, List.getD_cons_succ, Nat.toNat_testBit,
    Nat.reducePow]
  omega

theorem upperRegroup_pair {high low : Nat} (hh : high < 16) (hl : low < 16)
    (rest : List Nat) (count : Nat) :
    regroup 4 8 (high :: low :: rest) (count + 1) =
      (16 * high + low) :: regroup 4 8 rest count := by
  simp only [regroup, List.range_succ_eq_map, List.map_cons, Nat.mul_zero,
    Nat.zero_add, upperOfBits_pair hh hl, List.map_map]
  apply congrArg (List.cons (16 * high + low))
  apply List.map_congr_left
  intro i hi
  apply congrArg (ofBits 8)
  funext j
  exact upperStreamBit_pair_shift high low rest i j

def upperDecodeValues (values : List Nat) : Option (List UInt8) :=
  if values.length % 2 = 0 then
    some ((regroup 4 8 values (values.length / 2)).map UInt8.ofNat)
  else none

theorem upperDecodeValues_pair {high low : Nat} (hh : high < 16) (hl : low < 16)
    (rest : List Nat) :
    upperDecodeValues (high :: low :: rest) =
      (upperDecodeValues rest).map (UInt8.ofNat (16 * high + low) :: ·) := by
  have he : (rest.length + 1 + 1) % 2 = 0 ↔ rest.length % 2 = 0 := by omega
  have hc : (rest.length + 1 + 1) / 2 = rest.length / 2 + 1 := by omega
  simp only [upperDecodeValues, List.length_cons, he, hc]
  split
  · rw [upperRegroup_pair hh hl]
    rfl
  · rfl

theorem upperDecodeValues_model (input : List UInt8) :
    (input.mapM Alphabet.base16Upper.value?).bind upperDecodeValues =
      RFC4648.decode [.upper] input := by
  induction input using RFC4648.decode.induct with
  | case1 => rfl
  | case2 high low rest ih =>
    simp only [List.mapM_cons, RFC4648.decode, ← upperValue_eq]
    cases hh : Alphabet.base16Upper.value? high with
    | none => rfl
    | some h =>
      cases hl : Alphabet.base16Upper.value? low with
      | none => rfl
      | some l =>
        rw [← ih]
        cases ht : rest.mapM Alphabet.base16Upper.value? with
        | none => rfl
        | some values =>
          simp only [bind, Option.bind_some, pure]
          rw [upperDecodeValues_pair (upperValue_lt hh) (upperValue_lt hl)]
          cases upperDecodeValues values <;> rfl
  | case3 c =>
    simp only [List.mapM_cons, List.mapM_nil]
    cases Alphabet.base16Upper.value? c <;> rfl

theorem upperCharacterValues_eq (input : List UInt8) :
    characterValues Alphabet.base16Upper .unpadded input.toByteArray =
      (input.mapM Alphabet.base16Upper.value?).bind
        (fun values => if values.length % 2 = 0 then some values else none) := by
  simp only [characterValues, removePadding, List.toList_data_toByteArray,
    Option.bind_some, bind]
  congr 1
  funext values
  change (if Alphabet.base16Upper.encodedLength (4 * values.length / 8) =
    values.length then some values else none) = _
  simp only [upperEncodedLength_iff]

theorem upperDecoder_eq_model (input : List UInt8) :
    (Base16ct.Spec.Base16.upperDecoder input.toByteArray).map (fun b => b.data.toList) =
      RFC4648.decode [.upper] input := by
  rw [← upperDecodeValues_model]
  simp only [Base16ct.Spec.Base16.upperDecoder, decode, upperCharacterValues_eq]
  cases hv : input.mapM Alphabet.base16Upper.value? with
  | none => rfl
  | some values =>
    simp only [Option.bind_some, bind]
    by_cases he : values.length % 2 = 0
    · simp only [he, ite_true, Option.bind_some, upperPadBitsZero he,
        upperDecodeValues, Option.map_some, octetsOf]
      have hc : 4 * values.length / 8 = values.length / 2 := by omega
      change some ((regroup 4 8 values (4 * values.length / 8)).map UInt8.ofNat) = _
      rw [hc]
    · simp only [he, ite_false, Option.bind_none, Option.map_none, upperDecodeValues]

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
