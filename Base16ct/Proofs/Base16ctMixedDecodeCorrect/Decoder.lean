import Base16ct.Spec.Base16
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Decoder.Case
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Decoder.List
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Decoder.Regroup
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Decoder.Validation

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect

open Standards.RFC.BaseEncodings Base16ct.Spec.Base16

theorem mixedDecodeList_eq_mapM (input : List UInt8) :
    mixedDecodeList input =
      if input.length % 2 = 0 then (input.mapM mixedNibble).map pairOctets else none := by
  induction input using mixedDecodeList.induct with
  | case1 => rfl
  | case2 c => simp [mixedDecodeList]
  | case3 high low rest ih =>
      have hm : (rest.length + 1 + 1) % 2 = rest.length % 2 := by omega
      simp only [mixedDecodeList_cons_cons, List.length_cons, hm, ih, List.mapM_cons]
      by_cases he : rest.length % 2 = 0
      · simp only [he, ite_true]
        cases mixedNibble high <;> cases mixedNibble low <;>
          cases rest.mapM mixedNibble <;> rfl
      · simp only [he, ite_false]
        cases mixedNibble high <;> cases mixedNibble low <;> rfl

theorem decode_base16Upper_toList (input : List UInt8) :
    (decode .base16Upper .unpadded input.toByteArray).map (fun b ↦ b.data.toList) =
      if input.length % 2 = 0 then
        (input.mapM Alphabet.base16Upper.value?).map
          (fun values ↦ (octetsOf .base16Upper values).data.toList)
      else none := by
  cases hc : characterValues .base16Upper .unpadded input.toByteArray with
  | none =>
      simp only [decode, hc, Option.bind_eq_bind, Option.bind_none, Option.map_none]
      by_cases he : input.length % 2 = 0
      · simp only [he, ite_true]
        cases hm : input.mapM Alphabet.base16Upper.value? with
        | none => rfl
        | some values =>
            have hh := (characterValues_base16Upper_iff input values).mpr ⟨hm, he⟩
            rw [hc] at hh
            contradiction
      · simp [he]
  | some values =>
      have hv := (characterValues_base16Upper_iff input values).mp hc
      have hl := option_mapM_length hv.1
      have hp := padBitsZero_base16Upper values (by omega)
      simp [decode, hc, hp, hv.1, hv.2]

theorem mixedDecoder_toList (input : List UInt8) :
    (mixedDecoder input.toByteArray).map (fun b ↦ b.data.toList) = mixedDecodeList input := by
  unfold mixedDecoder decodeIgnoringCase
  simp only [List.toList_data_toByteArray]
  change (decode .base16Upper .unpadded
    (⟨(input.map mixedMatchCase).toArray⟩ : ByteArray)).map (fun b ↦ b.data.toList) = _
  have hb : (⟨(input.map mixedMatchCase).toArray⟩ : ByteArray) =
      (input.map mixedMatchCase).toByteArray := ByteArray.ext List.data_toByteArray.symm
  rw [hb, decode_base16Upper_toList, List.length_map, mapM_mixedMatchCase,
    mixedDecodeList_eq_mapM]
  by_cases he : input.length % 2 = 0
  · simp only [he, ite_true]
    cases hm : input.mapM mixedNibble with
    | none => rfl
    | some values =>
        simp only [Option.map_some, octetsOf_base16Upper values (mapM_mixedNibble_lt hm)]
  · simp [he]

theorem mixedDecodeResult_eq (input : List UInt8) (outputCapacity : Nat) :
    (decodeInto mixedDecoder input.toByteArray outputCapacity).map (fun b ↦ b.data.toList) =
      if input.length % 2 ≠ 0 ∨ outputCapacity < input.length / 2 then
        .error .invalidLength
      else match mixedDecodeList input with
        | some output => .ok output
        | none => .error .invalidEncoding := by
  simp only [decodeInto, decodedLength, List.size_toByteArray]
  by_cases he : input.length % 2 = 0
  · simp only [he, ite_true, ne_eq, not_true_eq_false, false_or]
    by_cases hc : outputCapacity < input.length / 2
    · simp [hc, Except.map]
    · simp only [hc, ite_false]
      rw [← mixedDecoder_toList input]
      cases mixedDecoder input.toByteArray <;> rfl
  · simp [he, Except.map]

theorem mixedDecodeResult_byteArray (input : ByteArray) (outputCapacity : Nat) :
    Base16ct.Spec.Base16.decodeInto Base16ct.Spec.Base16.mixedDecoder input outputCapacity =
    if input.data.toList.length % 2 ≠ 0 ∨ outputCapacity < input.data.toList.length / 2 then
      .error .invalidLength
    else match mixedDecodeList input.data.toList with
      | some output => .ok output.toByteArray
      | none => .error .invalidEncoding := by
  have roundtrip (b : ByteArray) : b.data.toList.toByteArray = b := by
    apply ByteArray.ext
    simp only [List.data_toByteArray, Array.toArray_toList]
  have h := mixedDecodeResult_eq input.data.toList outputCapacity
  rw [roundtrip] at h
  have hm := congrArg (Except.map List.toByteArray) h
  have inverse (r : Except Base16ct.Spec.Base16.Error ByteArray) :
      (r.map (fun b ↦ b.data.toList)).map List.toByteArray = r := by
    cases r with
    | error e => rfl
    | ok b => change Except.ok b.data.toList.toByteArray = Except.ok b; rw [roundtrip]
  rw [inverse] at hm
  rw [hm]
  split
  · rfl
  · cases mixedDecodeList input.data.toList <;> rfl

end Base16ct.Proofs.Base16ctMixedDecodeCorrect
