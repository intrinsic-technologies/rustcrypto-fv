import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Decoder.Nibble

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect

def mixedDecodeList : List UInt8 → Option (List UInt8)
  | [] => some []
  | [_] => none
  | high :: low :: rest => do
    let h ← mixedNibble high
    let l ← mixedNibble low
    let tail ← mixedDecodeList rest
    pure (UInt8.ofNat (16 * h + l) :: tail)

theorem mixedDecodeList_nil : mixedDecodeList [] = some [] := rfl

theorem mixedDecodeList_singleton (c : UInt8) : mixedDecodeList [c] = none := rfl

theorem mixedDecodeList_cons_cons (high low : UInt8) (rest : List UInt8) :
    mixedDecodeList (high :: low :: rest) = (do
      let h ← mixedNibble high
      let l ← mixedNibble low
      let tail ← mixedDecodeList rest
      pure (UInt8.ofNat (16 * h + l) :: tail)) := rfl

theorem mixedDecodeList_length {input output : List UInt8}
    (h : mixedDecodeList input = some output) : input.length = 2 * output.length := by
  induction input using mixedDecodeList.induct generalizing output with
  | case1 =>
      simp only [mixedDecodeList, Option.some.injEq] at h
      subst output
      rfl
  | case2 c => simp [mixedDecodeList] at h
  | case3 high low rest ih =>
      simp only [mixedDecodeList] at h
      cases hh : mixedNibble high with
      | none => simp [hh] at h
      | some hi =>
          cases hl : mixedNibble low with
          | none => simp [hh, hl] at h
          | some lo =>
              cases ht : mixedDecodeList rest with
              | none => simp [hh, hl, ht] at h
              | some tail =>
                  simp only [hh, hl, ht, Option.bind_eq_bind, Option.bind_some,
                    Option.pure_def, Option.some.injEq] at h
                  subst output
                  have := ih ht
                  simp only [List.length_cons]
                  omega

theorem mixedDecodeList_length_div_two {input output : List UInt8}
    (h : mixedDecodeList input = some output) : output.length = input.length / 2 := by
  have := mixedDecodeList_length h
  omega

theorem mixedDecodeList_even {input output : List UInt8}
    (h : mixedDecodeList input = some output) : input.length % 2 = 0 := by
  have := mixedDecodeList_length h
  omega

theorem mixedDecodeList_none_of_odd {input : List UInt8}
    (h : input.length % 2 ≠ 0) : mixedDecodeList input = none := by
  cases hd : mixedDecodeList input with
  | none => rfl
  | some output => exact False.elim (h (mixedDecodeList_even hd))

theorem mixedDecodeList_append (left right : List UInt8) (heven : left.length % 2 = 0) :
    mixedDecodeList (left ++ right) = (do
      let a ← mixedDecodeList left
      let b ← mixedDecodeList right
      pure (a ++ b)) := by
  induction left using mixedDecodeList.induct with
  | case1 => simp [mixedDecodeList]
  | case2 c => simp at heven
  | case3 high low rest ih =>
      have hrest : rest.length % 2 = 0 := by
        simp only [List.length_cons] at heven
        omega
      simp only [List.cons_append, mixedDecodeList_cons_cons, ih hrest]
      cases mixedNibble high <;> cases mixedNibble low <;>
        cases mixedDecodeList rest <;> cases mixedDecodeList right <;> rfl

theorem mixedDecodeList_append_some {left right a b : List UInt8}
    (ha : mixedDecodeList left = some a) (hb : mixedDecodeList right = some b) :
    mixedDecodeList (left ++ right) = some (a ++ b) := by
  simp only [mixedDecodeList_append left right (mixedDecodeList_even ha), ha, hb,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def]

end Base16ct.Proofs.Base16ctMixedDecodeCorrect
