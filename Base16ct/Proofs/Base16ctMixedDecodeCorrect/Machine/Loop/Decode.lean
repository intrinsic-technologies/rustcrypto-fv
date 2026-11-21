import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Arithmetic
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Decoder.List

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

def mixedLoopBytes : List UInt8 → List UInt8
  | [] => []
  | [_] => []
  | high :: low :: rest => (⟨(pairWord high low).setWidth 8⟩ : UInt8) :: mixedLoopBytes rest

def mixedLoopMarker : List UInt8 → BitVec 64
  | [] => 0
  | [_] => 255
  | high :: low :: rest =>
      ((pairWord high low).extractLsb' 8 8).setWidth 64 ||| mixedLoopMarker rest

theorem mixedLoopBytes_nil : mixedLoopBytes [] = [] := rfl

theorem mixedLoopBytes_singleton (c : UInt8) : mixedLoopBytes [c] = [] := rfl

theorem mixedLoopBytes_cons_cons (high low : UInt8) (rest : List UInt8) :
    mixedLoopBytes (high :: low :: rest) =
      (⟨(pairWord high low).setWidth 8⟩ : UInt8) :: mixedLoopBytes rest := rfl

theorem mixedLoopMarker_nil : mixedLoopMarker [] = 0 := rfl

theorem mixedLoopMarker_singleton (c : UInt8) : mixedLoopMarker [c] = 255 := rfl

theorem mixedLoopMarker_cons_cons (high low : UInt8) (rest : List UInt8) :
    mixedLoopMarker (high :: low :: rest) =
      ((pairWord high low).extractLsb' 8 8).setWidth 64 ||| mixedLoopMarker rest := rfl

theorem pairWord_marker64 (high low : UInt8) :
    ((pairWord high low).extractLsb' 8 8).setWidth 64 =
      if (mixedNibble high).isSome && (mixedNibble low).isSome then 0 else 255 := by
  rw [pairWord_marker]
  split <;> rfl

theorem pairWord_marker64_eq_zero_iff (high low : UInt8) :
    ((pairWord high low).extractLsb' 8 8).setWidth 64 = 0 ↔
      (mixedNibble high).isSome ∧ (mixedNibble low).isSome := by
  rw [pairWord_marker64]
  cases mixedNibble high <;> cases mixedNibble low <;> simp

theorem mixedLoopMarker_eq_zero_or (input : List UInt8) :
    mixedLoopMarker input = 0 ∨ mixedLoopMarker input = 255 := by
  induction input using mixedLoopMarker.induct with
  | case1 => exact Or.inl rfl
  | case2 c => exact Or.inr rfl
  | case3 high low rest ih =>
      rw [mixedLoopMarker_cons_cons, BitVec.or_comm]
      exact pairWord_accumulate_cases (mixedLoopMarker rest) high low ih

theorem mixedLoopMarker_eq_zero_iff (input : List UInt8) :
    mixedLoopMarker input = 0 ↔ (mixedDecodeList input).isSome := by
  induction input using mixedLoopMarker.induct with
  | case1 => simp [mixedLoopMarker, mixedDecodeList]
  | case2 c => simp [mixedLoopMarker, mixedDecodeList]
  | case3 high low rest ih =>
      have hor :
          (((pairWord high low).extractLsb' 8 8).setWidth 64 ||| mixedLoopMarker rest) = 0 ↔
            ((pairWord high low).extractLsb' 8 8).setWidth 64 = 0 ∧ mixedLoopMarker rest = 0 :=
        BitVec.or_eq_zero_iff
      rw [mixedLoopMarker_cons_cons, hor, pairWord_marker64_eq_zero_iff, ih]
      cases hh : mixedNibble high <;> cases hl : mixedNibble low <;>
        cases ht : mixedDecodeList rest <;> simp [mixedDecodeList_cons_cons, hh, hl, ht]

theorem mixedLoopBytes_eq_of_decode {input output : List UInt8}
    (h : mixedDecodeList input = some output) : mixedLoopBytes input = output := by
  induction input using mixedDecodeList.induct generalizing output with
  | case1 =>
      simp only [mixedDecodeList_nil, Option.some.injEq] at h
      subst output
      rfl
  | case2 c => simp [mixedDecodeList_singleton] at h
  | case3 high low rest ih =>
      cases hh : mixedNibble high with
      | none => simp [mixedDecodeList_cons_cons, hh] at h
      | some hi =>
          cases hl : mixedNibble low with
          | none => simp [mixedDecodeList_cons_cons, hh, hl] at h
          | some lo =>
              cases ht : mixedDecodeList rest with
              | none => simp [mixedDecodeList_cons_cons, hh, hl, ht] at h
              | some tail =>
                  simp only [mixedDecodeList_cons_cons, hh, hl, ht, Option.bind_eq_bind,
                    Option.bind_some, Option.pure_def, Option.some.injEq] at h
                  subst output
                  rw [mixedLoopBytes_cons_cons, pairWord_byte hh hl, ih ht]

theorem mixedDecodeList_eq_some_iff_loop {input output : List UInt8} :
    mixedDecodeList input = some output ↔
      mixedLoopMarker input = 0 ∧ mixedLoopBytes input = output := by
  constructor
  · intro h
    refine ⟨?_, mixedLoopBytes_eq_of_decode h⟩
    rw [mixedLoopMarker_eq_zero_iff, h]
    rfl
  · rintro ⟨hmarker, hbytes⟩
    obtain ⟨actual, hactual⟩ :=
      Option.isSome_iff_exists.mp ((mixedLoopMarker_eq_zero_iff input).mp hmarker)
    exact hactual.trans (congrArg some ((mixedLoopBytes_eq_of_decode hactual).symm.trans hbytes))

theorem mixedLoopBytes_length (input : List UInt8) :
    (mixedLoopBytes input).length = input.length / 2 := by
  induction input using mixedLoopBytes.induct with
  | case1 => rfl
  | case2 c => simp [mixedLoopBytes_singleton]
  | case3 high low rest ih =>
      simp only [mixedLoopBytes_cons_cons, List.length_cons, ih]
      omega

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
