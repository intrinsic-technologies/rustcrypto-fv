import Standards.RFC.BaseEncodings.Decoding

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect

open Standards.RFC.BaseEncodings

theorem option_mapM_length {α β : Type} {f : α → Option β} {xs : List α}
    {ys : List β} (h : xs.mapM f = some ys) : xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst ys
      rfl
  | cons x xs ih =>
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨y, _, ys', hys, rfl⟩ := h
      simpa only [List.length_cons] using congrArg Nat.succ (ih hys)

private theorem encodedLength_base16Upper_iff (n : Nat) :
    Alphabet.base16Upper.encodedLength (Alphabet.base16Upper.bits * n / 8) = n ↔
      n % 2 = 0 := by
  change (8 * (4 * n / 8) + 4 - 1) / 4 = n ↔ n % 2 = 0
  omega

theorem characterValues_base16Upper_iff (xs : List UInt8) (vs : List Nat) :
    characterValues .base16Upper .unpadded xs.toByteArray = some vs ↔
      xs.mapM Alphabet.base16Upper.value? = some vs ∧ xs.length % 2 = 0 := by
  simp only [characterValues, removePadding, List.toList_data_toByteArray,
    Option.bind_eq_bind, Option.bind_some]
  cases hm : xs.mapM Alphabet.base16Upper.value? with
  | none => simp
  | some values =>
      have hl := option_mapM_length hm
      simp only [Option.bind_some]
      by_cases he : values.length % 2 = 0
      · have h := (encodedLength_base16Upper_iff values.length).mpr he
        simp [h, hl, he]
      · have h := mt (encodedLength_base16Upper_iff values.length).mp he
        simp [h, hl, he]

theorem padBitsZero_base16Upper (vs : List Nat) (heven : vs.length % 2 = 0) :
    padBitsZero .base16Upper vs = true := by
  have hused : 4 * vs.length - 8 * (4 * vs.length / 8) = 0 := by omega
  change (List.range (4 * vs.length - 8 * (4 * vs.length / 8))).all _ = true
  rw [hused]
  rfl

end Base16ct.Proofs.Base16ctMixedDecodeCorrect
