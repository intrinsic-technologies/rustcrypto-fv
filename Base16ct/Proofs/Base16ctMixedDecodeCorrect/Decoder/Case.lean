import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Decoder.Nibble
import Standards.RFC.BaseEncodings.Decoding

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect

open Standards.RFC.BaseEncodings

def mixedMatchCase (c : UInt8) : UInt8 :=
  if Alphabet.base16Upper.characters.contains c then c else swapCase c

theorem mixedNibble_eq_value (c : UInt8) :
    Alphabet.base16Upper.value? (mixedMatchCase c) = mixedNibble c := by
  have table : ∀ n : Fin 256,
      Alphabet.base16Upper.value? (mixedMatchCase (UInt8.ofNat n.val)) =
        mixedNibble (UInt8.ofNat n.val) := by
    decide +kernel
  simpa only [UInt8.ofNat_toNat] using table ⟨c.toNat, c.toNat_lt_size⟩

theorem mapM_mixedMatchCase (input : List UInt8) :
    (input.map mixedMatchCase).mapM Alphabet.base16Upper.value? = input.mapM mixedNibble := by
  simp only [List.mapM_map, Function.comp_def, mixedNibble_eq_value]

theorem mapM_mixedNibble_lt {input : List UInt8} {values : List Nat}
    (h : input.mapM mixedNibble = some values) : ∀ n ∈ values, n < 16 := by
  induction input generalizing values with
  | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst values
      simp
  | cons c rest ih =>
      simp only [List.mapM_cons] at h
      cases hc : mixedNibble c with
      | none => simp [hc] at h
      | some n =>
          cases hr : rest.mapM mixedNibble with
          | none => simp [hc, hr] at h
          | some ns =>
              simp only [hc, hr, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.some.injEq] at h
              subst values
              intro v hv
              simp only [List.mem_cons] at hv
              rcases hv with rfl | hv
              · exact mixedNibble_lt hc
              · exact ih hr v hv

end Base16ct.Proofs.Base16ctMixedDecodeCorrect
