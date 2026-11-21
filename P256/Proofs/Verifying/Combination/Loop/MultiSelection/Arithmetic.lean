import P256.Proofs.Verifying.Combination.Loop.MultiDigitState

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Selection

open P256.Proofs.Projective P256.Proofs.Program P256.Proofs.Program.ScalarFrame

theorem validDigit_cases {d : Int} (h : Naf.ValidDigit d) :
    d = -15 ∨ d = -13 ∨ d = -11 ∨ d = -9 ∨ d = -7 ∨ d = -5 ∨ d = -3 ∨ d = -1 ∨
      d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 7 ∨ d = 9 ∨ d = 11 ∨ d = 13 ∨ d = 15 := by
  rcases h with hz | ⟨hodd, hlo, hhi⟩ <;> omega

theorem digit_zero {d : Int} (h : Naf.ValidDigit d) :
    (BitVec.ofInt 8 d = 0#8) ↔ d = 0 := by
  rcases validDigit_cases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem digit_sign {d : Int} (h : Naf.ValidDigit d) :
    (BitVec.ofInt 8 d).msb = decide (d < 0) := by
  rcases validDigit_cases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem digit_index_lt {d : Int} (h : Naf.ValidDigit d) : d.natAbs / 2 < 8 := by
  rcases validDigit_cases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem signedLookup_nonzero (table : Fin 8 → Projective) {d : Int}
    (h : Naf.ValidDigit d) (nonzero : d ≠ 0) :
    Algebra.signedLookup table d =
      if d < 0 then (table ⟨d.natAbs / 2, digit_index_lt h⟩).negate
      else table ⟨d.natAbs / 2, digit_index_lt h⟩ := by
  rcases validDigit_cases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact (nonzero rfl).elim | simp [Algebra.signedLookup, Algebra.selectMagnitude]

end P256.Proofs.Verifying.Combination.Loop.Multi.Selection
