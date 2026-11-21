import P256.Proofs.Projective.Multiply.Machine.Lookup.Digit

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Lookup

open P256.Spec ProjectiveLookup

def scanPrefix (table : Fin 8 → Projective) (magnitude count : Nat) : Projective :=
  if magnitude ≤ count then selectMagnitude table magnitude else Projective.identity

theorem scanPrefix_zero (table : Fin 8 → Projective) (magnitude : Nat) :
    scanPrefix table magnitude 0 = Projective.identity := by
  by_cases h : magnitude = 0
  · subst magnitude
    simp [scanPrefix, selectMagnitude_zero]
  · simp [scanPrefix, h]

theorem scanPrefix_step (table : Fin 8 → Projective) (magnitude : Nat) (index : Fin 8) :
    (if magnitude = index.val + 1 then table index else scanPrefix table magnitude index.val) =
      scanPrefix table magnitude (index.val + 1) := by
  by_cases h : magnitude = index.val + 1
  · subst magnitude
    simp [scanPrefix, selectMagnitude_at]
  · have hm : magnitude ≤ index.val + 1 ↔ magnitude ≤ index.val := by omega
    simp [scanPrefix, h, hm]

theorem scanPrefix_eight (table : Fin 8 → Projective) (magnitude : Nat) :
    scanPrefix table magnitude 8 = selectMagnitude table magnitude := by
  by_cases h : magnitude ≤ 8
  · simp [scanPrefix, h]
  · simp [scanPrefix, h, selectMagnitude]

end P256.Proofs.Projective.Multiply.Machine.Lookup
