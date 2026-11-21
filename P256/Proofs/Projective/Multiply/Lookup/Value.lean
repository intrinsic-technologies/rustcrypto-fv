import P256.Proofs.Projective.Multiply.Operations

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.ProjectiveLookup

def digitMagnitude (digit : BitVec 8) : Nat :=
  (if digit.msb then -digit else digit).toNat

def selectMagnitude (table : Fin 8 → Projective) (magnitude : Nat) : Projective :=
  if h : 0 < magnitude ∧ magnitude ≤ 8 then
    table ⟨magnitude - 1, by omega⟩
  else Projective.identity

def signedLookup (table : Fin 8 → Projective) (digit : BitVec 8) : Projective :=
  let point := selectMagnitude table (digitMagnitude digit)
  if digit.msb then point.negate else point

theorem digitMagnitude_eq_natAbs (digit : BitVec 8) :
    digitMagnitude digit = digit.toInt.natAbs := by
  revert digit
  decide +kernel

theorem selectMagnitude_zero (table : Fin 8 → Projective) :
    selectMagnitude table 0 = Projective.identity := by
  simp [selectMagnitude]

end P256.Proofs.Projective.Multiply.ProjectiveLookup
