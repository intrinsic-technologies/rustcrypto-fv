import P256.Proofs.Projective.Multiply.Machine.Lookup.Interface

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Lookup

open P256.Spec ProjectiveLookup

theorem abs_instructions (digit : BitVec 8) :
    (digit ^^^ digit.sshiftRight 7) - digit.sshiftRight 7 =
      BitVec.ofNat 8 (digitMagnitude digit) := by
  revert digit
  decide +kernel

theorem sign_instruction (digit : BitVec 8) :
    digit >>> 7 = if digit.msb then 1 else 0 := by
  revert digit
  decide +kernel

theorem magnitude_eq (digit : BitVec 8) (index : Fin 8) :
    (BitVec.ofNat 8 (digitMagnitude digit) == BitVec.ofNat 8 (index.val + 1)) =
      decide (digitMagnitude digit = index.val + 1) := by
  revert digit index
  decide +kernel

theorem selectMagnitude_at (table : Fin 8 → Projective) (index : Fin 8) :
    selectMagnitude table (index.val + 1) = table index := by
  have h : 0 < index.val + 1 ∧ index.val + 1 ≤ 8 := by have := index.isLt; omega
  simp [selectMagnitude, h]

end P256.Proofs.Projective.Multiply.Machine.Lookup
