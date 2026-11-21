import K256.Proofs.ParseSignature.Contract

namespace K256.Proofs.ParseSignature

open K256.Proofs.Common X86.Machine

theorem scalarValue_eq_zero_iff (m : Ram) (base : BitVec 64) :
    scalarValue m base = 0 ↔ ∀ i < 4, scalarWord m base i = 0 := by
  change ((scalarWord m base 3).toNat * 2^64 + (scalarWord m base 2).toNat) * 2^128 +
      (scalarWord m base 1).toNat * 2^64 + (scalarWord m base 0).toNat = 0 ↔ _
  constructor
  · intro h i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> apply BitVec.eq_of_toNat_eq <;>
      change _ = 0 <;> omega
  · intro h
    rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]
    decide

end K256.Proofs.ParseSignature
