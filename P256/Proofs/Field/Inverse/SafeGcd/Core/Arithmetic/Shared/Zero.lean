import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Invariant

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Arithmetic

open P256.Proofs.Field.Schoolbook (packFour)
open P256.Proofs.Field.Inverse.SafeGcd.Core
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd

theorem zeroWords_iff (w : Vector (BitVec 64) 4) :
    zeroWords w = true ↔ packFour (w.map BitVec.toNat) = 0 := by
  rw [zeroWords, beq_iff_eq]
  change (w[0] ||| w[1] ||| w[2] ||| w[3]) = 0#64 ↔ _
  simp only [BitVec.or_eq_zero_iff]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
    simp only [packFour, Vector.getElem_map, h0, h1, h2, h3, BitVec.toNat_zero,
      Nat.mul_zero, Nat.add_zero]
  · intro h
    simp only [packFour, Vector.getElem_map, P256.Proofs.Field.Montgomery.wordBase] at h
    exact ⟨⟨⟨BitVec.eq_of_toNat_eq (by change _ = 0; omega),
      BitVec.eq_of_toNat_eq (by change _ = 0; omega)⟩,
      BitVec.eq_of_toNat_eq (by change _ = 0; omega)⟩,
      BitVec.eq_of_toNat_eq (by change _ = 0; omega)⟩

theorem zeroWords_value (w : SignedWords) : zeroWords w.words = true ↔ value w = 0 := by
  rw [zeroWords_iff]
  change magnitude w = 0 ↔ value w = 0
  rw [← value_natAbs, Int.natAbs_eq_zero]

end P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Arithmetic
