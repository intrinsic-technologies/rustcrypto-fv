import K256.Proofs.Sec1.Affine.Compressed.Cube.Boundary
import K256.Proofs.Common.Field.SqrtRepr

namespace K256.Proofs.Sec1.Affine.Compressed

open K256.Proofs.Common.Field X86Proofs

theorem maskedX_eq_words (a b c d : Word) (ok : Bool) :
    let mask := -(BitVec.ofNat 64 ok.toNat)
    maskedX a b c d ok =
      #v[(d &&& 0xfffffffffffff) &&& mask, (shldResult 12 c d &&& 0xfffffffffffff) &&& mask,
        shldResult 24 b c &&& (mask &&& 0xfffffffffffff), (mask &&& 0xfffffffffffff) &&& shldResult 36 a b,
        (a >>> 16) &&& mask] := by
  cases ok
  · simp only [maskedX, Bool.false_eq_true, ↓reduceIte,
      show -(BitVec.ofNat 64 false.toNat) = 0#64 by decide,
      BitVec.and_zero, BitVec.zero_and]
    rfl
  · simp only [maskedX, ↓reduceIte, Uncompressed.unpack,
      show -(BitVec.ofNat 64 true.toNat) = BitVec.allOnes 64 by decide,
      BitVec.and_allOnes, BitVec.allOnes_and, BitVec.and_comm (0xfffffffffffff : Word) (shldResult 36 a b)]

theorem maskedX_repr (a b c d : Word) (ok : Bool) :
    let xs := maskedX a b c d ok
    FieldRepr xs ⟨limbValue xs % modulus, Nat.mod_lt _ (by decide)⟩ 8 := by
  refine ⟨?_, rfl⟩
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  cases ok
  · rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact Nat.zero_le _
  · rcases hi with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | change (_ &&& (0xfffffffffffff : Word)).toNat ≤ 2 * 8 * (2^52 - 1)
        rw [SquareValue.mask52]
        omega
      | change (a >>> 16).toNat ≤ 2 * 8 * (2^48 - 1)
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        have := a.isLt
        omega

theorem addSeven_repr {u : Limbs} {y : Fin modulus} (h : FieldRepr u y 1) :
    FieldRepr #v[u[0] + 7, u[1], u[2], u[3], u[4]]
      ⟨(y.val + 7) % modulus, Nat.mod_lt _ (by decide)⟩ 8 := by
  have low := h.1 0
  change u[0].toNat ≤ 2 * 1 * (2^52 - 1) at low
  have plus : (u[0] + 7).toNat = u[0].toNat + 7 :=
    BitVec.toNat_add_of_lt (by change u[0].toNat + 7 < 2^64; omega)
  constructor
  · intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · change (u[0] + 7).toNat ≤ 2 * 8 * (2^52 - 1)
      omega
    · exact (h.mono (n := 8) (by decide)).1 1
    · exact (h.mono (n := 8) (by decide)).1 2
    · exact (h.mono (n := 8) (by decide)).1 3
    · exact (h.mono (n := 8) (by decide)).1 4
  · change _ = (y.val + 7) % modulus
    rw [← h.2, Nat.mod_add_mod, SquareValue.limbValue_eq, SquareValue.limbValue_eq]
    change ((u[0] + 7).toNat + u[1].toNat * 2^52 + u[2].toNat * 2^104 +
        u[3].toNat * 2^156 + u[4].toNat * 2^208) % modulus =
      (u[0].toNat + u[1].toNat * 2^52 + u[2].toNat * 2^104 +
        u[3].toNat * 2^156 + u[4].toNat * 2^208 + 7) % modulus
    rw [plus]
    congr 1
    omega

end K256.Proofs.Sec1.Affine.Compressed
