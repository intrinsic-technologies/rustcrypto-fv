import K256.Proofs.Sec1.Serialize.Normalize.Words
import K256.Proofs.Common.Field.SquareValue

namespace K256.Proofs.Sec1.Serialize.Normalize

open K256.Proofs.Common.Field

private theorem blend_eq (x y mask : Word) :
    (x ^^^ y) &&& mask ^^^ (y &&& mask) = x &&& mask := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, BitVec.toNat_and, Nat.and_xor_distrib_right, Nat.xor_assoc,
    Nat.xor_self, Nat.xor_zero]

private theorem masked_add_toNat (t a : Word) :
    (t >>> 52 + (a &&& mask52)).toNat = t.toNat / 2^52 + a.toNat % 2^52 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, mask52,
    SquareValue.mask52]
  apply Nat.mod_eq_of_lt
  have := t.isLt
  omega

private theorem top_add_toNat (t e : Word) (he : e.toNat < 2^49) :
    ((t >>> 52 + e) &&& mask48).toNat = (t.toNat / 2^52 + e.toNat) % 2^48 := by
  rw [BitVec.and_comm, mask48, SquareValue.mask48']
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have ht := t.isLt
  rw [Nat.mod_eq_of_lt (by omega : t.toNat / 2^52 + e.toNat < 2^64)]

private theorem selected_widths (a b c d e : Word) (he : e.toNat < 2^48) :
    Widths #v[a &&& mask52, b &&& mask52, c &&& mask52, d &&& mask52, e] := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    simp only [Fin.ext_iff]
    omega
  have hmask (x : Word) : (x &&& mask52).toNat < 2^52 := by
    rw [mask52, SquareValue.mask52]
    exact Nat.mod_lt _ (by decide)
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact hmask a
  · exact hmask b
  · exact hmask c
  · exact hmask d
  · exact he

private theorem selected_value (a b c d e : Word) :
    limbValue #v[a &&& mask52, b &&& mask52, c &&& mask52, d &&& mask52, e] =
      foldedValue a b c d e := by
  rw [SquareValue.limbValue_eq]
  change (a &&& mask52).toNat + (b &&& mask52).toNat * 2^52 +
      (c &&& mask52).toNat * 2^104 + (d &&& mask52).toNat * 2^156 +
        e.toNat * 2^208 = _
  simp only [mask52, SquareValue.mask52, foldedValue]
  omega

theorem normOf_correct (a b c d e : Word) (h : foldedValue a b c d e < 2*modulus) :
    let r : Word := if modulus ≤ foldedValue a b c d e then 1 else 0
    let out := normOf r a b c d e
    Widths out ∧ limbValue out = foldedValue a b c d e % modulus := by
  dsimp only
  by_cases hp : modulus ≤ foldedValue a b c d e
  · rw [ite_eq_left hp]
    let s0 : Word := 0x1000003d1 + (a &&& mask52)
    let s1 : Word := (s0 >>> 52) + (b &&& mask52)
    let s2 : Word := (s1 >>> 52) + (c &&& mask52)
    let s3 : Word := (s2 >>> 52) + (d &&& mask52)
    let s4 : Word := ((s3 >>> 52) + e) &&& mask48
    have hout : normOf 1 a b c d e =
        #v[s0 &&& mask52, s1 &&& mask52, s2 &&& mask52, s3 &&& mask52, s4] := by
      have hm : -BitVec.setWidth 64 (BitVec.setWidth 8 (1 : Word)) = BitVec.allOnes 64 := by
        decide +kernel
      simp only [normOf, hm, BitVec.and_allOnes, blend_eq,
        BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      rfl
    rw [hout, selected_value]
    have he : e.toNat < 2^49 := by
      rw [show modulus = 2^256 - 4294968273 by decide +kernel, foldedValue] at h
      omega
    have hs4 : s4.toNat = (s3.toNat / 2^52 + e.toNat) % 2^48 :=
      top_add_toNat s3 e he
    refine ⟨selected_widths _ _ _ _ _ (hs4 ▸ Nat.mod_lt _ (by decide)), ?_⟩
    have hs0 : s0.toNat = 4294968273 + a.toNat % 2^52 := by
      simp only [s0, BitVec.toNat_add, mask52, SquareValue.mask52]
      change (4294968273 + a.toNat % 2^52) % 2^64 = _
      omega
    have hs1 : s1.toNat = s0.toNat / 2^52 + b.toNat % 2^52 := masked_add_toNat s0 b
    have hs2 : s2.toNat = s1.toNat / 2^52 + c.toNat % 2^52 := masked_add_toNat s1 c
    have hs3 : s3.toNat = s2.toNat / 2^52 + d.toNat % 2^52 := masked_add_toNat s2 d
    have hmod := Nat.mod_eq_sub_mod hp
    rw [Nat.mod_eq_of_lt (by omega : foldedValue a b c d e - modulus < modulus)] at hmod
    rw [hmod]
    have hcarry : foldedValue s0 s1 s2 s3 s4 +
        (s3.toNat / 2^52 + e.toNat) / 2^48 * 2^256 =
        foldedValue a b c d e + 4294968273 := by
      unfold foldedValue
      omega
    rw [show modulus = 2^256 - 4294968273 by decide +kernel] at hp h ⊢
    have hfit : foldedValue s0 s1 s2 s3 s4 < 2^256 := by
      unfold foldedValue
      omega
    omega
  · rw [ite_eq_right hp]
    have hout : normOf 0 a b c d e =
        #v[a &&& mask52, b &&& mask52, c &&& mask52, d &&& mask52, e] := by
      have hm : -BitVec.setWidth 64 (BitVec.setWidth 8 (0 : Word)) = 0#64 := by
        decide +kernel
      simp only [normOf, hm, BitVec.and_zero, BitVec.zero_xor]
    rw [hout, selected_value, Nat.mod_eq_of_lt (Nat.lt_of_not_ge hp)]
    apply And.intro
    · apply selected_widths
      rw [show modulus = 2^256 - 4294968273 by decide +kernel, foldedValue] at hp
      omega
    · rfl

end K256.Proofs.Sec1.Serialize.Normalize
