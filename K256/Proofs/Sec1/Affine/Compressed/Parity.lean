import K256.Proofs.Sec1.Serialize.Normalize.Words
import K256.Proofs.Common.Field.SquareValue

namespace K256.Proofs.Sec1.Affine.Compressed

open Common.Field Serialize.Normalize

def negationOffset (i : Fin 5) : Word :=
  if i = 0 then 0x3ffffbfffff0bc else if i = 4 then 0x3fffffffffffc else 0x3ffffffffffffc

def negated (a : Limbs) : Limbs := Vector.ofFn fun i => negationOffset i - a[i.val]

def parityMask (low : Word) (want : BitVec 8) : Word :=
  -BitVec.setWidth 64 ((~~~((low.setWidth 8 &&& 1) ^^^ want)) &&& 1)

def selectRoot (a : Limbs) (want : BitVec 8) : Limbs :=
  Vector.ofFn fun i =>
    let n := (negated a)[i]
    (a[i] ^^^ n) &&& parityMask a[0] want ^^^ n

private theorem lowBit_eq (w : Word) :
    w.setWidth 8 &&& 1 = BitVec.ofNat 8 (w.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  change (w.toNat % 256 &&& (2^1 - 1)) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem selectRoot_eq (a : Limbs) (want : BitVec 8) (h : want = 0 ∨ want = 1) :
    selectRoot a want = if a[0].toNat % 2 = want.toNat then a else negated a := by
  have hbit : a[0].toNat % 2 = 0 ∨ a[0].toNat % 2 = 1 := by omega
  have hm : parityMask a[0] want =
      if a[0].toNat % 2 = want.toNat then BitVec.allOnes 64 else 0 := by
    unfold parityMask
    rw [lowBit_eq]
    rcases h with rfl | rfl <;> rcases hbit with hb | hb <;> rw [hb] <;> decide
  split <;> rename_i he
  · simp only [he, ite_true] at hm
    apply Vector.ext
    intro i hi
    simp only [selectRoot, Vector.getElem_ofFn, hm, BitVec.and_allOnes]
    simp [BitVec.xor_assoc]
  · simp only [he, ite_false] at hm
    apply Vector.ext
    intro i hi
    simp [selectRoot, hm]

private theorem negated_add_limb (a : Limbs) (ha : Widths a) (i : Fin 5) :
    (negated a)[i.val].toNat + a[i.val].toNat = (negationOffset i).toNat := by
  have hi := ha i
  change a[i.val].toNat < _ at hi
  have hb : a[i.val].toNat ≤ (negationOffset i).toNat := by
    apply Nat.le_trans (Nat.le_of_lt hi)
    exact (by decide +kernel : ∀ j : Fin 5, 2^(if j.val = 4 then 48 else 52) ≤ (negationOffset j).toNat) i
  simp only [negated, Vector.getElem_ofFn]
  change (negationOffset i - a[i.val]).toNat + a[i.val].toNat = _
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hb)]
  exact Nat.sub_add_cancel hb

private theorem pairValue (a b : Limbs) :
    limbValue a + limbValue b = (a[0].toNat + b[0].toNat) +
    (a[1].toNat + b[1].toNat) * 2^52 + (a[2].toNat + b[2].toNat) * 2^104 +
    (a[3].toNat + b[3].toNat) * 2^156 + (a[4].toNat + b[4].toNat) * 2^208 := by
  rw [SquareValue.limbValue_eq, SquareValue.limbValue_eq]
  simp (disch := decide) only [getElem!_pos, Nat.add_mul]
  omega

theorem negated_value (a : Limbs) (ha : Widths a) :
    limbValue (negated a) + limbValue a = 4 * modulus := by
  rw [pairValue]
  have h0 : (negated a)[0].toNat + a[0].toNat = (negationOffset 0).toNat := negated_add_limb a ha 0
  have h1 : (negated a)[1].toNat + a[1].toNat = (negationOffset 1).toNat := negated_add_limb a ha 1
  have h2 : (negated a)[2].toNat + a[2].toNat = (negationOffset 2).toNat := negated_add_limb a ha 2
  have h3 : (negated a)[3].toNat + a[3].toNat = (negationOffset 3).toNat := negated_add_limb a ha 3
  have h4 : (negated a)[4].toNat + a[4].toNat = (negationOffset 4).toNat := negated_add_limb a ha 4
  rw [h0, h1, h2, h3, h4]
  decide +kernel

theorem selectRoot_repr (a : Limbs) (ha : Widths a) {root : Nat}
    (hroot : limbValue a = root) (hpos : 0 < root) (hlt : root < modulus)
    (want : BitVec 8) (hwant : want = 0 ∨ want = 1) :
    let y := if root % 2 = want.toNat then root else modulus - root
    FieldRepr (selectRoot a want) ⟨y, by dsimp only [y]; split <;> omega⟩ 2 := by
  have parity : a[0].toNat % 2 = root % 2 := by
    rw [← hroot, SquareValue.limbValue_eq]
    simp (disch := decide) only [getElem!_pos]
    omega
  rw [selectRoot_eq a want hwant, parity]
  dsimp only
  split
  · refine ⟨?_, ?_⟩
    · intro i
      have hi := ha i
      change a[i.val].toNat < _ at hi
      simp (disch := exact i.isLt) only [getElem!_pos]
      change (if i.val < 4 then a[i.val].toNat ≤ 2*2*(2^52-1) else a[i.val].toNat ≤ 2*2*(2^48-1))
      split <;> split at hi <;> omega
    · rw [hroot, Nat.mod_eq_of_lt hlt]
  · refine ⟨?_, ?_⟩
    · intro i
      have hi := negated_add_limb a ha i
      have hb := (by decide +kernel : ∀ j : Fin 5,
        (negationOffset j).toNat ≤ 2 * 2 * (2^(if j.val < 4 then 52 else 48) - 1)) i
      simp (disch := exact i.isLt) only [getElem!_pos]
      change (if i.val < 4 then (negated a)[i.val].toNat ≤ 2*2*(2^52-1) else (negated a)[i.val].toNat ≤ 2*2*(2^48-1))
      split <;> split at hb <;> omega
    · have hv := negated_value a ha
      rw [hroot] at hv
      have e : limbValue (negated a) = (modulus - root) + modulus * 3 := by omega
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

end K256.Proofs.Sec1.Affine.Compressed
