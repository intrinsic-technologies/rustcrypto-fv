import K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.LowBits

set_option autoImplicit false

namespace K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd

theorem positive_byte (value : BitVec 64) :
    (if (value == 0 || value.msb != false) = false then (1 : BitVec 8) else 0) =
      if 0 < value.toInt then 1 else 0 := by
  by_cases negative : value.msb = true
  · have h := BitVec.toInt_neg_of_msb_true negative
    simp [negative, show ¬ 0 < value.toInt by omega]
  · have nonnegative : value.msb = false := Bool.eq_false_iff.mpr negative
    have h := BitVec.toInt_eq_toNat_of_msb nonnegative
    by_cases zero : value = 0#64
    · simp [zero]
    · have positive : 0 < value.toInt := by
        have nz : value.toNat ≠ 0 := by
          intro hn
          exact zero (BitVec.eq_of_toNat_eq hn)
        omega
      simp [nonnegative, zero, positive]

theorem toInt_mod_two (value : BitVec 64) :
    value.toInt % 2 = (value.toNat % 2 : Nat) := by
  rw [BitVec.toInt_eq_msb_cond]
  split <;> omega

theorem parity_byte (value : BitVec 64) :
    value.setWidth 8 &&& 1 =
      if value.toInt % 2 = 0 then (0 : BitVec 8) else 1 := by
  apply BitVec.eq_of_toNat_eq
  have parity := toInt_mod_two value
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change (value.toNat % 256 &&& 1) = _
  rw [Nat.and_one_is_mod]
  split
  · change value.toNat % 256 % 2 = 0
    omega
  · change value.toNat % 256 % 2 = 1
    omega

theorem swap_byte (delta value : BitVec 64) :
    (if (delta == 0 || delta.msb != false) = false then (1 : BitVec 8) else 0) &&&
        value.setWidth 8 =
      if 0 < delta.toInt ∧ value.toInt % 2 ≠ 0 then 1 else 0 := by
  rw [positive_byte]
  by_cases positive : 0 < delta.toInt
  · rw [ite_eq_left positive, BitVec.and_comm, parity_byte]
    by_cases even : value.toInt % 2 = 0 <;> simp [positive, even]
  · simp [positive]

theorem divstep_values_word (delta f g : BitVec 64)
    (bound : delta.toInt.natAbs ≤ 1183) :
    let state : DivState := ⟨delta.toInt, f.toInt, g.toInt⟩
    let swap := 0 < delta.toInt ∧ g.toInt % 2 ≠ 0
    let nextDelta := if swap then 2 - delta else delta + 2
    let nextF := if swap then g else f
    let numerator := if g.toInt % 2 = 0 then g
      else if 0 < delta.toInt then g - f else g + f
    wordDivstep state = ⟨nextDelta.toInt, nextF.toInt, (numerator.sshiftRight 1).toInt⟩ := by
  have hdelta : -1183 ≤ delta.toInt ∧ delta.toInt ≤ 1183 := by
    have h := Int.natAbs_eq delta.toInt
    omega
  have add : (delta + 2).toInt = delta.toInt + 2 := by
    rw [BitVec.toInt_add]
    change (delta.toInt + 2).bmod (2^64) = delta.toInt + 2
    apply Int.bmod_eq_of_le <;> omega
  have sub : ((2 : BitVec 64) - delta).toInt = 2 - delta.toInt := by
    rw [BitVec.toInt_sub]
    change (2 - delta.toInt).bmod (2^64) = 2 - delta.toInt
    apply Int.bmod_eq_of_le <;> omega
  dsimp only
  by_cases even : g.toInt % 2 = 0
  · simp only [wordDivstep, even, ne_eq, not_true_eq_false, and_false, ↓reduceIte,
      BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, add]
    rfl
  · by_cases positive : 0 < delta.toInt
    · simp only [wordDivstep, even, positive, ne_eq, not_false_eq_true, and_self, ↓reduceIte,
        BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, BitVec.toInt_sub, sub]
      rfl
    · simp only [wordDivstep, even, positive, ne_eq, false_and, ↓reduceIte,
        BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, BitVec.toInt_add, add]
      rfl

end K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd
