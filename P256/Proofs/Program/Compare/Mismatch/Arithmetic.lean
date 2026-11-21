import X86Proofs.Program.Effect

namespace P256.Proofs.Program.Compare.Mismatch

theorem shift_ne_of_low_eq {n m : Nat} {x y : BitVec n}
    (hne : x ≠ y) (heq : x.setWidth m = y.setWidth m) : x >>> m ≠ y >>> m := by
  intro he
  apply hne
  apply BitVec.eq_of_toNat_eq
  have hl := congrArg BitVec.toNat heq
  have hh := congrArg BitVec.toNat he
  simp only [BitVec.toNat_setWidth] at hl
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hh
  calc
    x.toNat = x.toNat % 2 ^ m + 2 ^ m * (x.toNat / 2 ^ m) := (Nat.mod_add_div _ _).symm
    _ = y.toNat % 2 ^ m + 2 ^ m * (y.toNat / 2 ^ m) := by rw [hl, hh]
    _ = y.toNat := Nat.mod_add_div _ _

theorem shifted_half_ne {n : Nat} {x y : BitVec (n + n)}
    (hne : x ≠ y) (heq : x.setWidth n = y.setWidth n) :
    (x >>> n).setWidth n ≠ (y >>> n).setWidth n := by
  intro he
  apply shift_ne_of_low_eq hne heq
  apply BitVec.eq_of_toNat_eq
  have h := congrArg BitVec.toNat he
  have hx : (x >>> n).toNat < 2 ^ n := by
    simpa using BitVec.toNat_ushiftRight_lt x n (by omega)
  have hy : (y >>> n).toNat < 2 ^ n := by
    simpa using BitVec.toNat_ushiftRight_lt y n (by omega)
  simpa only [Nat.add_sub_cancel_left, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using h

theorem byte_sub_ne_zero {x y : BitVec 8} (hne : x ≠ y) :
    x.setWidth 32 - y.setWidth 32 ≠ 0 := by
  intro h
  have he : x.setWidth 32 = y.setWidth 32 := by
    simpa [BitVec.sub_eq_iff_eq_add] using h
  apply hne
  simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32),
    BitVec.setWidth_eq] using congrArg (BitVec.setWidth 8) he

end P256.Proofs.Program.Compare.Mismatch
