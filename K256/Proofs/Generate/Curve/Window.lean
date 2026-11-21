import K256.Proofs.Generate.Curve.Generator

set_option autoImplicit false

namespace K256.Proofs.Generate.Curve

open Standards.SECG.ECC
open Standards.SECG.DomainParameters.Secp256k1

def radixQuotient (x : Nat) : Nat := (x + 8) / 16

def radixDigit (x : Nat) : Int := (x : Int) - 16 * (radixQuotient x : Int)

theorem radixDigit_bounds (x : Nat) : -8 ≤ radixDigit x ∧ radixDigit x ≤ 7 := by
  unfold radixDigit radixQuotient
  omega

def radixCarry (x : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => (x / 16^i % 16 + radixCarry x i + 8) / 16

def radixRemaining (x i : Nat) : Nat := x / 16^i + radixCarry x i

theorem radixRemaining_zero (x : Nat) : radixRemaining x 0 = x := by
  simp [radixRemaining, radixCarry]

theorem radixQuotient_remaining (x i : Nat) :
    radixQuotient (radixRemaining x i) = radixRemaining x (i + 1) := by
  simp only [radixRemaining, radixQuotient, radixCarry, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega

theorem radixDigit_remaining (x i : Nat) :
    radixDigit (radixRemaining x i) =
      ((x / 16^i % 16 + radixCarry x i : Nat) : Int) - 16 * (radixCarry x (i + 1) : Int) := by
  rw [radixDigit, radixQuotient_remaining]
  simp only [radixRemaining, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega

theorem radixCarry_le_one (x i : Nat) : radixCarry x i ≤ 1 := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    rw [radixCarry]
    omega

theorem radixRemaining_top (x width : Nat) (h : x < 16^width) :
    radixRemaining x width = radixCarry x width := by
  simp [radixRemaining, Nat.div_eq_of_lt h]

def tableEntry (p : Curve.Point) : Nat → Curve.Point
  | 0 => .infinity
  | i + 1 => Curve.add domain (tableEntry p i) p

def selectDigit (p : Curve.Point) (d : Int) : Curve.Point :=
  let q := tableEntry p d.natAbs
  if d < 0 then Curve.neg domain q else q

def fourDoubles (p : Curve.Point) : Curve.Point :=
  let twice := fun q => Curve.add domain q q
  twice (twice (twice (twice p)))

def signedWindow (p q : Curve.Point) : Nat → Nat → Nat → Curve.Point
  | 0, x, y => Curve.add domain (selectDigit p x) (selectDigit q y)
  | n + 1, x, y =>
    let acc := signedWindow p q n (radixQuotient x) (radixQuotient y)
    Curve.add domain (Curve.add domain (fourDoubles acc) (selectDigit p (radixDigit x)))
      (selectDigit q (radixDigit y))

private theorem tableEntry_multiple (k : Int) (i : Nat) :
    tableEntry (generatorMultiple k) i = generatorMultiple ((i : Int) * k) := by
  induction i with
  | zero =>
    simp only [tableEntry, Int.natCast_zero, Int.zero_mul]
    decide +kernel
  | succ i ih =>
    simp only [tableEntry, ih, generatorMultiple_add, Int.natCast_succ, Int.add_mul, Int.one_mul]

theorem selectDigit_multiple (k d : Int) :
    selectDigit (generatorMultiple k) d = generatorMultiple (d * k) := by
  simp only [selectDigit, tableEntry_multiple]
  cases d with
  | ofNat n =>
    rw [ite_eq_right (show ¬ Int.ofNat n < 0 from Int.not_lt.mpr (Int.natCast_nonneg n))]
    rfl
  | negSucc n =>
    rw [ite_eq_left (Int.negSucc_lt_zero _), generatorMultiple_neg, ← Int.neg_mul]
    rfl

private theorem fourDoubles_multiple (k : Int) :
    fourDoubles (generatorMultiple k) = generatorMultiple (16 * k) := by
  simp only [fourDoubles, generatorMultiple_add]
  congr 1
  omega

theorem signedWindow_multiple (a b : Int) (width x y : Nat) :
    signedWindow (generatorMultiple a) (generatorMultiple b) width x y =
      generatorMultiple ((x : Int) * a + (y : Int) * b) := by
  induction width generalizing x y with
  | zero => simp only [signedWindow, selectDigit_multiple, generatorMultiple_add]
  | succ n ih =>
    simp only [signedWindow, ih, fourDoubles_multiple, selectDigit_multiple, generatorMultiple_add,
      radixDigit]
    congr 1
    grind only

end K256.Proofs.Generate.Curve
