import Std

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.ProjectiveRadix

def nibble (d i : Nat) : Nat := d / 16 ^ i % 16

def carry (d : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => (nibble d i + carry d i + 8) / 16

def centeredDigit (d i : Nat) : Int :=
  (nibble d i : Int) + carry d i - 16 * carry d (i + 1)

def digitInt (d i : Nat) : Int :=
  if i < 64 then centeredDigit d i else carry d 64

def digitByte (d i : Nat) : BitVec 8 := BitVec.ofInt 8 (digitInt d i)

theorem nibble_lt (d i : Nat) : nibble d i < 16 := Nat.mod_lt _ (by decide)

theorem carry_le_one (d i : Nat) : carry d i ≤ 1 := by
  induction i with
  | zero => exact Nat.zero_le 1
  | succ i ih =>
    have hn := nibble_lt d i
    rw [carry]
    omega

theorem centeredDigit_bounds (d i : Nat) :
    -8 ≤ centeredDigit d i ∧ centeredDigit d i < 8 := by
  have hn := nibble_lt d i
  have hc := carry_le_one d i
  unfold centeredDigit
  rw [carry]
  omega

theorem digitInt_bounds (d i : Nat) : -8 ≤ digitInt d i ∧ digitInt d i ≤ 8 := by
  unfold digitInt
  split
  · have h := centeredDigit_bounds d i
    omega
  · have h := carry_le_one d 64
    omega

theorem digitInt_last (d : Nat) : digitInt d 64 = carry d 64 := by
  simp [digitInt]

theorem digitByte_toInt (d i : Nat) : (digitByte d i).toInt = digitInt d i := by
  have h := digitInt_bounds d i
  apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega

theorem nibble_quotient (d i : Nat) :
    nibble d i + 16 * (d / 16 ^ (i + 1)) = d / 16 ^ i := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.mod_add_div _ _

end P256.Proofs.Projective.Multiply.ProjectiveRadix
