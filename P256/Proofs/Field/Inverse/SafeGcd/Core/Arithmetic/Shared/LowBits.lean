import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Matrix

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Machine

def LowBitsEq (bits : Nat) (left right : DivState) : Prop :=
  left.delta = right.delta ∧
    (2 : Int)^bits ∣ left.f - right.f ∧ (2 : Int)^bits ∣ left.g - right.g

theorem two_pow_dvd_two_pow {a b : Nat} (h : a ≤ b) : (2 : Int)^a ∣ (2 : Int)^b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨2^k, Int.pow_add _ _ _⟩

theorem LowBitsEq.mono {a b : Nat} {left right : DivState}
    (h : LowBitsEq b left right) (bound : a ≤ b) : LowBitsEq a left right :=
  ⟨h.1, Int.dvd_trans (two_pow_dvd_two_pow bound) h.2.1,
    Int.dvd_trans (two_pow_dvd_two_pow bound) h.2.2⟩

theorem LowBitsEq.trans {bits : Nat} {left middle right : DivState}
    (first : LowBitsEq bits left middle) (second : LowBitsEq bits middle right) :
    LowBitsEq bits left right := by
  refine ⟨first.1.trans second.1, ?_, ?_⟩
  · have h := Int.dvd_add first.2.1 second.2.1
    rwa [show left.f - middle.f + (middle.f - right.f) = left.f - right.f by omega] at h
  · have h := Int.dvd_add first.2.2 second.2.2
    rwa [show left.g - middle.g + (middle.g - right.g) = left.g - right.g by omega] at h

theorem LowBitsEq.parity {bits : Nat} {left right : DivState}
    (h : LowBitsEq (bits + 1) left right) : left.g % 2 = right.g % 2 := by
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  apply Int.emod_eq_zero_of_dvd
  exact (h.mono (show 1 ≤ bits + 1 by omega)).2.2

theorem half_congruent {modulus left right : Int}
    (h : 2 * modulus ∣ left - right) : modulus ∣ left / 2 - right / 2 := by
  have even : 2 ∣ left - right := Int.dvd_trans (Int.dvd_mul_right 2 modulus) h
  rw [← Int.sub_ediv_of_dvd_sub even]
  exact Int.dvd_ediv_of_mul_dvd h

theorem divstep_lowBits {bits : Nat} {left right : DivState}
    (h : LowBitsEq (bits + 1) left right) :
    LowBitsEq bits (divstep left) (divstep right) := by
  have parity := h.parity
  have small := h.mono (show bits ≤ bits + 1 by omega)
  have half {a b : Int} (hh : (2 : Int)^(bits + 1) ∣ a - b) :
      (2 : Int)^bits ∣ a / 2 - b / 2 := by
    apply half_congruent
    simpa only [Int.pow_succ, Int.mul_comm] using hh
  by_cases even : right.g % 2 = 0
  · simp only [LowBitsEq, divstep, parity, even, ↓reduceIte]
    exact ⟨congrArg (· + 2) h.1, small.2.1, half h.2.2⟩
  · by_cases positive : 0 < right.delta
    · simp only [LowBitsEq, divstep, parity, even, h.1, positive, ↓reduceIte]
      refine ⟨True.intro, small.2.2, half ?_⟩
      have hh := Int.dvd_sub h.2.2 h.2.1
      rwa [show left.g - right.g - (left.f - right.f) =
        left.g - left.f - (right.g - right.f) by omega] at hh
    · simp only [LowBitsEq, divstep, parity, even, h.1, positive, ↓reduceIte]
      refine ⟨True.intro, small.2.1, half ?_⟩
      have hh := Int.dvd_add h.2.2 h.2.1
      rwa [show left.g - right.g + (left.f - right.f) =
        left.g + left.f - (right.g + right.f) by omega] at hh

theorem matrix_step_lowBits {bits : Nat} {left right : DivState}
    (h : LowBitsEq (bits + 1) left right) (matrix : Matrix) :
    matrix.step left = matrix.step right := by
  simp only [Matrix.step, h.parity, h.1]

def signedLow (magnitude : Nat) (negative : Bool) : Int :=
  if negative then -((magnitude % 2^63 : Nat) : Int) else (magnitude % 2^63 : Nat)

theorem signedLow_congruent (magnitude : Nat) (negative : Bool) :
    (2 : Int)^63 ∣ signedLow magnitude negative -
      (if negative then -(magnitude : Int) else (magnitude : Int)) := by
  have h : (2 : Int)^63 ∣ ((magnitude % 2^63 : Nat) : Int) - (magnitude : Int) := by
    rw [Int.natCast_emod, Int.natCast_pow]
    exact Int.dvd_emod_sub_self
  cases negative
  · exact h
  · change (2 : Int)^63 ∣ -((magnitude % 2^63 : Nat) : Int) - -(magnitude : Int)
    rw [show -((magnitude % 2^63 : Nat) : Int) - -(magnitude : Int) =
      -(((magnitude % 2^63 : Nat) : Int) - (magnitude : Int)) by omega]
    exact Int.dvd_neg.mpr h

def wordDivstep (state : DivState) : DivState :=
  if state.g % 2 = 0 then ⟨state.delta + 2, state.f, state.g / 2⟩
  else if 0 < state.delta then
    ⟨2 - state.delta, state.g, (state.g - state.f).bmod (2^64) / 2⟩
  else ⟨state.delta + 2, state.f, (state.g + state.f).bmod (2^64) / 2⟩

def wordJump : Nat → JumpState → JumpState
  | 0, state => state
  | n + 1, state => wordJump n ⟨wordDivstep state.state, state.matrix.step state.state⟩

theorem bmod_congruent {bits width : Nat} (bound : bits ≤ width) (value : Int) :
    (2 : Int)^bits ∣ value.bmod (2^width) - value := by
  apply Int.dvd_trans (two_pow_dvd_two_pow bound)
  have h := Int.dvd_bmod_sub_self (x := value) (m := 2^width)
  rw [Int.natCast_pow] at h
  exact h

theorem wordDivstep_lowBits {bits : Nat} (bound : bits ≤ 63) (state : DivState) :
    LowBitsEq bits (wordDivstep state) (divstep state) := by
  have half (value : Int) :
      (2 : Int)^bits ∣ value.bmod (2^64) / 2 - value / 2 := by
    apply half_congruent
    have h := bmod_congruent (bits := bits + 1) (width := 64) (by omega) value
    simpa only [Int.pow_succ, Int.mul_comm] using h
  by_cases even : state.g % 2 = 0
  · simp [LowBitsEq, wordDivstep, divstep, even]
  · by_cases positive : 0 < state.delta
    · simp only [LowBitsEq, wordDivstep, divstep, even, positive, ↓reduceIte,
        Int.sub_self, Int.dvd_zero, true_and]
      exact half _
    · simp only [LowBitsEq, wordDivstep, divstep, even, positive, ↓reduceIte,
        Int.sub_self, Int.dvd_zero, true_and]
      exact half _

theorem wordJump_lowBits {count bits : Nat} {left right : JumpState}
    (bound : count + bits ≤ 64)
    (states : LowBitsEq (count + bits) left.state right.state)
    (matrices : left.matrix = right.matrix) :
    LowBitsEq bits (wordJump count left).state (jump count right).state ∧
      (wordJump count left).matrix = (jump count right).matrix := by
  induction count generalizing left right with
  | zero =>
    exact ⟨by simpa only [Nat.zero_add, wordJump, jump] using states, matrices⟩
  | succ count ih =>
    have states' : LowBitsEq (count + bits + 1) left.state right.state := by
      simpa only [Nat.succ_add] using states
    apply ih (by omega)
      ((wordDivstep_lowBits (bits := count + bits) (by omega) left.state).trans
        (divstep_lowBits states'))
    rw [matrices]
    exact matrix_step_lowBits states' _

theorem wordDivstep_delta_bound (state : DivState) :
    (wordDivstep state).delta.natAbs ≤ state.delta.natAbs + 2 := by
  have add := Int.natAbs_add_le state.delta 2
  have sub := Int.natAbs_sub_le 2 state.delta
  change (2 - state.delta).natAbs ≤ 2 + state.delta.natAbs at sub
  simp only [wordDivstep]
  split
  · exact add
  · split
    · simpa only [Nat.add_comm] using sub
    · exact add

end P256.Proofs.Field.Inverse.SafeGcd.Machine
