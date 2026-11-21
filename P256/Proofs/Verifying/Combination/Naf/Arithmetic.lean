import Init.Omega
import Init.Data.Int.DivMod.Lemmas
import Init.Data.List.Lemmas
import Init.Data.BitVec.Lemmas

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf

def value (digits : List Int) : Int :=
  digits.foldr (fun digit rest => digit + 2 * rest) 0

def ValidDigit (digit : Int) : Prop :=
  digit = 0 ∨ (digit % 2 = 1 ∧ -15 ≤ digit ∧ digit ≤ 15)

def carry (window : Nat) : Nat := if window < 16 then 0 else 1

def digit (window : Nat) : Int := (window : Int) - 32 * (carry window : Int)

def skip (bits window : Nat) : Nat := min 5 (bits - carry window)

theorem carry_le_one (window : Nat) : carry window ≤ 1 := by
  unfold carry
  split <;> omega

theorem digit_valid {window : Nat} (bound : window ≤ 32) (odd : window % 2 = 1) :
    ValidDigit (digit window) := by
  right
  unfold digit carry
  split <;> omega

theorem even_reconstruction {n c : Nat} (hc : c ≤ 1) (even : (n % 32 + c) % 2 = 0) :
    (n : Int) + c = 2 * ((n / 2 : Nat) + (c : Int)) := by
  omega

theorem even_bound {bits n : Nat} (hb : 0 < bits) (hn : n < 2^bits) :
    n / 2 < 2^(bits-1) := by
  have hb' : bits = bits-1+1 := by omega
  rw [hb', Nat.pow_succ] at hn
  omega

theorem odd_skip_bounds {bits n c : Nat} (hb : 0 < bits) (hn : n < 2^bits)
    (hc : c ≤ 1) (odd : (n % 32 + c) % 2 = 1) :
    1 ≤ skip bits (n % 32 + c) ∧ skip bits (n % 32 + c) ≤ bits ∧
      skip bits (n % 32 + c) ≤ 5 := by
  have hcarry := carry_le_one (n % 32 + c)
  have hsmall : bits = 1 → carry (n % 32 + c) = 0 := by
    intro h
    subst bits
    have hn' : n < 2 := hn
    have hw : n % 32 + c < 16 := by omega
    simp only [carry, ite_eq_left hw]
  unfold skip
  omega

theorem odd_reconstruction {bits n c : Nat} (hb : 0 < bits) (hn : n < 2^bits)
    (hc : c ≤ 1) (odd : (n % 32 + c) % 2 = 1) :
    (n : Int) + c = digit (n % 32 + c) +
      (2 : Int) ^ skip bits (n % 32 + c) *
        ((n / 2^skip bits (n % 32 + c) : Nat) + (carry (n % 32 + c) : Int)) := by
  by_cases hlarge : 6 ≤ bits
  · have hs : skip bits (n % 32 + c) = 5 := by
      have hcarry := carry_le_one (n % 32 + c)
      unfold skip
      omega
    rw [hs]
    unfold digit
    change (n : Int) + c = (n % 32 : Nat) + (c : Int) -
      32 * (carry (n % 32 + c) : Int) +
      32 * ((n / 32 : Nat) + (carry (n % 32 + c) : Int))
    omega
  · have hcases : bits = 1 ∨ bits = 2 ∨ bits = 3 ∨ bits = 4 ∨ bits = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
      unfold digit skip carry <;> split <;> simp only [Nat.reducePow, Nat.reduceSub, Nat.min_def, Nat.reduceLeDiff, ↓reduceIte, Int.reducePow] at * <;> omega

end P256.Proofs.Verifying.Combination.Naf

namespace P256.Proofs.Verifying.Combination.Naf

theorem shifted_bound {bits n shift : Nat} (hn : n < 2^bits) (hs : shift ≤ bits) :
    n / 2^shift < 2^(bits-shift) := by
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift)).mpr
  rw [← Nat.pow_add]
  simpa only [Nat.sub_add_cancel hs] using hn

theorem value_cons (d : Int) (ds : List Int) : value (d :: ds) = d + 2 * value ds := rfl

theorem value_zeroes (k : Nat) (ds : List Int) :
    value (List.replicate k 0 ++ ds) = (2 : Int)^k * value ds := by
  induction k with
  | zero => simp [value]
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, value_cons, ih, Int.zero_add,
      Int.pow_succ, Int.mul_assoc, Int.mul_comm 2]

theorem value_block {k : Nat} (hk : 0 < k) (d : Int) (ds : List Int) :
    value (d :: (List.replicate (k-1) 0 ++ ds)) = d + (2 : Int)^k * value ds := by
  rw [value_cons, value_zeroes]
  have hk' : k = (k-1)+1 := by omega
  rw [hk', Int.pow_succ]
  simp only [Nat.add_sub_cancel, Int.mul_assoc, Int.mul_comm 2]

end P256.Proofs.Verifying.Combination.Naf
