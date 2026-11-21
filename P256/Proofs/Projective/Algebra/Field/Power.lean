import Standards.SECG.ECC.Curve
import Init.Data.Range.Lemmas
import Init.Data.Nat.Bitwise.Lemmas

set_option autoImplicit false

namespace P256.Proofs.Projective.Algebra.FieldArithmetic

open Standards.SECG.ECC.Curve

theorem powMod_lt (modulus base exponent : Nat) (hmodulus : 0 < modulus) :
    powMod modulus base exponent < modulus := by
  unfold powMod
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Id.run,
    ← apply_ite, List.forIn_pure_yield_eq_foldl]
  apply List.foldlRecOn (motive := fun state : Nat × Nat => state.1 < modulus)
  · exact Nat.mod_lt _ hmodulus
  · intro state hstate i _
    split
    · exact Nat.mod_lt _ hmodulus
    · exact hstate

theorem powMod_eq_pow_mod (modulus base exponent : Nat) :
    powMod modulus base exponent = base ^ exponent % modulus := by
  let step := fun (state : Nat × Nat) (i : Nat) =>
    if exponent.testBit i then
      (state.1 * state.2 % modulus, state.2 * state.2 % modulus)
    else (state.1, state.2 * state.2 % modulus)
  have hprefix (n : Nat) :
      (List.range n).foldl step (1 % modulus, base % modulus) =
        (base ^ (exponent % 2 ^ n) % modulus, base ^ (2 ^ n) % modulus) := by
    induction n with
    | zero => simp [List.range_zero, Nat.mod_one]
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      dsimp only [step]
      have hbit := Nat.toNat_testBit exponent n
      cases h : exponent.testBit n
      · simp only [Bool.false_eq_true, ite_false]
        apply Prod.ext
        · rw [Nat.mod_pow_succ, ← hbit, h]
          simp
        · simp only [Nat.pow_succ, Nat.mul_two, Nat.pow_add, ← Nat.mul_mod]
      · simp only [ite_true]
        apply Prod.ext
        · rw [Nat.mod_pow_succ, ← hbit, h]
          simp only [Bool.toNat_true, Nat.mul_one, Nat.pow_add, ← Nat.mul_mod]
        · simp only [Nat.pow_succ, Nat.mul_two, Nat.pow_add, ← Nat.mul_mod]
  unfold powMod
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Id.run,
    ← apply_ite, List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  change ((List.range (exponent.log2 + 1)).foldl step
    (1 % modulus, base % modulus)).1 = _
  rw [hprefix, Nat.mod_eq_of_lt Nat.lt_log2_self]

end P256.Proofs.Projective.Algebra.FieldArithmetic
