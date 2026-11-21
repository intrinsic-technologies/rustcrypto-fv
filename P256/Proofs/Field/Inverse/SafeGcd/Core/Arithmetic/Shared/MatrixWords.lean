import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.WordArithmetic

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Machine

theorem toInt_eq_of_word_eq {x : Int} {w : BitVec 64}
    (eq : BitVec.ofInt 64 x = w) (bound : x.natAbs < 2^63) : w.toInt = x := by
  rw [← eq]
  have abs := Int.natAbs_eq x
  apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega

theorem matrix_step_words (s : DivState) (u v q r : BitVec 64)
    (bound : (Matrix.step s ⟨u.toInt, v.toInt, q.toInt, r.toInt⟩).Bounded (2^62)) :
    let swap := 0 < s.delta ∧ s.g % 2 ≠ 0
    let uNext := if swap then q+q else u+u
    let vNext := if swap then r+r else v+v
    let qNext := if s.g % 2 = 0 then q else if 0 < s.delta then q-u else q+u
    let rNext := if s.g % 2 = 0 then r else if 0 < s.delta then r-v else r+v
    Matrix.step s ⟨u.toInt, v.toInt, q.toInt, r.toInt⟩ =
      ⟨uNext.toInt, vNext.toInt, qNext.toInt, rNext.toInt⟩ := by
  have double (x : BitVec 64) (h : (2*x.toInt).natAbs < 2^63) :
      2*x.toInt = (x+x).toInt := by
    symm
    apply toInt_eq_of_word_eq _ h
    rw [show (2:Int)*x.toInt=x.toInt+x.toInt by omega, BitVec.ofInt_add,
      BitVec.ofInt_toInt]
  have add (x y : BitVec 64) (h : (x.toInt+y.toInt).natAbs < 2^63) :
      x.toInt+y.toInt = (x+y).toInt := by
    symm
    apply toInt_eq_of_word_eq _ h
    rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  have sub (x y : BitVec 64) (h : (x.toInt-y.toInt).natAbs < 2^63) :
      x.toInt-y.toInt = (x-y).toInt := by
    rw [BitVec.toInt_sub]
    symm
    apply Int.bmod_eq_of_le
    all_goals have abs := Int.natAbs_eq (x.toInt-y.toInt); omega
  dsimp only
  by_cases even : s.g % 2 = 0
  · simp only [Matrix.step, even, ne_eq, not_true_eq_false, and_false, ↓reduceIte,
      Matrix.Bounded] at bound ⊢
    rw [double u (by omega), double v (by omega)]
  · by_cases positive : 0 < s.delta
    · simp only [Matrix.step, even, positive, ne_eq, not_false_eq_true, and_self,
        ↓reduceIte, Matrix.Bounded] at bound ⊢
      rw [double q (by omega), double r (by omega), sub q u (by omega), sub r v (by omega)]
    · simp only [Matrix.step, even, positive, ne_eq, false_and, ↓reduceIte,
        Matrix.Bounded] at bound ⊢
      rw [double u (by omega), double v (by omega), add q u (by omega), add r v (by omega)]

end P256.Proofs.Field.Inverse.SafeGcd.Machine
