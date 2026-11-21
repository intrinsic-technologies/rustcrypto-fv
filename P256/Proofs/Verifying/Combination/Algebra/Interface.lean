import P256.Proofs.Verifying.Combination.Algebra.Accumulator

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Algebra

open Standards.SECG.ECC
open P256.Spec.Operations (domain)
open P256.Proofs.Projective P256.Proofs.Projective.Multiply.Group
open Table (oddTable oddTableEntry)
open Lean.Grind

theorem pairDigits_values (xs ys : List Int) :
    firstValue (pairDigits xs ys) = Naf.value xs ∧
      secondValue (pairDigits xs ys) = Naf.value ys ∧
      (pairDigits xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [pairDigits, firstValue, secondValue, Naf.value]
    | cons y ys ih =>
      rw [pairDigits]
      change 0 + 2 * firstValue (pairDigits [] ys) = 0 ∧
        y + 2 * secondValue (pairDigits [] ys) = y + 2 * Naf.value ys ∧ _
      rw [ih.1, ih.2.1, List.length_cons, ih.2.2]
      simp [Naf.value]
  | cons x xs ih =>
    cases ys with
    | nil =>
      obtain ⟨h1, h2, hlen⟩ := ih []
      rw [pairDigits]
      change x + 2 * firstValue (pairDigits xs []) = x + 2 * Naf.value xs ∧
        0 + 2 * secondValue (pairDigits xs []) = 0 ∧ _
      rw [h1, h2, List.length_cons, hlen]
      simp [Naf.value]
    | cons y ys =>
      obtain ⟨h1, h2, hlen⟩ := ih ys
      rw [pairDigits]
      change x + 2 * firstValue (pairDigits xs ys) = x + 2 * Naf.value xs ∧
        y + 2 * secondValue (pairDigits xs ys) = y + 2 * Naf.value ys ∧ _
      rw [h1, h2, List.length_cons, hlen, List.length_cons, List.length_cons]
      exact ⟨rfl, rfl, by omega⟩

theorem digitValid_of_validDigit {d : Int} (h : Naf.ValidDigit d) : DigitValid d := by
  rcases h with hzero | ⟨hodd, hlo, hhi⟩
  · exact Or.inl hzero
  · right
    cases d <;> omega

theorem pairDigits_valid (xs ys : List Int)
    (hx : ∀ d ∈ xs, Naf.ValidDigit d) (hy : ∀ d ∈ ys, Naf.ValidDigit d) :
    digitsValid (pairDigits xs ys) := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => intro pair h; simp only [pairDigits, List.not_mem_nil] at h
    | cons y ys ih =>
      intro pair h
      simp only [pairDigits] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨Or.inl rfl, digitValid_of_validDigit (hy y (by simp))⟩
      · exact ih (fun d hd => hy d (List.mem_cons_of_mem _ hd)) pair h
  | cons x xs ih =>
    cases ys with
    | nil =>
      intro pair h
      simp only [pairDigits] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨digitValid_of_validDigit (hx x (by simp)), Or.inl rfl⟩
      · exact ih [] (fun d hd => hx d (List.mem_cons_of_mem _ hd)) hy pair h
    | cons y ys =>
      intro pair h
      simp only [pairDigits] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨digitValid_of_validDigit (hx x (by simp)),
          digitValid_of_validDigit (hy y (by simp))⟩
      · exact ih ys (fun d hd => hx d (List.mem_cons_of_mem _ hd))
          (fun d hd => hy d (List.mem_cons_of_mem _ hd)) pair h

theorem linearCombination_valid (p q : Projective) (hp : p.valid) (hq : q.valid)
    (u v : Nat) (hu : u < 2 ^ 256) (hv : v < 2 ^ 256) :
    (linearCombination p q u v).valid :=
  accumulator_valid p q hp hq _
    (pairDigits_valid _ _ (Naf.digits_valid u hu) (Naf.digits_valid v hv))

theorem linearCombination_toAffine (p q : Projective) (hp : p.valid) (hq : q.valid)
    (u v : Nat) (hu : u < 2 ^ 256) (hv : v < 2 ^ 256) :
    (linearCombination p q u v).toAffine =
      P256.Spec.Points.add (P256.Spec.Points.mul u p.toAffine)
        (P256.Spec.Points.mul v q.toAffine) := by
  apply accumulator_toAffine p q hp hq _
    (pairDigits_valid _ _ (Naf.digits_valid u hu) (Naf.digits_valid v hv)) u v
  · exact (pairDigits_values _ _).1.trans (Naf.digits_value u hu)
  · exact (pairDigits_values _ _).2.1.trans (Naf.digits_value v hv)

theorem identity_double : identity.double = identity := by decide +kernel

end P256.Proofs.Verifying.Combination.Algebra
