import P256.Proofs.Verifying.Combination.Naf.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf

def recode : Nat → Nat → Nat → Nat → List Int
  | 0, _, _, _ => []
  | fuel + 1, bits, n, c =>
    if bits = 0 then if c = 0 then [] else [1]
    else
      let window := n % 32 + c
      if window % 2 = 0 then 0 :: recode fuel (bits - 1) (n / 2) c
      else digit window :: (List.replicate (skip bits window - 1) 0 ++
        recode fuel (bits - skip bits window) (n / 2 ^ skip bits window) (carry window))

theorem recode_spec (fuel bits n c : Nat) (hf : bits < fuel) (hn : n < 2 ^ bits)
    (hc : c ≤ 1) :
    value (recode fuel bits n c) = (n : Int) + c ∧
      (∀ d ∈ recode fuel bits n c, ValidDigit d) ∧
      (recode fuel bits n c).length ≤ bits + 1 := by
  induction fuel generalizing bits n c with
  | zero => omega
  | succ fuel ih =>
    by_cases hb : bits = 0
    · subst bits
      have hz : n = 0 := by simpa only [Nat.pow_zero] using Nat.eq_zero_of_le_zero (by omega : n ≤ 0)
      subst n
      have hc' : c = 0 ∨ c = 1 := by omega
      rcases hc' with rfl | rfl <;> simp [recode, value, ValidDigit]
    · have hpos : 0 < bits := by omega
      by_cases he : (n % 32 + c) % 2 = 0
      · obtain ⟨heq, hvalid, hlen⟩ := ih (bits - 1) (n / 2) c (by omega)
          (even_bound hpos hn) hc
        simp only [recode, hb, ite_false, he, ite_true]
        refine ⟨?_, ?_, ?_⟩
        · rw [value_cons, Int.zero_add, heq]
          exact (even_reconstruction hc he).symm
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact Or.inl rfl
          · exact hvalid d hd
        · simp only [List.length_cons]
          omega
      · have ho : (n % 32 + c) % 2 = 1 := by omega
        have bounds := odd_skip_bounds hpos hn hc ho
        obtain ⟨heq, hvalid, hlen⟩ := ih (bits - skip bits (n % 32 + c))
          (n / 2 ^ skip bits (n % 32 + c)) (carry (n % 32 + c)) (by omega)
          (shifted_bound hn bounds.2.1) (carry_le_one _)
        simp only [recode, hb, ite_false, he]
        refine ⟨?_, ?_, ?_⟩
        · rw [value_block (by omega), heq]
          exact (odd_reconstruction hpos hn hc ho).symm
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact digit_valid (by omega) ho
          · rcases List.mem_append.mp hd with hd | hd
            · have hz : d = 0 := (List.mem_replicate.mp hd).2
              exact Or.inl hz
            · exact hvalid d hd
        · simp only [List.length_cons, List.length_append, List.length_replicate]
          omega

def digits (n : Nat) : List Int := recode 257 256 n 0

theorem digits_value (n : Nat) (hn : n < 2 ^ 256) : value (digits n) = n := by
  simpa only [digits, Int.natCast_zero, Int.add_zero] using (recode_spec 257 256 n 0 (by decide) hn (by decide)).1

theorem digits_valid (n : Nat) (hn : n < 2 ^ 256) : ∀ d ∈ digits n, ValidDigit d :=
  (recode_spec 257 256 n 0 (by decide) hn (by decide)).2.1

theorem digits_length (n : Nat) (hn : n < 2 ^ 256) : (digits n).length ≤ 257 :=
  (recode_spec 257 256 n 0 (by decide) hn (by decide)).2.2

theorem recode_fuel_eq (fuel fuel' bits n c : Nat) (hf : bits < fuel)
    (hf' : bits < fuel') (hn : n < 2 ^ bits) (hc : c ≤ 1) :
    recode fuel bits n c = recode fuel' bits n c := by
  induction fuel generalizing fuel' bits n c with
  | zero => omega
  | succ fuel ih =>
    cases fuel' with
    | zero => omega
    | succ fuel' =>
      by_cases hb : bits = 0
      · subst bits
        simp [recode]
      · by_cases he : (n % 32 + c) % 2 = 0
        · simp only [recode, hb, ite_false, he, ite_true]
          congr 1
          exact ih fuel' (bits-1) (n/2) c (by omega) (by omega)
            (even_bound (by omega) hn) hc
        · have bounds := odd_skip_bounds (by omega : 0 < bits) hn hc
            (by omega : (n % 32 + c) % 2 = 1)
          simp only [recode, hb, ite_false, he]
          rw [ih fuel' (bits - skip bits (n % 32 + c))
            (n / 2 ^ skip bits (n % 32 + c)) (carry (n % 32 + c))
            (by omega) (by omega) (shifted_bound hn bounds.2.1) (carry_le_one _)]

theorem recode_even {bits n c : Nat} (hb : 0 < bits) (he : (n % 32 + c) % 2 = 0) :
    recode (bits+1) bits n c = 0 :: recode bits (bits-1) (n/2) c := by
  simp only [recode, Nat.ne_of_gt hb, ite_false, he, ite_true]

theorem recode_odd {bits n c : Nat} (hb : 0 < bits) (hn : n < 2 ^ bits)
    (hc : c ≤ 1) (ho : (n % 32 + c) % 2 = 1) :
    recode (bits+1) bits n c = digit (n % 32 + c) ::
      (List.replicate (skip bits (n % 32 + c)-1) 0 ++
        recode (bits - skip bits (n % 32 + c)+1) (bits - skip bits (n % 32 + c))
          (n / 2 ^ skip bits (n % 32 + c)) (carry (n % 32 + c))) := by
  have bounds := odd_skip_bounds hb hn hc ho
  have ne : (n % 32 + c) % 2 ≠ 0 := by omega
  conv => lhs; rw [recode]
  simp only [Nat.ne_of_gt hb, ite_false, ne]
  rw [recode_fuel_eq bits (bits - skip bits (n % 32 + c)+1)
    (bits - skip bits (n % 32 + c)) (n / 2 ^ skip bits (n % 32 + c))
    (carry (n % 32 + c)) (by omega) (by omega) (shifted_bound hn bounds.2.1)
    (carry_le_one _)]

theorem iterator_index_step {i j : Nat} (hi : i ≤ j) (hj : j ≤ i + 5) :
    j / 64 = i / 64 ∨ j / 64 = i / 64 + 1 := by
  omega

end P256.Proofs.Verifying.Combination.Naf
