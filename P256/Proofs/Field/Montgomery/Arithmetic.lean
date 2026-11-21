import P256.Spec.Operations
import Init.Data.Nat.Mod

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery

abbrev p : Nat := P256.Spec.Operations.domain.p

abbrev wordBase : Nat := 2 ^ 64

def reduceStep (a : Nat) : Nat := (a + (a % wordBase) * p) / wordBase

def reduceFour (a : Nat) : Nat := reduceStep (reduceStep (reduceStep (reduceStep a)))

theorem p_pos : 0 < p := by decide +kernel

theorem p_lt_radix : p < 2 ^ 256 := by decide +kernel

theorem reduceStep_eq (a : Nat) :
    reduceStep a = a / wordBase + (a % wordBase) * ((p + 1) / wordBase) := by
  dsimp [reduceStep, wordBase, p, P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain]
  omega

theorem reduceStep_mul (a : Nat) :
    reduceStep a * wordBase = a + (a % wordBase) * p := by
  rw [reduceStep_eq]
  dsimp [wordBase, p, P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain]
  omega

theorem reduceStep_mod (a : Nat) : (reduceStep a * wordBase) % p = a % p := by
  rw [reduceStep_mul, Nat.add_mul_mod_self_right]

theorem reduceStep_mul_mod (a b : Nat) :
    reduceStep a * (wordBase * b) % p = a * b % p := by
  have h := congrArg (fun n => n * b % p) (reduceStep_mod a)
  simpa only [Nat.mod_mul_mod, Nat.mul_assoc] using h

theorem reduceStep_mul_pow_mod (a n : Nat) :
    reduceStep a * wordBase ^ (n + 1) % p = a * wordBase ^ n % p := by
  rw [Nat.pow_succ, Nat.mul_comm (wordBase ^ n) wordBase]
  exact reduceStep_mul_mod a (wordBase ^ n)

theorem reduceFour_mod (a : Nat) : reduceFour a * 2 ^ 256 % p = a % p := by
  rw [show 2 ^ 256 = wordBase ^ 4 by decide +kernel]
  unfold reduceFour
  rw [reduceStep_mul_pow_mod, reduceStep_mul_pow_mod,
    reduceStep_mul_pow_mod, reduceStep_mul_pow_mod]
  simp only [Nat.pow_zero, Nat.mul_one]

theorem reduceFour_lt_two_mul_p (a : Nat) (ha : a < p * 2 ^ 256) :
    reduceFour a < 2 * p := by
  have h0 := reduceStep_mul a
  have h1 := reduceStep_mul (reduceStep a)
  have h2 := reduceStep_mul (reduceStep (reduceStep a))
  have h3 := reduceStep_mul (reduceStep (reduceStep (reduceStep a)))
  have hm0 : a % wordBase < wordBase := Nat.mod_lt _ (by decide +kernel)
  have hm1 : reduceStep a % wordBase < wordBase := Nat.mod_lt _ (by decide +kernel)
  have hm2 : reduceStep (reduceStep a) % wordBase < wordBase :=
    Nat.mod_lt _ (by decide +kernel)
  have hm3 : reduceStep (reduceStep (reduceStep a)) % wordBase < wordBase :=
    Nat.mod_lt _ (by decide +kernel)
  change reduceStep (reduceStep (reduceStep (reduceStep a))) < 2 * p
  dsimp only [wordBase, p, P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at *
  omega

def subtractP (a : Nat) : Nat := if a < p then a else a - p

theorem subtractP_eq_mod (a : Nat) (ha : a < 2 * p) : subtractP a = a % p := by
  unfold subtractP
  split
  · exact (Nat.mod_eq_of_lt ‹a < p›).symm
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

abbrev radixInverse : Nat := ((p + 1) / wordBase) ^ 4 % p

theorem radix_mul_inverse : 2 ^ 256 * radixInverse % p = 1 := by
  decide +kernel

theorem reduceFour_eq_mod (a : Nat) : reduceFour a % p = a * radixInverse % p := by
  have h := congrArg (fun n => n * radixInverse % p) (reduceFour_mod a)
  simpa only [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod _ (2 ^ 256 * radixInverse),
    radix_mul_inverse, Nat.mul_one, Nat.mod_mod] using h

theorem subtractP_reduceFour (a : Nat) (ha : a < p * 2 ^ 256) :
    subtractP (reduceFour a) = a * radixInverse % p := by
  rw [subtractP_eq_mod _ (reduceFour_lt_two_mul_p a ha), reduceFour_eq_mod]

theorem montgomery_mul_mod (a b : Nat) :
    ((a * 2 ^ 256 % p) * (b * 2 ^ 256 % p)) * radixInverse % p =
      a * b * 2 ^ 256 % p := by
  rw [← Nat.mod_mul_mod ((a * 2 ^ 256 % p) * (b * 2 ^ 256 % p)) radixInverse p,
    Nat.mod_mul_mod (a * 2 ^ 256) (b * 2 ^ 256 % p) p,
    Nat.mul_mod_mod (a * 2 ^ 256) (b * 2 ^ 256) p, Nat.mod_mul_mod]
  have h : a * 2 ^ 256 * (b * 2 ^ 256) * radixInverse =
      (a * b * 2 ^ 256) * (2 ^ 256 * radixInverse) := by ac_rfl
  rw [h, Nat.mul_mod, radix_mul_inverse, Nat.mul_one, Nat.mod_mod]

theorem subtractP_reduceFour_montgomery_mul (a b : Nat) :
    subtractP (reduceFour ((a * 2 ^ 256 % p) * (b * 2 ^ 256 % p))) =
      a * b * 2 ^ 256 % p := by
  have h : (a * 2 ^ 256 % p) * (b * 2 ^ 256 % p) < p * 2 ^ 256 :=
    Nat.mul_lt_mul_of_lt_of_lt (Nat.mod_lt _ p_pos) (Nat.lt_trans (Nat.mod_lt _ p_pos) p_lt_radix)
  rw [subtractP_reduceFour _ h, montgomery_mul_mod]

theorem reduceStep_add_wordMultiple (a b : Nat) :
    reduceStep (a + wordBase * b) = reduceStep a + b := by
  simp only [reduceStep_eq, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (show 0 < wordBase by decide +kernel)]
  omega

theorem reduceStep_limbs_sparse (a0 a1 a2 a3 : Nat) (h0 : a0 < wordBase) :
    reduceStep (a0 + wordBase * (a1 + wordBase * (a2 + wordBase * a3))) =
      a1 + a0 * 2^32 + wordBase * a2 +
        wordBase^2 * (a3 + a0 * 0xffffffff00000001) := by
  rw [reduceStep_eq]
  dsimp only [wordBase, p, P256.Spec.Operations.domain,
    Standards.NIST.EllipticCurves.P256.domain] at *
  omega

end P256.Proofs.Field.Montgomery
