import K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.Convergence
import K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.DivstepBounds
import K256.Proofs.Generate.Curve.OrderPrime
import K256.Proofs.Common.Arithmetic.CubicNonzero.Fermat

namespace K256.Proofs.Verify.Core.Scalars.Inverse

open Generate.Generator.Affine.Invert.SafeGcd
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

def model (s rounds : Nat) : DivState := divsteps rounds ⟨1, domain.n, s⟩

theorem modelFits {s : Nat} (bound : s < domain.n) (rounds : Nat) :
    (model s rounds).f.natAbs < 2^256 ∧ (model s rounds).g.natAbs < 2^256 := by
  have h := divsteps_natAbs_le rounds (s := ⟨1, domain.n, s⟩) (limit := domain.n)
    (Nat.le_refl _) (Nat.le_of_lt bound)
  have small : domain.n < 2^256 := by decide +kernel
  exact ⟨Nat.lt_of_le_of_lt h.1 small, Nat.lt_of_le_of_lt h.2 small⟩

theorem coefficient_update {s f g d e u v fNext dNext : Int} (shift : Nat)
    (hd : (d * s) % domain.n = f % domain.n) (he : (e * s) % domain.n = g % domain.n)
    (row : u * f + v * g = (2 : Int)^shift * fNext)
    (correction : ((2 : Int)^shift * dNext) % domain.n = (d * u + e * v) % domain.n) :
    (dNext * s) % domain.n = fNext % domain.n := by
  have eq : ((2 : Int)^shift * (dNext * s)) % domain.n =
      ((2 : Int)^shift * fNext) % domain.n := by
    rw [← Int.mul_assoc, Int.mul_emod _ s, correction, ← Int.mul_emod,
      Int.add_mul, Int.mul_comm d u, Int.mul_comm e v, Int.mul_assoc, Int.mul_assoc,
      Int.add_emod, Int.mul_emod u, Int.mul_emod v, hd, he,
      ← Int.mul_emod, ← Int.mul_emod, ← Int.add_emod, row]
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero,
    ← Int.mul_sub, ← Int.dvd_gcd_mul_iff_dvd_mul] at eq
  have coprime : domain.n.Coprime (2^shift) :=
    Nat.Coprime.pow_right shift (by decide +kernel : domain.n.Coprime 2)
  have gcd : Int.gcd domain.n ((2 : Int)^shift) = 1 := by
    exact_mod_cast coprime
  rw [gcd, Int.natCast_one, Int.one_mul, Int.dvd_iff_emod_eq_zero,
    ← Int.emod_eq_emod_iff_emod_sub_eq_zero] at eq
  exact eq

theorem converges {s : Nat} (bound : s < domain.n) : (model s 591).g = 0 := by
  apply Contraction.divsteps_terminate 591 (show (domain.n : Int) % 2 = 1 by decide +kernel)
    (t := (111 / 100) * ((domain.n : Int) : Rat))
  · apply Contraction.Region.positive 0
    simp only [Rat.pow_zero, Rat.one_mul]
    apply Contraction.positive_initial
    · exact Rat.intCast_nonneg.mpr (by omega)
    · exact Rat.intCast_le_intCast.mpr (by omega)
  · change Contraction.Budget 1 ((111 / 100) * ((domain.n : Int) : Rat))
    unfold Contraction.Budget
    decide +kernel
  · decide +kernel

theorem unit_at_exit {s rounds : Nat} (positive : 0 < s) (bound : s < domain.n)
    (exit : rounds = 591 ∨ (model s rounds).g = 0) : (model s rounds).f.natAbs = 1 := by
  have zero : (model s rounds).g = 0 := exit.elim (fun h => h ▸ converges bound) id
  rw [model, divsteps_terminal_natAbs rounds (show (domain.n : Int) % 2 = 1 by decide +kernel) zero,
    Int.gcd_natCast_natCast, Nat.gcd_comm]
  exact Generate.Curve.order_prime.coprime_of_lt positive bound

theorem coefficient_at_exit {s rounds : Nat} {d : Int} (positive : 0 < s) (bound : s < domain.n)
    (exit : rounds = 591 ∨ (model s rounds).g = 0)
    (relation : (d * (s : Int)) % domain.n = (model s rounds).f % domain.n) :
    ((if (model s rounds).f < 0 then -d else d) % (domain.n : Int)).toNat =
      Curve.inverse domain.n s := by
  let f := (model s rounds).f
  let result := if f < 0 then -d else d
  have unit : f.natAbs = 1 := unit_at_exit positive bound exit
  have one : (1 : Int) % domain.n = 1 := by decide +kernel
  change (d * (s : Int)) % domain.n = f % domain.n at relation
  have mul : (result * (s : Int)) % domain.n = 1 := by
    dsimp only [result]
    split
    · rename_i neg
      have := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt neg)
      have eq : f = -1 := by omega
      have h := (Int.emod_sub_cancel_left (m := d * (s : Int)) (n := (domain.n : Int))
        (k := f) 0).mpr relation
      simpa only [Int.zero_sub, eq, Int.neg_neg, Int.neg_mul, one] using h
    · rename_i nonneg
      have := Int.natAbs_of_nonneg (Int.not_lt.mp nonneg)
      have eq : f = 1 := by omega
      rwa [eq, one] at relation
  have orderPos : 0 < domain.n := by decide +kernel
  have resultNonneg := Int.emod_nonneg result (by omega : (domain.n : Int) ≠ 0)
  have resultBound := Int.emod_lt_of_pos result (by omega : 0 < (domain.n : Int))
  have product : ((result % domain.n).toNat * s) % domain.n = 1 := by
    have cast := Int.toNat_of_nonneg resultNonneg
    have h : (((result % domain.n).toNat : Int) * (s : Int)) % domain.n = 1 := by
      rw [cast, Int.mul_emod, Int.emod_emod, ← Int.mul_emod, mul]
    exact_mod_cast h
  have coprime := Generate.Curve.order_prime.coprime_of_lt positive bound
  change (result % domain.n).toNat = Curve.inverse domain.n s
  rw [Curve.inverse, Common.Field.PowMod.powMod_eq_pow_mod]
  apply Common.Arithmetic.CubicNonzero.coprime_mul_mod_injective coprime (by omega)
    (Nat.mod_lt _ orderPos)
  rw [Nat.mul_comm s, product, Nat.mul_mod_mod, Nat.mul_comm, ← Nat.pow_succ]
  have pred : (domain.n - 2).succ = domain.n - 1 := by decide +kernel
  rw [pred, Common.Arithmetic.CubicNonzero.pow_pred_prime_mod _ _ Generate.Curve.order_prime coprime]

end K256.Proofs.Verify.Core.Scalars.Inverse
