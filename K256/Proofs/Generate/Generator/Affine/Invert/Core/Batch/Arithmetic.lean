import K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.Coefficient
import K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.DivstepBounds
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.State

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open SafeGcd.Batch (Words)

theorem deltaBound (n : Nat) (s : SafeGcd.DivState) :
    (SafeGcd.divsteps n s).delta.natAbs ≤ s.delta.natAbs + 2*n := by
  induction n generalizing s with
  | zero => simp [SafeGcd.divsteps]
  | succ n ih =>
    have ha := Int.natAbs_add_le s.delta 2
    have hs := Int.natAbs_sub_le 2 s.delta
    have step : (SafeGcd.divstep s).delta.natAbs ≤ s.delta.natAbs + 2 := by
      simp only [SafeGcd.divstep]
      split
      · exact ha
      · split
        · exact Nat.le_trans hs (by simp [Nat.add_comm])
        · exact ha
    simpa only [SafeGcd.divsteps] using
      (show (SafeGcd.divsteps n (SafeGcd.divstep s)).delta.natAbs ≤ s.delta.natAbs + 2*(n+1)
       from by have := ih (SafeGcd.divstep s); omega)

theorem modelFits (z : Fin modulus) (n : Nat) :
    (Core.model z n).f.natAbs < 2^256 ∧ (Core.model z n).g.natAbs < 2^256 := by
  have h := SafeGcd.divsteps_natAbs_le n (s := ⟨1, modulus, z.val⟩) (limit := modulus)
    (Nat.le_refl _) (Nat.le_of_lt z.isLt)
  have lt : modulus < 2^256 := by decide +kernel
  exact ⟨Nat.lt_of_le_of_lt h.1 lt, Nat.lt_of_le_of_lt h.2 lt⟩

theorem rowBound {d e : Int} {u v : Word} {shift : Nat}
    (hd : d.natAbs < modulus) (he : e.natAbs < modulus)
    (bound : u.toInt.natAbs + v.toInt.natAbs ≤ 2^shift) :
    (d*u.toInt + e*v.toInt).natAbs < 2^shift * modulus := by
  rw [Int.mul_comm d, Int.mul_comm e]
  exact SafeGcd.linearCombination_natAbs_lt hd he bound (Nat.two_pow_pos _)

theorem rowInvariant {z : Fin modulus} {f g d e f' d' : Int} {u v : Word} {shift : Nat}
    (hd : (d*z.val) % modulus = f % modulus) (he : (e*z.val) % modulus = g % modulus)
    (rep : u.toInt*f + v.toInt*g = (2:Int)^shift * f')
    (congruent : ((2:Int)^shift * d') % modulus = (d*u.toInt + e*v.toInt) % modulus) :
    (d' * z.val) % modulus = f' % modulus := by
  rw [Int.mul_comm d, Int.mul_comm e] at congruent
  exact (by simpa only [Int.mul_one] using
    (SafeGcd.coefficient_update (scale := 1) shift
      (by simpa only [Int.mul_one] using hd) (by simpa only [Int.mul_one] using he)
      rep.symm congruent))

end K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
