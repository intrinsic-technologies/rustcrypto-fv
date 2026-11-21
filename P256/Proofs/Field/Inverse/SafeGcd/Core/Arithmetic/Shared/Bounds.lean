import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.MatrixWords
namespace P256.Proofs.Field.Inverse.SafeGcd
theorem divstep_natAbs_le {s : DivState} {limit : Nat}
    (hf : s.f.natAbs ≤ limit) (hg : s.g.natAbs ≤ limit) :
    (divstep s).f.natAbs ≤ limit ∧ (divstep s).g.natAbs ≤ limit := by
  simp only [divstep]
  split
  · constructor
    · exact hf
    · dsimp only; omega
  · split
    · constructor
      · exact hg
      · dsimp only; omega
    · constructor
      · exact hf
      · dsimp only; omega

theorem divsteps_natAbs_le (n : Nat) {s : DivState} {limit : Nat}
    (hf : s.f.natAbs ≤ limit) (hg : s.g.natAbs ≤ limit) :
    (divsteps n s).f.natAbs ≤ limit ∧ (divsteps n s).g.natAbs ≤ limit := by
  induction n generalizing s with
  | zero => exact ⟨hf, hg⟩
  | succ n ih =>
    have bounds := divstep_natAbs_le hf hg
    exact ih bounds.1 bounds.2

theorem linearCombination_natAbs_lt {f g u v : Int} {limit bound : Nat}
    (hf : f.natAbs < limit) (hg : g.natAbs < limit)
    (huv : u.natAbs + v.natAbs ≤ bound) (positive : 0 < bound) :
    (u*f+v*g).natAbs < bound*limit := by
  have estimate := linearCombination_natAbs_le
    (limit := limit-1) (bound := bound) (by omega : f.natAbs ≤ limit-1)
    (by omega : g.natAbs ≤ limit-1) huv
  have strict : bound * (limit-1) < bound * limit := Nat.mul_lt_mul_of_pos_left (by omega) positive
  exact Nat.lt_of_le_of_lt estimate strict

namespace Machine
theorem divsteps_delta_natAbs_le (rounds : Nat) (state : DivState) :
    (divsteps rounds state).delta.natAbs≤state.delta.natAbs+2*rounds := by
  have step (s : DivState) : (divstep s).delta.natAbs≤s.delta.natAbs+2 := by
    have same : (divstep s).delta=(wordDivstep s).delta := by
      simp only [divstep,wordDivstep]
      split
      · rfl
      · split <;> rfl
    rw [same]
    exact wordDivstep_delta_bound s
  induction rounds generalizing state with
  | zero => simp [divsteps]
  | succ n ih =>
    have h := ih (divstep state)
    have hs := step state
    change (divsteps n (divstep state)).delta.natAbs≤_
    omega

end Machine
end P256.Proofs.Field.Inverse.SafeGcd
