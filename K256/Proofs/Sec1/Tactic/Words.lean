import K256.Proofs.Sec1.Tactic.Core

namespace K256.Proofs.Sec1.Tactic

open X86Proofs K256.Proofs.Refine

theorem wordAddr_0 (b : BitVec 64) : wordAddr b 64 0 = b := by simp [wordAddr]

theorem wordAddr_1 (b : BitVec 64) : wordAddr b 64 1 = b + 8 := by simp [wordAddr]

theorem wordAddr_2 (b : BitVec 64) : wordAddr b 64 2 = b + 16 := by simp [wordAddr]

theorem wordAddr_3 (b : BitVec 64) : wordAddr b 64 3 = b + 24 := by simp [wordAddr]

theorem wordAddr_4 (b : BitVec 64) : wordAddr b 64 4 = b + 32 := by simp [wordAddr]

open Lean Meta Elab Tactic in
elab "kernel_refl" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (ty, l, _) := t.consumeMData.eq? | throwError "kernel_refl: not an equation"
  g.assign (mkApp2 (mkConst ``Eq.refl [← getLevel ty]) ty l)
  replaceMainGoal []

macro "words_close" : tactic => `(tactic| (
  intro i hi
  obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  all_goals simp only [K256.Proofs.Sec1.Tactic.wordAddr_0, K256.Proofs.Sec1.Tactic.wordAddr_1,
    K256.Proofs.Sec1.Tactic.wordAddr_2, K256.Proofs.Sec1.Tactic.wordAddr_3,
    K256.Proofs.Sec1.Tactic.wordAddr_4]
  all_goals refine_norm []
  all_goals kernel_refl))

end K256.Proofs.Sec1.Tactic
