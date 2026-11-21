import K256.Proofs.Sec1.Square.Layout
import K256.Proofs.Sec1.Tactic
import K256.Proofs.Sec1.LIR.Generated.Values

namespace K256.Proofs.Sec1.Square

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude


private theorem wordAddr_0 (b : BitVec 64) : wordAddr b 64 0 = b := by simp [wordAddr]

private theorem wordAddr_1 (b : BitVec 64) : wordAddr b 64 1 = b + 8 := by simp [wordAddr]

private theorem wordAddr_2 (b : BitVec 64) : wordAddr b 64 2 = b + 16 := by simp [wordAddr]

private theorem wordAddr_3 (b : BitVec 64) : wordAddr b 64 3 = b + 24 := by simp [wordAddr]

private theorem wordAddr_4 (b : BitVec 64) : wordAddr b 64 4 = b + 32 := by simp [wordAddr]

set_option maxHeartbeats 4000000 in
theorem entry_block (code : CodeMap) : layout.BlockSimulation code .entry := by
  x86_refine
  intro i hi
  obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  all_goals simp only [wordAddr_0, wordAddr_1, wordAddr_2, wordAddr_3, wordAddr_4]
  all_goals refine_norm []
  all_goals run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    let target ← Lean.instantiateMVars (← g.getType)
    let some (ty, lhs, _) := target.consumeMData.eq? | throwError "expected a limb equality"
    g.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [← Lean.Meta.getLevel ty]) ty lhs)
    Lean.Elab.Tactic.replaceMainGoal []

theorem blocks (code : CodeMap) : ∀ l, layout.BlockSimulation code l
  | .entry => entry_block code

end K256.Proofs.Sec1.Square
