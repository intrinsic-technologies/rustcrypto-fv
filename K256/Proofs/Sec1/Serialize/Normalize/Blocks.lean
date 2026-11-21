import K256.Proofs.Sec1.Serialize.Normalize.Layout
import K256.Proofs.Sec1.Tactic
import K256.Proofs.Sec1.LIR.Generated.Values

namespace K256.Proofs.Sec1.Serialize.Normalize

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field Prelude

set_option maxHeartbeats 4000000 in
theorem entry_block (code : CodeMap) : layout.BlockSimulation code .entry := by
  x86_refine [setWidth_mergeGPR8]
  all_goals rfl

set_option maxHeartbeats 4000000 in
theorem resume_block (code : CodeMap) : layout.BlockSimulation code .resume := by
  x86_refine
  all_goals
    intro i hi
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    all_goals simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero]
    all_goals refine_norm []
    all_goals rfl

theorem choice_block (code : CodeMap) : layout.BlockSimulation code .choice := by
  x86_refine
  all_goals exact WordsAt.write_apart ‹_› _ _ (RangeApart.of_diff (by bv_omega))

theorem blocks (code : CodeMap) : ∀ l, layout.BlockSimulation code l
  | .entry => entry_block code
  | .resume => resume_block code
  | .choice => choice_block code

end K256.Proofs.Sec1.Serialize.Normalize
