import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part21 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (start : invariant21 h block s) : invariant22 h block (run context Program.part21 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  rcases start with ⟨hr0, hr5, hr6, hr8, hr9, hr10, hr11, hr14, hr15, hs0, hs8, hs16, hs24, hs32, hs40, hs48, hs64, hs72, hs88, hs96, hs104, hs112, hs128, hs168, hs176, hs216, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant22, Program.part21, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr5, hr6, hr8, hr9, hr10, hr11, hr14, hr15, hs0, hs8, hs16, hs24, hs32, hs40, hs48, hs64, hs72, hs88, hs96, hs104, hs112, hs128, hs168, hs176, hs216, hs304, hs312, hs320, hs328, hs336, hs344, hs352]
  simp only [rotate, a18, e18, choice_xor, choice_xor_commuted]
  generalize (a h block 14) = va14
  generalize (a h block 15) = va15
  generalize (a h block 16) = va16
  generalize (a h block 17) = va17
  generalize (a h block 18) = va18
  generalize (e h block 14) = ve14
  generalize (e h block 15) = ve15
  generalize (e h block 16) = ve16
  generalize (e h block 17) = ve17
  generalize (e h block 18) = ve18
  generalize (word block 10) = vw10
  generalize (word block 11) = vw11
  generalize (word block 12) = vw12
  generalize (word block 13) = vw13
  generalize (word block 14) = vw14
  generalize (word block 15) = vw15
  generalize (word block 16) = vw16
  generalize (word block 17) = vw17
  generalize (word block 2) = vw2
  generalize (word block 3) = vw3
  generalize (word block 4) = vw4
  generalize (word block 5) = vw5
  generalize (word block 6) = vw6
  generalize (word block 7) = vw7
  generalize (word block 8) = vw8
  generalize (word block 9) = vw9
  generalize (NIST.SHA512.roundConstants[17]!).toBitVec = vk17
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
