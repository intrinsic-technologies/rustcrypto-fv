import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part16 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant16 h block s) : invariant17 h block (run context Program.part16 s) := by
  have constant11 : context.constants 88 = (NIST.SHA512.roundConstants[11]!).toBitVec := constants 11 (by decide)
  rcases start with ⟨hr0, hr1, hr3, hr6, hr7, hr8, hr9, hr10, hr11, hr14, hs0, hs8, hs16, hs24, hs32, hs40, hs48, hs64, hs72, hs88, hs96, hs104, hs112, hs136, hs144, hs168, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant17, Program.part16, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr3, hr6, hr7, hr8, hr9, hr10, hr11, hr14, hs0, hs8, hs16, hs24, hs32, hs40, hs48, hs64, hs72, hs88, hs96, hs104, hs112, hs136, hs144, hs168, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352, constant11]
  simp only [a12, e12, choice_xor, choice_xor_commuted]
  generalize (a h block 10) = va10
  generalize (a h block 11) = va11
  generalize (a h block 12) = va12
  generalize (a h block 8) = va8
  generalize (a h block 9) = va9
  generalize (e h block 10) = ve10
  generalize (e h block 11) = ve11
  generalize (e h block 12) = ve12
  generalize (e h block 8) = ve8
  generalize (e h block 9) = ve9
  generalize (word block 0) = vw0
  generalize (word block 1) = vw1
  generalize (word block 10) = vw10
  generalize (word block 11) = vw11
  generalize (word block 12) = vw12
  generalize (word block 13) = vw13
  generalize (word block 14) = vw14
  generalize (word block 15) = vw15
  generalize (word block 2) = vw2
  generalize (word block 3) = vw3
  generalize (word block 4) = vw4
  generalize (word block 5) = vw5
  generalize (word block 6) = vw6
  generalize (word block 7) = vw7
  generalize (word block 8) = vw8
  generalize (word block 9) = vw9
  generalize (NIST.SHA512.roundConstants[11]!).toBitVec = vk11
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
