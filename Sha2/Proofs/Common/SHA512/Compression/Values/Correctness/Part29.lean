import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part29 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant29 h block s) : invariant30 h block (run context Program.part29 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  have constant29 : context.constants 232 = (NIST.SHA512.roundConstants[29]!).toBitVec := constants 29 (by decide)
  have constant30 : context.constants 240 = (NIST.SHA512.roundConstants[30]!).toBitVec := constants 30 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr14, hr15, hs0, hs8, hs16, hs24, hs32, hs40, hs56, hs64, hs72, hs96, hs104, hs112, hs136, hs176, hs200, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant30, Program.part29, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr2, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr14, hr15, hs0, hs8, hs16, hs24, hs32, hs40, hs56, hs64, hs72, hs96, hs104, hs112, hs136, hs176, hs200, hs304, hs312, hs320, hs328, hs336, hs344, hs352, constant29, constant30]
  simp only [rotate, a29, a30, e29, e30, w29, w30, choice_xor, choice_xor_commuted]
  generalize (a h block 25) = va25
  generalize (a h block 26) = va26
  generalize (a h block 27) = va27
  generalize (a h block 28) = va28
  generalize (a h block 29) = va29
  generalize (a h block 30) = va30
  generalize (e h block 25) = ve25
  generalize (e h block 26) = ve26
  generalize (e h block 27) = ve27
  generalize (e h block 28) = ve28
  generalize (e h block 29) = ve29
  generalize (e h block 30) = ve30
  generalize (word block 13) = vw13
  generalize (word block 14) = vw14
  generalize (word block 15) = vw15
  generalize (word block 16) = vw16
  generalize (word block 17) = vw17
  generalize (word block 18) = vw18
  generalize (word block 19) = vw19
  generalize (word block 20) = vw20
  generalize (word block 21) = vw21
  generalize (word block 22) = vw22
  generalize (word block 23) = vw23
  generalize (word block 24) = vw24
  generalize (word block 25) = vw25
  generalize (word block 26) = vw26
  generalize (word block 27) = vw27
  generalize (word block 28) = vw28
  generalize (word block 29) = vw29
  generalize (word block 30) = vw30
  generalize (NIST.SHA512.roundConstants[28]!).toBitVec = vk28
  generalize (NIST.SHA512.roundConstants[29]!).toBitVec = vk29
  generalize (NIST.SHA512.roundConstants[30]!).toBitVec = vk30
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
