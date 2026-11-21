import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part51 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant51 h block s) : invariant52 h block (run context Program.part51 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  have constant70 : context.constants 560 = (NIST.SHA512.roundConstants[70]!).toBitVec := constants 70 (by decide)
  have constant71 : context.constants 568 = (NIST.SHA512.roundConstants[71]!).toBitVec := constants 71 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr6, hr7, hr8, hr9, hr11, hr12, hr13, hr14, hr15, hs0, hs8, hs16, hs24, hs32, hs48, hs56, hs64, hs72, hs80, hs144, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant52, Program.part51, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr2, hr6, hr7, hr8, hr9, hr11, hr12, hr13, hr14, hr15, hs0, hs8, hs16, hs24, hs32, hs48, hs56, hs64, hs72, hs80, hs144, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352, constant70, constant71]
  simp only [rotate, a70, a71, e70, e71, w70, w71, choice_xor, choice_xor_commuted]
  generalize (a h block 66) = va66
  generalize (a h block 67) = va67
  generalize (a h block 68) = va68
  generalize (a h block 69) = va69
  generalize (a h block 70) = va70
  generalize (a h block 71) = va71
  generalize (e h block 66) = ve66
  generalize (e h block 67) = ve67
  generalize (e h block 68) = ve68
  generalize (e h block 69) = ve69
  generalize (e h block 70) = ve70
  generalize (e h block 71) = ve71
  generalize (word block 54) = vw54
  generalize (word block 55) = vw55
  generalize (word block 56) = vw56
  generalize (word block 57) = vw57
  generalize (word block 58) = vw58
  generalize (word block 59) = vw59
  generalize (word block 60) = vw60
  generalize (word block 61) = vw61
  generalize (word block 62) = vw62
  generalize (word block 63) = vw63
  generalize (word block 64) = vw64
  generalize (word block 65) = vw65
  generalize (word block 66) = vw66
  generalize (word block 67) = vw67
  generalize (word block 68) = vw68
  generalize (word block 69) = vw69
  generalize (word block 70) = vw70
  generalize (word block 71) = vw71
  generalize (NIST.SHA512.roundConstants[69]!).toBitVec = vk69
  generalize (NIST.SHA512.roundConstants[70]!).toBitVec = vk70
  generalize (NIST.SHA512.roundConstants[71]!).toBitVec = vk71
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl
  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
