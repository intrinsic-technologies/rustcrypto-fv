import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part52 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant52 h block s) : invariant53 h block (run context Program.part52 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  have constant72 : context.constants 576 = (NIST.SHA512.roundConstants[72]!).toBitVec := constants 72 (by decide)
  have constant73 : context.constants 584 = (NIST.SHA512.roundConstants[73]!).toBitVec := constants 73 (by decide)
  have constant74 : context.constants 592 = (NIST.SHA512.roundConstants[74]!).toBitVec := constants 74 (by decide)
  have constant75 : context.constants 600 = (NIST.SHA512.roundConstants[75]!).toBitVec := constants 75 (by decide)
  have constant76 : context.constants 608 = (NIST.SHA512.roundConstants[76]!).toBitVec := constants 76 (by decide)
  have constant77 : context.constants 616 = (NIST.SHA512.roundConstants[77]!).toBitVec := constants 77 (by decide)
  have constant78 : context.constants 624 = (NIST.SHA512.roundConstants[78]!).toBitVec := constants 78 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr3, hr5, hr6, hr9, hr10, hr11, hr12, hr14, hr15, hs0, hs8, hs16, hs24, hs32, hs48, hs64, hs72, hs80, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant53, Program.part52, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr2, hr3, hr5, hr6, hr9, hr10, hr11, hr12, hr14, hr15, hs0, hs8, hs16, hs24, hs32, hs48, hs64, hs72, hs80, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352, constant72, constant73, constant74, constant75, constant76, constant77, constant78]
  simp only [rotate, a72, a73, e72, e73, w72, w73, choice_xor, choice_xor_commuted]
  generalize (a h block 68) = va68
  generalize (a h block 69) = va69
  generalize (a h block 70) = va70
  generalize (a h block 71) = va71
  generalize (a h block 72) = va72
  generalize (a h block 73) = va73
  generalize (e h block 68) = ve68
  generalize (e h block 69) = ve69
  generalize (e h block 70) = ve70
  generalize (e h block 71) = ve71
  generalize (e h block 72) = ve72
  generalize (e h block 73) = ve73
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
  generalize (word block 72) = vw72
  generalize (word block 73) = vw73
  generalize (NIST.SHA512.roundConstants[71]!).toBitVec = vk71
  generalize (NIST.SHA512.roundConstants[72]!).toBitVec = vk72
  generalize (NIST.SHA512.roundConstants[73]!).toBitVec = vk73
  generalize (NIST.SHA512.roundConstants[74]!).toBitVec = vk74
  generalize (NIST.SHA512.roundConstants[75]!).toBitVec = vk75
  generalize (NIST.SHA512.roundConstants[76]!).toBitVec = vk76
  generalize (NIST.SHA512.roundConstants[77]!).toBitVec = vk77
  generalize (NIST.SHA512.roundConstants[78]!).toBitVec = vk78
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl
  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
