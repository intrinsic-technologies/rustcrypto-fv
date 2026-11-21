import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part55 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (start : invariant55 h block s) : invariant56 h block (run context Program.part55 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  rcases start with ⟨hr0, hr2, hr3, hr5, hr7, hr8, hr9, hr12, hr13, hr14, hr15, hs24, hs32, hs48, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant56, Program.part55, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr2, hr3, hr5, hr7, hr8, hr9, hr12, hr13, hr14, hr15, hs24, hs32, hs48, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352]
  simp only [rotate, a78, a79, e78, e79, w78, choice_xor, choice_xor_commuted]
  generalize (a h block 74) = va74
  generalize (a h block 75) = va75
  generalize (a h block 76) = va76
  generalize (a h block 77) = va77
  generalize (a h block 78) = va78
  generalize (a h block 79) = va79
  generalize (e h block 74) = ve74
  generalize (e h block 75) = ve75
  generalize (e h block 76) = ve76
  generalize (e h block 77) = ve77
  generalize (e h block 78) = ve78
  generalize (e h block 79) = ve79
  generalize (word block 62) = vw62
  generalize (word block 63) = vw63
  generalize (word block 64) = vw64
  generalize (word block 71) = vw71
  generalize (word block 72) = vw72
  generalize (word block 76) = vw76
  generalize (word block 77) = vw77
  generalize (NIST.SHA512.roundConstants[77]!).toBitVec = vk77
  generalize (NIST.SHA512.roundConstants[78]!).toBitVec = vk78
  generalize (NIST.SHA512.roundConstants[79]!).toBitVec = vk79
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl
  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
