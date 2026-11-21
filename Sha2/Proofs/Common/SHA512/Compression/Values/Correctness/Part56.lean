import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part56 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (start : invariant56 h block s) : invariant57 h block (run context Program.part56 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  rcases start with ⟨hr0, hr1, hr3, hr8, hr9, hr10, hr11, hr13, hr14, hs320, hs336, hs352⟩
  simp only [invariant57, Program.part56, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr3, hr8, hr9, hr10, hr11, hr13, hr14, hs320, hs336, hs352]
  simp only [rotate, a80, e80, w79, choice_xor, choice_xor_commuted]
  generalize (a h block 76) = va76
  generalize (a h block 77) = va77
  generalize (a h block 78) = va78
  generalize (a h block 79) = va79
  generalize (a h block 80) = va80
  generalize (e h block 76) = ve76
  generalize (e h block 77) = ve77
  generalize (e h block 78) = ve78
  generalize (e h block 79) = ve79
  generalize (e h block 80) = ve80
  generalize (word block 63) = vw63
  generalize (word block 64) = vw64
  generalize (word block 72) = vw72
  generalize (word block 77) = vw77
  generalize (NIST.SHA512.roundConstants[79]!).toBitVec = vk79
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl
  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
