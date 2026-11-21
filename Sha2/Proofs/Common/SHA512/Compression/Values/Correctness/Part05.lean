import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part05 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant05 h block s) : invariant06 h block (run context Program.part05 s) := by
  have constant1 : context.constants 8 = (NIST.SHA512.roundConstants[1]!).toBitVec := constants 1 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr5, hr6, hr8, hr11, hr12, hr14, hr15, hs0, hs8, hs16, hs24, hs32, hs40, hs48, hs64, hs72, hs88, hs96, hs104, hs112, hs136, hs144, hs176, hs328, hs336, hs344, hs352⟩
  simp only [invariant06, Program.part05, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr2, hr5, hr6, hr8, hr11, hr12, hr14, hr15, hs0, hs8, hs16, hs24, hs32, hs40, hs48, hs64, hs72, hs88, hs96, hs104, hs112, hs136, hs144, hs176, hs328, hs336, hs344, hs352, constant1]
  simp only [a02, e02]
  generalize (a h block 1) = va
  generalize (e h block 1) = ve
  generalize (word block 1) = vw
  generalize (NIST.SHA512.roundConstants[1]!).toBitVec = vk
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
