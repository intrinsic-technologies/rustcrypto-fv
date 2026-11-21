import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part03 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant03 h block s) : invariant04 h block (run context Program.part03 s) := by
  have constant0 : context.constants 0 = (NIST.SHA512.roundConstants[0]!).toBitVec := constants 0 (by decide)
  rcases start with ⟨hr0, hr1, hr3, hr5, hr8, hr10, hr11, hr12, hr13, hr14, hr15, hs0, hs8, hs16, hs24, hs32, hs40, hs48, hs64, hs72, hs88, hs96, hs104, hs136, hs144, hs176, hs328, hs336, hs344, hs352⟩
  simp only [invariant04, Program.part03, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr3, hr5, hr8, hr10, hr11, hr12, hr13, hr14, hr15, hs0, hs8, hs16, hs24, hs32, hs40, hs48, hs64, hs72, hs88, hs96, hs104, hs136, hs144, hs176, hs328, hs336, hs344, hs352, constant0]
  simp only [a01, e01]
  generalize (word block 0) = vw
  generalize (NIST.SHA512.roundConstants[0]!).toBitVec = vk
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
