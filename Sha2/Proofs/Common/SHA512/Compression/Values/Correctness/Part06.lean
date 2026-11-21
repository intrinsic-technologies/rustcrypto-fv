import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part06 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant06 h block s) : invariant06And h block (run context Program.part06 s) := by
  have constant2 : context.constants 16 = (NIST.SHA512.roundConstants[2]!).toBitVec := constants 2 (by decide)
  rcases start with ⟨hr0, hr1, hr3, hr5, hr8, hr11, hr12, hr15, hs0, hs8, hs16, hs24, hs32, hs40, hs48, hs64, hs72, hs88, hs96, hs104, hs112, hs136, hs144, hs176, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant06And, Program.part06, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr3, hr5, hr8, hr11, hr12, hr15, hs0, hs8, hs16, hs24, hs32, hs40, hs48, hs64, hs72, hs88, hs96, hs104, hs112, hs136, hs144, hs176, hs312, hs320, hs328, hs336, hs344, hs352, constant2]

  generalize (word block 2) = vw
  generalize (e h block 2) = ve2
  generalize (e h block 1) = ve1
  generalize (NIST.SHA512.roundConstants[2]!).toBitVec = vk
  change vw + h.f + (0 : BitVec 64) + vk + (ve2 &&& ve1) = vw + h.f + vk + (ve2 &&& ve1)
  exact congrArg (fun x : BitVec 64 => x + vk + (ve2 &&& ve1)) (BitVec.add_zero (vw + h.f))

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
