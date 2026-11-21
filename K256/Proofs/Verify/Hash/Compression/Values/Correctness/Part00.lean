import K256.Proofs.Verify.Hash.Compression.Values.Correctness.Invariants

import K256.Proofs.Verify.Hash.Compression.Values.ReadSteps

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash.Compression.Values.Correctness

open K256.Proofs.Verify.Hash.Compression

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part00 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant00 h block s) : invariant01 h block (run context Program.part00 s) := by
  have input0 : bswap32 (context.inputWords 0) = word block 0 := input 0 (by decide)
  have input1 : bswap32 (context.inputWords 4) = word block 1 := input 1 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr3, hr8, hr9, hr10, hr14⟩
  simp only [invariant01, Program.part00, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr3, hr8, hr9, hr10, hr14, input0, input1]
  try simp only [choice_xor, a01, e01]
  generalize (word block 0) = v0
  generalize (word block 1) = v1
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end K256.Proofs.Verify.Hash.Compression.Values.Correctness
