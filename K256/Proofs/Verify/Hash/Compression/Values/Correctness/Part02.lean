import K256.Proofs.Verify.Hash.Compression.Values.Correctness.Invariants

import K256.Proofs.Verify.Hash.Compression.Values.ReadSteps

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash.Compression.Values.Correctness

open K256.Proofs.Verify.Hash.Compression

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part02 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant02 h block s) : invariant03 h block (run context Program.part02 s) := by
  have input3 : bswap32 (context.inputWords 12) = word block 3 := input 3 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr3, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr15, hs56, hs80, hs104, hs188, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant03, Program.part02, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr3, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr15, hs56, hs80, hs104, hs188, hs240, hs248, hs256, hs264, hs272, hs280, input3]
  try simp only [choice_xor, a03, a04, e03, e04]
  generalize (a h block 1) = v0
  generalize (a h block 2) = v1
  generalize (e h block 1) = v2
  generalize (e h block 2) = v3
  generalize (word block 0) = v4
  generalize (word block 1) = v5
  generalize (word block 2) = v6
  generalize (word block 3) = v7
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end K256.Proofs.Verify.Hash.Compression.Values.Correctness
