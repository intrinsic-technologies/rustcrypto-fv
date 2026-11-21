import K256.Proofs.Verify.Hash.Compression.Values.Correctness.Invariants

import K256.Proofs.Verify.Hash.Compression.Values.ReadSteps

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash.Compression.Values.Correctness

open K256.Proofs.Verify.Hash.Compression

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part50 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant50 h block s) : invariant51 h block (run context Program.part50 s) := by
  rcases start with ⟨hr0, hr1, hr2, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr15, hs40, hs64, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant51, Program.part50, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr15, hs40, hs64, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a62, e62, w61, w62]
  generalize (a h block 58) = v0
  generalize (a h block 59) = v1
  generalize (a h block 60) = v2
  generalize (a h block 61) = v3
  generalize (e h block 58) = v4
  generalize (e h block 59) = v5
  generalize (e h block 60) = v6
  generalize (e h block 61) = v7
  generalize (word block 45) = v8
  generalize (word block 46) = v9
  generalize (word block 47) = v10
  generalize (word block 48) = v11
  generalize (word block 54) = v12
  generalize (word block 55) = v13
  generalize (word block 56) = v14
  generalize (word block 59) = v15
  generalize (word block 60) = v16
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end K256.Proofs.Verify.Hash.Compression.Values.Correctness
