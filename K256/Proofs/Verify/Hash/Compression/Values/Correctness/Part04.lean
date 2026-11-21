import K256.Proofs.Verify.Hash.Compression.Values.Correctness.Invariants

import K256.Proofs.Verify.Hash.Compression.Values.ReadSteps

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash.Compression.Values.Correctness

open K256.Proofs.Verify.Hash.Compression

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part04 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant04 h block s) : invariant05 h block (run context Program.part04 s) := by
  have input6 : bswap32 (context.inputWords 24) = word block 6 := input 6 (by decide)
  have input7 : bswap32 (context.inputWords 28) = word block 7 := input 7 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hs36, hs56, hs64, hs72, hs80, hs104, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant05, Program.part04, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hs36, hs56, hs64, hs72, hs80, hs104, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280, input6, input7]
  try simp only [choice_xor, a06, a07, e06, e07]
  generalize (a h block 2) = v0
  generalize (a h block 3) = v1
  generalize (a h block 4) = v2
  generalize (a h block 5) = v3
  generalize (e h block 2) = v4
  generalize (e h block 3) = v5
  generalize (e h block 4) = v6
  generalize (e h block 5) = v7
  generalize (word block 0) = v8
  generalize (word block 1) = v9
  generalize (word block 2) = v10
  generalize (word block 3) = v11
  generalize (word block 4) = v12
  generalize (word block 5) = v13
  generalize (word block 6) = v14
  generalize (word block 7) = v15
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end K256.Proofs.Verify.Hash.Compression.Values.Correctness
