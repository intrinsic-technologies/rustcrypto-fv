import K256.Proofs.Verify.Hash.Compression.Values.Correctness.Invariants

import K256.Proofs.Verify.Hash.Compression.Values.ReadSteps

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash.Compression.Values.Correctness

open K256.Proofs.Verify.Hash.Compression

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part39 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant39 h block s) : invariant40 h block (run context Program.part39 s) := by
  rcases start with ⟨hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr9, hr10, hr11, hr12, hr13, hr15, hs4, hs8, hs12, hs16, hs20, hs40, hs56, hs64, hs72, hs80, hs88, hs104, hs112, hs120, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant40, Program.part39, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr9, hr10, hr11, hr12, hr13, hr15, hs4, hs8, hs12, hs16, hs20, hs40, hs56, hs64, hs72, hs80, hs88, hs104, hs112, hs120, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a47, e47, w46]
  generalize (a h block 43) = v0
  generalize (a h block 44) = v1
  generalize (a h block 45) = v2
  generalize (a h block 46) = v3
  generalize (e h block 43) = v4
  generalize (e h block 44) = v5
  generalize (e h block 45) = v6
  generalize (e h block 46) = v7
  generalize (word block 30) = v8
  generalize (word block 31) = v9
  generalize (word block 32) = v10
  generalize (word block 33) = v11
  generalize (word block 34) = v12
  generalize (word block 35) = v13
  generalize (word block 36) = v14
  generalize (word block 37) = v15
  generalize (word block 38) = v16
  generalize (word block 39) = v17
  generalize (word block 40) = v18
  generalize (word block 41) = v19
  generalize (word block 42) = v20
  generalize (word block 43) = v21
  generalize (word block 44) = v22
  generalize (word block 45) = v23
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end K256.Proofs.Verify.Hash.Compression.Values.Correctness
