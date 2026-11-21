import K256.Proofs.Verify.Hash.Compression.Values.Correctness.Invariants

import K256.Proofs.Verify.Hash.Compression.Values.ReadSteps

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash.Compression.Values.Correctness

open K256.Proofs.Verify.Hash.Compression

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part32 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant32 h block s) : invariant33 h block (run context Program.part32 s) := by
  rcases start with ⟨hr0, hr1, hr2, hr3, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hs0, hs4, hs8, hs12, hs16, hs20, hs36, hs40, hs64, hs72, hs80, hs88, hs112, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant33, Program.part32, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr3, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hs0, hs4, hs8, hs12, hs16, hs20, hs36, hs40, hs64, hs72, hs80, hs88, hs112, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a39, e39, w38]
  generalize (a h block 35) = v0
  generalize (a h block 36) = v1
  generalize (a h block 37) = v2
  generalize (a h block 38) = v3
  generalize (e h block 35) = v4
  generalize (e h block 36) = v5
  generalize (e h block 37) = v6
  generalize (e h block 38) = v7
  generalize (word block 22) = v8
  generalize (word block 23) = v9
  generalize (word block 24) = v10
  generalize (word block 25) = v11
  generalize (word block 26) = v12
  generalize (word block 27) = v13
  generalize (word block 28) = v14
  generalize (word block 29) = v15
  generalize (word block 30) = v16
  generalize (word block 31) = v17
  generalize (word block 32) = v18
  generalize (word block 33) = v19
  generalize (word block 34) = v20
  generalize (word block 35) = v21
  generalize (word block 36) = v22
  generalize (word block 37) = v23
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end K256.Proofs.Verify.Hash.Compression.Values.Correctness
