import K256.Proofs.Verify.Hash.Compression.Values.Correctness.Invariants

import K256.Proofs.Verify.Hash.Compression.Values.ReadSteps

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash.Compression.Values.Correctness

open K256.Proofs.Verify.Hash.Compression

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part10 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant10 h block s) : invariant11 h block (run context Program.part10 s) := by
  rcases start with ⟨hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr9, hr11, hr13, hr14, hr15, hs0, hs8, hs12, hs16, hs20, hs36, hs40, hs52, hs56, hs64, hs72, hs80, hs96, hs104, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant11, Program.part10, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr9, hr11, hr13, hr14, hr15, hs0, hs8, hs12, hs16, hs20, hs36, hs40, hs52, hs56, hs64, hs72, hs80, hs96, hs104, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a16, e16, w16]
  generalize (a h block 12) = v0
  generalize (a h block 13) = v1
  generalize (a h block 14) = v2
  generalize (a h block 15) = v3
  generalize (e h block 12) = v4
  generalize (e h block 13) = v5
  generalize (e h block 14) = v6
  generalize (e h block 15) = v7
  generalize (word block 0) = v8
  generalize (word block 1) = v9
  generalize (word block 10) = v10
  generalize (word block 11) = v11
  generalize (word block 12) = v12
  generalize (word block 13) = v13
  generalize (word block 14) = v14
  generalize (word block 15) = v15
  generalize (word block 2) = v16
  generalize (word block 3) = v17
  generalize (word block 4) = v18
  generalize (word block 5) = v19
  generalize (word block 6) = v20
  generalize (word block 7) = v21
  generalize (word block 8) = v22
  generalize (word block 9) = v23
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end K256.Proofs.Verify.Hash.Compression.Values.Correctness
