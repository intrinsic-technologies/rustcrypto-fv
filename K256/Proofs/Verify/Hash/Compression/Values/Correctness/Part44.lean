import K256.Proofs.Verify.Hash.Compression.Values.Correctness.Invariants

import K256.Proofs.Verify.Hash.Compression.Values.ReadSteps

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash.Compression.Values.Correctness

open K256.Proofs.Verify.Hash.Compression

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part44 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant44 h block s) : invariant45 h block (run context Program.part44 s) := by
  rcases start with ⟨hr0, hr3, hr5, hr7, hr8, hr9, hr10, hr11, hr12, hr14, hs0, hs4, hs16, hs20, hs40, hs64, hs72, hs88, hs104, hs112, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant45, Program.part44, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr3, hr5, hr7, hr8, hr9, hr10, hr11, hr12, hr14, hs0, hs4, hs16, hs20, hs40, hs64, hs72, hs88, hs104, hs112, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a53, a54, e53, e54, w53]
  generalize (a h block 49) = v0
  generalize (a h block 50) = v1
  generalize (a h block 51) = v2
  generalize (a h block 52) = v3
  generalize (e h block 49) = v4
  generalize (e h block 50) = v5
  generalize (e h block 51) = v6
  generalize (e h block 52) = v7
  generalize (word block 37) = v8
  generalize (word block 38) = v9
  generalize (word block 39) = v10
  generalize (word block 40) = v11
  generalize (word block 41) = v12
  generalize (word block 42) = v13
  generalize (word block 43) = v14
  generalize (word block 44) = v15
  generalize (word block 45) = v16
  generalize (word block 46) = v17
  generalize (word block 47) = v18
  generalize (word block 48) = v19
  generalize (word block 49) = v20
  generalize (word block 50) = v21
  generalize (word block 51) = v22
  generalize (word block 52) = v23
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end K256.Proofs.Verify.Hash.Compression.Values.Correctness
