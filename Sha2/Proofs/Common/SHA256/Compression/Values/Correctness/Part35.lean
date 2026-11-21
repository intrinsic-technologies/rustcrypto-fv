import Sha2.Proofs.Common.SHA256.Compression.Values.Correctness.Invariants

import Sha2.Proofs.Common.SHA256.Compression.Values.ReadSteps

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Values.Correctness

open Sha2.Proofs.NIST

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part35 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant35 h block s) : invariant36 h block (run context Program.part35 s) := by
  rcases start with ⟨hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hs4, hs8, hs12, hs20, hs36, hs40, hs64, hs72, hs80, hs88, hs112, hs120, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant36, Program.part35, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hs4, hs8, hs12, hs20, hs36, hs40, hs64, hs72, hs80, hs88, hs112, hs120, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a42, e42, w42]
  generalize (a h block 38) = v0
  generalize (a h block 39) = v1
  generalize (a h block 40) = v2
  generalize (a h block 41) = v3
  generalize (e h block 38) = v4
  generalize (e h block 39) = v5
  generalize (e h block 40) = v6
  generalize (e h block 41) = v7
  generalize (word block 26) = v8
  generalize (word block 27) = v9
  generalize (word block 28) = v10
  generalize (word block 29) = v11
  generalize (word block 30) = v12
  generalize (word block 31) = v13
  generalize (word block 32) = v14
  generalize (word block 33) = v15
  generalize (word block 34) = v16
  generalize (word block 35) = v17
  generalize (word block 36) = v18
  generalize (word block 37) = v19
  generalize (word block 38) = v20
  generalize (word block 39) = v21
  generalize (word block 40) = v22
  generalize (word block 41) = v23
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end Sha2.Proofs.Common.SHA256.Compression.Values.Correctness
