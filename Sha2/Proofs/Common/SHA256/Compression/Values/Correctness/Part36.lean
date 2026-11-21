import Sha2.Proofs.Common.SHA256.Compression.Values.Correctness.Invariants

import Sha2.Proofs.Common.SHA256.Compression.Values.ReadSteps

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Values.Correctness

open Sha2.Proofs.NIST

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part36 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant36 h block s) : invariant37 h block (run context Program.part36 s) := by
  rcases start with ⟨hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr13, hr15, hs4, hs8, hs12, hs20, hs36, hs40, hs64, hs72, hs80, hs88, hs104, hs112, hs120, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant37, Program.part36, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr13, hr15, hs4, hs8, hs12, hs20, hs36, hs40, hs64, hs72, hs80, hs88, hs104, hs112, hs120, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a43, e43, w43]
  generalize (a h block 39) = v0
  generalize (a h block 40) = v1
  generalize (a h block 41) = v2
  generalize (a h block 42) = v3
  generalize (e h block 39) = v4
  generalize (e h block 40) = v5
  generalize (e h block 41) = v6
  generalize (e h block 42) = v7
  generalize (word block 27) = v8
  generalize (word block 28) = v9
  generalize (word block 29) = v10
  generalize (word block 30) = v11
  generalize (word block 31) = v12
  generalize (word block 32) = v13
  generalize (word block 33) = v14
  generalize (word block 34) = v15
  generalize (word block 35) = v16
  generalize (word block 36) = v17
  generalize (word block 37) = v18
  generalize (word block 38) = v19
  generalize (word block 39) = v20
  generalize (word block 40) = v21
  generalize (word block 41) = v22
  generalize (word block 42) = v23
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end Sha2.Proofs.Common.SHA256.Compression.Values.Correctness
