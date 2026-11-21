import Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness.Invariants

import Hkdf.Proofs.Common.SHA256.Compression.Values.ReadSteps

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness

open Hkdf.Proofs.NIST

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part22 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant22 h block s) : invariant23 h block (run context Program.part22 s) := by
  rcases start with ⟨hr0, hr1, hr2, hr3, hr7, hr8, hr12, hr13, hr14, hr15, hs4, hs8, hs12, hs16, hs20, hs36, hs40, hs56, hs72, hs80, hs100, hs104, hs112, hs120, hs136, hs140, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant23, Program.part22, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr3, hr7, hr8, hr12, hr13, hr14, hr15, hs4, hs8, hs12, hs16, hs20, hs36, hs40, hs56, hs72, hs80, hs100, hs104, hs112, hs120, hs136, hs140, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a27, e27, w26, w27]
  generalize (a h block 23) = v0
  generalize (a h block 24) = v1
  generalize (a h block 25) = v2
  generalize (a h block 26) = v3
  generalize (e h block 23) = v4
  generalize (e h block 24) = v5
  generalize (e h block 25) = v6
  generalize (e h block 26) = v7
  generalize (word block 10) = v8
  generalize (word block 11) = v9
  generalize (word block 12) = v10
  generalize (word block 13) = v11
  generalize (word block 14) = v12
  generalize (word block 15) = v13
  generalize (word block 16) = v14
  generalize (word block 17) = v15
  generalize (word block 18) = v16
  generalize (word block 19) = v17
  generalize (word block 20) = v18
  generalize (word block 21) = v19
  generalize (word block 22) = v20
  generalize (word block 23) = v21
  generalize (word block 24) = v22
  generalize (word block 25) = v23
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness
