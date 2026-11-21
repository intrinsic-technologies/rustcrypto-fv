import Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness.Invariants

import Hkdf.Proofs.Common.SHA256.Compression.Values.ReadSteps

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness

open Hkdf.Proofs.NIST

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part16 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant16 h block s) : invariant17 h block (run context Program.part16 s) := by
  rcases start with ⟨hr0, hr2, hr5, hr6, hr7, hr8, hr9, hr11, hr14, hr15, hs0, hs4, hs8, hs12, hs16, hs20, hs36, hs40, hs52, hs64, hs96, hs100, hs112, hs120, hs136, hs140, hs144, hs148, hs152, hs168, hs172, hs176, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant17, Program.part16, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr2, hr5, hr6, hr7, hr8, hr9, hr11, hr14, hr15, hs0, hs4, hs8, hs12, hs16, hs20, hs36, hs40, hs52, hs64, hs96, hs100, hs112, hs120, hs136, hs140, hs144, hs148, hs152, hs168, hs172, hs176, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a20, e20, w20]
  generalize (a h block 16) = v0
  generalize (a h block 17) = v1
  generalize (a h block 18) = v2
  generalize (a h block 19) = v3
  generalize (e h block 16) = v4
  generalize (e h block 17) = v5
  generalize (e h block 18) = v6
  generalize (e h block 19) = v7
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
  generalize (word block 4) = v18
  generalize (word block 5) = v19
  generalize (word block 6) = v20
  generalize (word block 7) = v21
  generalize (word block 8) = v22
  generalize (word block 9) = v23
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness
