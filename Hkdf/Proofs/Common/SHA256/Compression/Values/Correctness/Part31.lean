import Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness.Invariants

import Hkdf.Proofs.Common.SHA256.Compression.Values.ReadSteps

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness

open Hkdf.Proofs.NIST

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part31 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant31 h block s) : invariant32 h block (run context Program.part31 s) := by
  rcases start with ⟨hr0, hr1, hr3, hr5, hr6, hr7, hr8, hr10, hr11, hr13, hr14, hs0, hs4, hs8, hs12, hs16, hs20, hs36, hs40, hs64, hs72, hs88, hs104, hs112, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant32, Program.part31, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr3, hr5, hr6, hr7, hr8, hr10, hr11, hr13, hr14, hs0, hs4, hs8, hs12, hs16, hs20, hs36, hs40, hs64, hs72, hs88, hs104, hs112, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a37, a38, e37, e38, w37]
  generalize (a h block 33) = v0
  generalize (a h block 34) = v1
  generalize (a h block 35) = v2
  generalize (a h block 36) = v3
  generalize (e h block 33) = v4
  generalize (e h block 34) = v5
  generalize (e h block 35) = v6
  generalize (e h block 36) = v7
  generalize (word block 21) = v8
  generalize (word block 22) = v9
  generalize (word block 23) = v10
  generalize (word block 24) = v11
  generalize (word block 25) = v12
  generalize (word block 26) = v13
  generalize (word block 27) = v14
  generalize (word block 28) = v15
  generalize (word block 29) = v16
  generalize (word block 30) = v17
  generalize (word block 31) = v18
  generalize (word block 32) = v19
  generalize (word block 33) = v20
  generalize (word block 34) = v21
  generalize (word block 35) = v22
  generalize (word block 36) = v23
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness
