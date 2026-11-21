import Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness.Invariants

import Hkdf.Proofs.Common.SHA256.Compression.Values.ReadSteps

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness

open Hkdf.Proofs.NIST

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part25 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant25 h block s) : invariant26 h block (run context Program.part25 s) := by
  rcases start with ⟨hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr12, hr14, hr15, hs0, hs4, hs8, hs12, hs20, hs56, hs72, hs80, hs88, hs104, hs112, hs120, hs128, hs140, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant26, Program.part25, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr12, hr14, hr15, hs0, hs4, hs8, hs12, hs20, hs56, hs72, hs80, hs88, hs104, hs112, hs120, hs128, hs140, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a30, e30, w30]
  generalize (a h block 26) = v0
  generalize (a h block 27) = v1
  generalize (a h block 28) = v2
  generalize (a h block 29) = v3
  generalize (e h block 26) = v4
  generalize (e h block 27) = v5
  generalize (e h block 28) = v6
  generalize (e h block 29) = v7
  generalize (word block 14) = v8
  generalize (word block 15) = v9
  generalize (word block 16) = v10
  generalize (word block 17) = v11
  generalize (word block 18) = v12
  generalize (word block 19) = v13
  generalize (word block 20) = v14
  generalize (word block 21) = v15
  generalize (word block 22) = v16
  generalize (word block 23) = v17
  generalize (word block 24) = v18
  generalize (word block 25) = v19
  generalize (word block 26) = v20
  generalize (word block 27) = v21
  generalize (word block 28) = v22
  generalize (word block 29) = v23
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness
