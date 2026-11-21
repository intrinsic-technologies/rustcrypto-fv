import Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness.Invariants

import Hkdf.Proofs.Common.SHA256.Compression.Values.ReadSteps

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness

open Hkdf.Proofs.NIST

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part49 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant49 h block s) : invariant50 h block (run context Program.part49 s) := by
  rcases start with ⟨hr0, hr1, hr2, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr13, hr15, hs0, hs4, hs40, hs64, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant50, Program.part49, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr13, hr15, hs0, hs4, hs40, hs64, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a60, a61, e60, e61, w60]
  generalize (a h block 56) = v0
  generalize (a h block 57) = v1
  generalize (a h block 58) = v2
  generalize (a h block 59) = v3
  generalize (e h block 56) = v4
  generalize (e h block 57) = v5
  generalize (e h block 58) = v6
  generalize (e h block 59) = v7
  generalize (word block 44) = v8
  generalize (word block 45) = v9
  generalize (word block 46) = v10
  generalize (word block 47) = v11
  generalize (word block 48) = v12
  generalize (word block 53) = v13
  generalize (word block 54) = v14
  generalize (word block 55) = v15
  generalize (word block 56) = v16
  generalize (word block 58) = v17
  generalize (word block 59) = v18
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness
