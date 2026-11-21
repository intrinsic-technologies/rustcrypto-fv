import Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness.Invariants

import Hkdf.Proofs.Common.SHA256.Compression.Values.ReadSteps

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness

open Hkdf.Proofs.NIST

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part47 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant47 h block s) : invariant48 h block (run context Program.part47 s) := by
  rcases start with ⟨hr0, hr1, hr2, hr3, hr5, hr6, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hs0, hs4, hs40, hs64, hs88, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant48, Program.part47, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr3, hr5, hr6, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hs0, hs4, hs40, hs64, hs88, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a57, a58, e57, e58, w57, w58]
  generalize (a h block 53) = v0
  generalize (a h block 54) = v1
  generalize (a h block 55) = v2
  generalize (a h block 56) = v3
  generalize (e h block 53) = v4
  generalize (e h block 54) = v5
  generalize (e h block 55) = v6
  generalize (e h block 56) = v7
  generalize (word block 41) = v8
  generalize (word block 42) = v9
  generalize (word block 43) = v10
  generalize (word block 44) = v11
  generalize (word block 45) = v12
  generalize (word block 46) = v13
  generalize (word block 47) = v14
  generalize (word block 48) = v15
  generalize (word block 50) = v16
  generalize (word block 51) = v17
  generalize (word block 52) = v18
  generalize (word block 53) = v19
  generalize (word block 54) = v20
  generalize (word block 55) = v21
  generalize (word block 56) = v22
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness
