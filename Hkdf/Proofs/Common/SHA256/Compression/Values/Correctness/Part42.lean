import Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness.Invariants

import Hkdf.Proofs.Common.SHA256.Compression.Values.ReadSteps

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness

open Hkdf.Proofs.NIST

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part42 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant42 h block s) : invariant43 h block (run context Program.part42 s) := by
  rcases start with ⟨hr0, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hs0, hs4, hs8, hs16, hs20, hs40, hs64, hs72, hs80, hs88, hs104, hs112, hs120, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant43, Program.part42, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hs0, hs4, hs8, hs16, hs20, hs40, hs64, hs72, hs80, hs88, hs104, hs112, hs120, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a50, a51, e50, e51, w50]
  generalize (a h block 46) = v0
  generalize (a h block 47) = v1
  generalize (a h block 48) = v2
  generalize (a h block 49) = v3
  generalize (e h block 46) = v4
  generalize (e h block 47) = v5
  generalize (e h block 48) = v6
  generalize (e h block 49) = v7
  generalize (word block 34) = v8
  generalize (word block 35) = v9
  generalize (word block 36) = v10
  generalize (word block 37) = v11
  generalize (word block 38) = v12
  generalize (word block 39) = v13
  generalize (word block 40) = v14
  generalize (word block 41) = v15
  generalize (word block 42) = v16
  generalize (word block 43) = v17
  generalize (word block 44) = v18
  generalize (word block 45) = v19
  generalize (word block 46) = v20
  generalize (word block 47) = v21
  generalize (word block 48) = v22
  generalize (word block 49) = v23
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness
