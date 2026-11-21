import P256.Proofs.SHA256.Interface
import P256.Proofs.SHA256.Compression.Values.Correctness.Invariants

import P256.Proofs.SHA256.Compression.Values.ReadSteps

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Values.Correctness

open P256.Proofs.Common.SHA256.Compression

open P256.Proofs.SHA256

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part43 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant43 h block s) : invariant44 h block (run context Program.part43 s) := by
  rcases start with ⟨hr1, hr3, hr5, hr6, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hs0, hs4, hs16, hs20, hs40, hs64, hs72, hs80, hs88, hs104, hs112, hs120, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant44, Program.part43, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr1, hr3, hr5, hr6, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hs0, hs4, hs16, hs20, hs40, hs64, hs72, hs80, hs88, hs104, hs112, hs120, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a52, e52, w51, w52]
  generalize (a h block 48) = v0
  generalize (a h block 49) = v1
  generalize (a h block 50) = v2
  generalize (a h block 51) = v3
  generalize (e h block 48) = v4
  generalize (e h block 49) = v5
  generalize (e h block 50) = v6
  generalize (e h block 51) = v7
  generalize (word block 35) = v8
  generalize (word block 36) = v9
  generalize (word block 37) = v10
  generalize (word block 38) = v11
  generalize (word block 39) = v12
  generalize (word block 40) = v13
  generalize (word block 41) = v14
  generalize (word block 42) = v15
  generalize (word block 43) = v16
  generalize (word block 44) = v17
  generalize (word block 45) = v18
  generalize (word block 46) = v19
  generalize (word block 47) = v20
  generalize (word block 48) = v21
  generalize (word block 49) = v22
  generalize (word block 50) = v23
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end P256.Proofs.SHA256.Compression.Values.Correctness
