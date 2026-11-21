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
theorem part29 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant29 h block s) : invariant30 h block (run context Program.part29 s) := by
  rcases start with ⟨hr0, hr1, hr2, hr5, hr6, hr8, hr9, hr10, hr11, hr12, hr13, hr15, hs0, hs4, hs16, hs20, hs36, hs40, hs64, hs72, hs80, hs88, hs104, hs112, hs120, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant30, Program.part29, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr5, hr6, hr8, hr9, hr10, hr11, hr12, hr13, hr15, hs0, hs4, hs16, hs20, hs36, hs40, hs64, hs72, hs80, hs88, hs104, hs112, hs120, hs128, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, choice_xor_commuted, a35, e35, w35]
  generalize (a h block 31) = v0
  generalize (a h block 32) = v1
  generalize (a h block 33) = v2
  generalize (a h block 34) = v3
  generalize (e h block 31) = v4
  generalize (e h block 32) = v5
  generalize (e h block 33) = v6
  generalize (e h block 34) = v7
  generalize (word block 19) = v8
  generalize (word block 20) = v9
  generalize (word block 21) = v10
  generalize (word block 22) = v11
  generalize (word block 23) = v12
  generalize (word block 24) = v13
  generalize (word block 25) = v14
  generalize (word block 26) = v15
  generalize (word block 27) = v16
  generalize (word block 28) = v17
  generalize (word block 29) = v18
  generalize (word block 30) = v19
  generalize (word block 31) = v20
  generalize (word block 32) = v21
  generalize (word block 33) = v22
  generalize (word block 34) = v23
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end P256.Proofs.SHA256.Compression.Values.Correctness
