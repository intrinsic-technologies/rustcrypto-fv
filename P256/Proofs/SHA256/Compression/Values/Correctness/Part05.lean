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
theorem part05 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant05 h block s) : invariant06 h block (run context Program.part05 s) := by
  have input8 : bswap32 (context.inputWords 32) = word block 8 := input 8 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr3, hr6, hr7, hr8, hr9, hr10, hr11, hs20, hs36, hs40, hs56, hs64, hs72, hs80, hs104, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant06, Program.part05, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr3, hr6, hr7, hr8, hr9, hr10, hr11, hs20, hs36, hs40, hs56, hs64, hs72, hs80, hs104, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280, input8]
  try simp only [choice_xor, a08, a09, e08, e09]
  generalize (a h block 4) = v0
  generalize (a h block 5) = v1
  generalize (a h block 6) = v2
  generalize (a h block 7) = v3
  generalize (e h block 4) = v4
  generalize (e h block 5) = v5
  generalize (e h block 6) = v6
  generalize (e h block 7) = v7
  generalize (word block 0) = v8
  generalize (word block 1) = v9
  generalize (word block 2) = v10
  generalize (word block 3) = v11
  generalize (word block 4) = v12
  generalize (word block 5) = v13
  generalize (word block 6) = v14
  generalize (word block 7) = v15
  generalize (word block 8) = v16
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end P256.Proofs.SHA256.Compression.Values.Correctness
