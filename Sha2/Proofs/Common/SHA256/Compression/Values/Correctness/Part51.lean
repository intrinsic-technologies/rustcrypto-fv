import Sha2.Proofs.Common.SHA256.Compression.Values.Correctness.Invariants

import Sha2.Proofs.Common.SHA256.Compression.Values.ReadSteps

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Values.Correctness

open Sha2.Proofs.NIST

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part51 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant51 h block s) : invariant52 h block (run context Program.part51 s) := by
  rcases start with ⟨hr0, hr1, hr2, hr3, hr5, hr7, hr8, hr9, hr10, hr11, hr15, hs40, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant52, Program.part51, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr3, hr5, hr7, hr8, hr9, hr10, hr11, hr15, hs40, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280]
  try simp only [choice_xor, a63, e63, w63]
  generalize (a h block 59) = v0
  generalize (a h block 60) = v1
  generalize (a h block 61) = v2
  generalize (a h block 62) = v3
  generalize (e h block 59) = v4
  generalize (e h block 60) = v5
  generalize (e h block 61) = v6
  generalize (e h block 62) = v7
  generalize (word block 47) = v8
  generalize (word block 48) = v9
  generalize (word block 56) = v10
  generalize (word block 61) = v11
  generalize (word block 62) = v12
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end Sha2.Proofs.Common.SHA256.Compression.Values.Correctness
