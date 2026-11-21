import Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness.Invariants

import Hkdf.Proofs.Common.SHA256.Compression.Values.ReadSteps

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness

open Hkdf.Proofs.NIST

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part07 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant07 h block s) : invariant08 h block (run context Program.part07 s) := by
  have input11 : bswap32 (context.inputWords 44) = word block 11 := input 11 (by decide)
  have input12 : bswap32 (context.inputWords 48) = word block 12 := input 12 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr6, hr7, hr8, hr9, hr10, hr11, hs8, hs12, hs20, hs36, hs40, hs56, hs64, hs72, hs80, hs96, hs104, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280⟩
  simp only [invariant08, Program.part07, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr6, hr7, hr8, hr9, hr10, hr11, hs8, hs12, hs20, hs36, hs40, hs56, hs64, hs72, hs80, hs96, hs104, hs188, hs232, hs240, hs248, hs256, hs264, hs272, hs280, input11, input12]
  try simp only [choice_xor, a11, a12, e11, e12]
  generalize (a h block 10) = v0
  generalize (a h block 7) = v1
  generalize (a h block 8) = v2
  generalize (a h block 9) = v3
  generalize (e h block 10) = v4
  generalize (e h block 7) = v5
  generalize (e h block 8) = v6
  generalize (e h block 9) = v7
  generalize (word block 0) = v8
  generalize (word block 1) = v9
  generalize (word block 10) = v10
  generalize (word block 11) = v11
  generalize (word block 12) = v12
  generalize (word block 2) = v13
  generalize (word block 3) = v14
  generalize (word block 4) = v15
  generalize (word block 5) = v16
  generalize (word block 6) = v17
  generalize (word block 7) = v18
  generalize (word block 8) = v19
  generalize (word block 9) = v20
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness
