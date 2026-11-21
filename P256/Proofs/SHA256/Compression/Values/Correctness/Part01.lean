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
theorem part01 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant01 h block s) : invariant02 h block (run context Program.part01 s) := by
  have input2 : bswap32 (context.inputWords 8) = word block 2 := input 2 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr3, hr6, hr7, hr9, hr10, hr12, hr13, hr14, hr15, hs56, hs80, hs188, hs264, hs272, hs280⟩
  simp only [invariant02, Program.part01, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr3, hr6, hr7, hr9, hr10, hr12, hr13, hr14, hr15, hs56, hs80, hs188, hs264, hs272, hs280, input2]
  try simp only [choice_xor, a02, e02]
  generalize (a h block 1) = v0
  generalize (e h block 1) = v1
  generalize (word block 0) = v2
  generalize (word block 1) = v3
  generalize (word block 2) = v4
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end P256.Proofs.SHA256.Compression.Values.Correctness
