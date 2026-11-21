import Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness.Invariants

import Hkdf.Proofs.Common.SHA256.Compression.Values.ReadSteps

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness

open Hkdf.Proofs.NIST

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part52 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap32 (context.inputWords (4*i)) = word block i)
    (start : invariant52 h block s) : invariant53 h block (run context Program.part52 s) := by
  rcases start with ⟨hr0, hr1, hr2, hr3, hr8, hr9, hr10, hr14, hs188⟩
  simp only [invariant53, Program.part52, run]
  simp only [↓Op.low_eval, ↓Op.stack_eval, Source.read32, read32, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero,
    hr0, hr1, hr2, hr3, hr8, hr9, hr10, hr14, hs188]
  try simp only [choice_xor]
  generalize (a h block 60) = v0
  generalize (a h block 61) = v1
  generalize (a h block 62) = v2
  generalize (a h block 63) = v3
  generalize (e h block 60) = v4
  generalize (e h block 61) = v5
  generalize (e h block 62) = v6
  generalize (e h block 63) = v7
  generalize (word block 63) = v8
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

end Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness
