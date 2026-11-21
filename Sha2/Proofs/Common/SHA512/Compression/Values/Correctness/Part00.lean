import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Invariants

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Common.Instructions

theorem part00 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (start : invariant00 h block s) :
    invariant01 h block (run context Program.part00 s) := by
  rcases start with ⟨hr11, hr1, hr10, hr0, hr3, hr9, hr8, hr13⟩
  simp only [invariant01, Program.part00, run, Op.eval, Source.read64,
    writeReg, write64,
    BitVec.reduceEq, ite_true, ite_false, hr11, hr1, hr10, hr0, hr3, hr9, hr8, hr13]
  repeat' apply And.intro
  all_goals first | exact True.intro | rfl

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
