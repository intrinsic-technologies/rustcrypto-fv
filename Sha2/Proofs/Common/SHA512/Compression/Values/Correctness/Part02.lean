import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part02 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (start : invariant02 h block s) : invariant03 h block (run context Program.part02 s) := by
  have input4raw : context.inputWords 32 = bswap64 (word block 4) := by
    rw [← bswap64_bswap64 (context.inputWords 32), input 4 (by decide)]
  have input5raw : context.inputWords 40 = bswap64 (word block 5) := by
    rw [← bswap64_bswap64 (context.inputWords 40), input 5 (by decide)]
  have input6raw : context.inputWords 48 = bswap64 (word block 6) := by
    rw [← bswap64_bswap64 (context.inputWords 48), input 6 (by decide)]
  have input7raw : context.inputWords 56 = bswap64 (word block 7) := by
    rw [← bswap64_bswap64 (context.inputWords 56), input 7 (by decide)]
  have input8raw : context.inputWords 64 = bswap64 (word block 8) := by
    rw [← bswap64_bswap64 (context.inputWords 64), input 8 (by decide)]
  have input9raw : context.inputWords 72 = bswap64 (word block 9) := by
    rw [← bswap64_bswap64 (context.inputWords 72), input 9 (by decide)]
  have input10raw : context.inputWords 80 = bswap64 (word block 10) := by
    rw [← bswap64_bswap64 (context.inputWords 80), input 10 (by decide)]
  have input11raw : context.inputWords 88 = bswap64 (word block 11) := by
    rw [← bswap64_bswap64 (context.inputWords 88), input 11 (by decide)]
  have input12raw : context.inputWords 96 = bswap64 (word block 12) := by
    rw [← bswap64_bswap64 (context.inputWords 96), input 12 (by decide)]
  have input13raw : context.inputWords 104 = bswap64 (word block 13) := by
    rw [← bswap64_bswap64 (context.inputWords 104), input 13 (by decide)]
  have input14raw : context.inputWords 112 = bswap64 (word block 14) := by
    rw [← bswap64_bswap64 (context.inputWords 112), input 14 (by decide)]
  have input15raw : context.inputWords 120 = bswap64 (word block 15) := by
    rw [← bswap64_bswap64 (context.inputWords 120), input 15 (by decide)]
  rcases start with ⟨hr11, hr1, hr10, hr0, hr3, hr9, hr8, hr15, hr13, hr14, hr5, hr12, hr2, hs0, hs72, hs144, hs176, hs344, hs352⟩
  simp only [invariant03, Program.part02, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr11, hr1, hr10, hr0, hr3, hr9, hr8, hr15, hr13, hr14, hr5, hr12, hr2, hs0, hs72, hs144, hs176, hs344, hs352, input4raw, input5raw, input6raw, input7raw, input8raw, input9raw, input10raw, input11raw, input12raw, input13raw, input14raw, input15raw]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
