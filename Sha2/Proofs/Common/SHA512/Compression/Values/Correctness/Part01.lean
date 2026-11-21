import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Invariants

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values

theorem Op.eval_regs (operation : Op) (context : ValueContext) (state : Values) (r : BitVec 5) :
    (operation.eval context state).regs r =
      match operation with
      | .mov64 dst src => if r = dst then src.read64 context state else state.regs r
      | .store64 _ _ => state.regs r
      | .addStack64 _ _ => state.regs r
      | .xorStack64 _ _ => state.regs r
      | .binary64 op dst src => if r = dst then op.apply (state.regs dst) (src.read64 context state) else state.regs r
      | .not64 dst => if r = dst then ~~~(state.regs dst) else state.regs r
      | .rol64 dst count => if r = dst then (state.regs dst).rotateLeft count else state.regs r
      | .ror64 dst count => if r = dst then (state.regs dst).rotateRight count else state.regs r
      | .shr64 dst count => if r = dst then (state.regs dst) >>> count else state.regs r
      | .lea64 dst base index scale disp =>
          if r = dst then state.regs base + (match index with | none => 0 | some i => state.regs i <<< scale) + disp
          else state.regs r
      | .bswap64 dst => if r = dst then Instructions.bswap64 (state.regs dst) else state.regs r := by
  cases operation <;> simp only [Op.eval, writeReg] <;> try rfl


theorem Op.stack_eval (operation : Op) (context : ValueContext) (state : Values) (offset : Nat) :
    (operation.eval context state).stack offset =
      match operation with
      | .store64 off src => if offset = off then state.regs src else state.stack offset
      | .addStack64 off src => if offset = off then state.stack off + state.regs src else state.stack offset
      | .xorStack64 off src => if offset = off then state.stack off ^^^ state.regs src else state.stack offset
      | _ => state.stack offset := by
  cases operation <;> rfl

end Sha2.Proofs.Common.SHA512.Compression.Values

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.NIST
open Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
theorem part01 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (start : invariant01 h block s) : invariant02 h block (run context Program.part01 s) := by
  have input0 : bswap64 (context.inputWords 0) = word block 0 := input 0 (by decide)
  have input1 : bswap64 (context.inputWords 8) = word block 1 := input 1 (by decide)
  have input2 : bswap64 (context.inputWords 16) = word block 2 := input 2 (by decide)
  have input3 : bswap64 (context.inputWords 24) = word block 3 := input 3 (by decide)
  have input1raw : context.inputWords 8 = bswap64 (word block 1) := by rw [← bswap64_bswap64 (context.inputWords 8), input1]
  have input2raw : context.inputWords 16 = bswap64 (word block 2) := by rw [← bswap64_bswap64 (context.inputWords 16), input2]
  have input3raw : context.inputWords 24 = bswap64 (word block 3) := by rw [← bswap64_bswap64 (context.inputWords 24), input3]
  rcases start with ⟨hr11, hr1, hr10, hr0, hr3, hr9, hr8, hr13, hr15, hr14, hr5, hr12, hs176, hs344⟩
  simp only [invariant02, Program.part01, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_zero, true_and, and_true,
    hr11, hr1, hr10, hr0, hr3, hr9, hr8, hr13, hr15, hr14, hr5, hr12, hs176, hs344,
    input0, input1, input2, input3, input1raw, input2raw, input3raw]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
