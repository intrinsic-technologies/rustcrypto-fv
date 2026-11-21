import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part35 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant35 h block s) : invariant36 h block (run context Program.part35 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  have constant40 : context.constants 320 = (NIST.SHA512.roundConstants[40]!).toBitVec := constants 40 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr15, hs8, hs16, hs24, hs40, hs48, hs80, hs88, hs96, hs104, hs112, hs120, hs128, hs136, hs144, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant36, Program.part35, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr15, hs8, hs16, hs24, hs40, hs48, hs80, hs88, hs96, hs104, hs112, hs120, hs128, hs136, hs144, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352, constant40]
  simp only [rotate, a40, a41, e40, e41, w40, choice_xor, choice_xor_commuted]
  generalize (a h block 36) = va36
  generalize (a h block 37) = va37
  generalize (a h block 38) = va38
  generalize (a h block 39) = va39
  generalize (a h block 40) = va40
  generalize (a h block 41) = va41
  generalize (e h block 36) = ve36
  generalize (e h block 37) = ve37
  generalize (e h block 38) = ve38
  generalize (e h block 39) = ve39
  generalize (e h block 40) = ve40
  generalize (e h block 41) = ve41
  generalize (word block 24) = vw24
  generalize (word block 25) = vw25
  generalize (word block 26) = vw26
  generalize (word block 27) = vw27
  generalize (word block 28) = vw28
  generalize (word block 29) = vw29
  generalize (word block 30) = vw30
  generalize (word block 31) = vw31
  generalize (word block 32) = vw32
  generalize (word block 33) = vw33
  generalize (word block 34) = vw34
  generalize (word block 35) = vw35
  generalize (word block 36) = vw36
  generalize (word block 37) = vw37
  generalize (word block 38) = vw38
  generalize (word block 39) = vw39
  generalize (word block 40) = vw40
  generalize (NIST.SHA512.roundConstants[39]!).toBitVec = vk39
  generalize (NIST.SHA512.roundConstants[40]!).toBitVec = vk40
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
