import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part33 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant33 h block s) : invariant34 h block (run context Program.part33 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  have constant36 : context.constants 288 = (NIST.SHA512.roundConstants[36]!).toBitVec := constants 36 (by decide)
  have constant37 : context.constants 296 = (NIST.SHA512.roundConstants[37]!).toBitVec := constants 37 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr3, hr5, hr6, hr8, hr9, hr10, hr12, hr13, hr15, hs16, hs24, hs32, hs40, hs48, hs56, hs64, hs80, hs88, hs96, hs104, hs112, hs120, hs128, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant34, Program.part33, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr2, hr3, hr5, hr6, hr8, hr9, hr10, hr12, hr13, hr15, hs16, hs24, hs32, hs40, hs48, hs56, hs64, hs80, hs88, hs96, hs104, hs112, hs120, hs128, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352, constant36, constant37]
  simp only [rotate, a37, e37, w36, w37, choice_xor, choice_xor_commuted]
  generalize (a h block 33) = va33
  generalize (a h block 34) = va34
  generalize (a h block 35) = va35
  generalize (a h block 36) = va36
  generalize (a h block 37) = va37
  generalize (e h block 33) = ve33
  generalize (e h block 34) = ve34
  generalize (e h block 35) = ve35
  generalize (e h block 36) = ve36
  generalize (e h block 37) = ve37
  generalize (word block 20) = vw20
  generalize (word block 21) = vw21
  generalize (word block 22) = vw22
  generalize (word block 23) = vw23
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
  generalize (NIST.SHA512.roundConstants[36]!).toBitVec = vk36
  generalize (NIST.SHA512.roundConstants[37]!).toBitVec = vk37
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
