import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part31 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant31 h block s) : invariant32 h block (run context Program.part31 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  have constant32 : context.constants 256 = (NIST.SHA512.roundConstants[32]!).toBitVec := constants 32 (by decide)
  have constant33 : context.constants 264 = (NIST.SHA512.roundConstants[33]!).toBitVec := constants 33 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr3, hr6, hr7, hr9, hr10, hr11, hr12, hr13, hr15, hs0, hs8, hs24, hs32, hs40, hs48, hs56, hs64, hs72, hs80, hs96, hs104, hs112, hs120, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant32, Program.part31, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr2, hr3, hr6, hr7, hr9, hr10, hr11, hr12, hr13, hr15, hs0, hs8, hs24, hs32, hs40, hs48, hs56, hs64, hs72, hs80, hs96, hs104, hs112, hs120, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352, constant32, constant33]
  simp only [rotate, a33, a34, e33, e34, w33, choice_xor, choice_xor_commuted]
  generalize (a h block 29) = va29
  generalize (a h block 30) = va30
  generalize (a h block 31) = va31
  generalize (a h block 32) = va32
  generalize (a h block 33) = va33
  generalize (a h block 34) = va34
  generalize (e h block 29) = ve29
  generalize (e h block 30) = ve30
  generalize (e h block 31) = ve31
  generalize (e h block 32) = ve32
  generalize (e h block 33) = ve33
  generalize (e h block 34) = ve34
  generalize (word block 17) = vw17
  generalize (word block 18) = vw18
  generalize (word block 19) = vw19
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
  generalize (NIST.SHA512.roundConstants[32]!).toBitVec = vk32
  generalize (NIST.SHA512.roundConstants[33]!).toBitVec = vk33
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
