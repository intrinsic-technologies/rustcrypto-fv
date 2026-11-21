import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part28 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant28 h block s) : invariant29 h block (run context Program.part28 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  have constant27 : context.constants 216 = (NIST.SHA512.roundConstants[27]!).toBitVec := constants 27 (by decide)
  have constant28 : context.constants 224 = (NIST.SHA512.roundConstants[28]!).toBitVec := constants 28 (by decide)
  rcases start with ⟨hr0, hr1, hr3, hr5, hr7, hr8, hr9, hr10, hr11, hr13, hr15, hs0, hs8, hs16, hs32, hs40, hs56, hs64, hs72, hs88, hs96, hs104, hs136, hs168, hs176, hs200, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant29, Program.part28, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr3, hr5, hr7, hr8, hr9, hr10, hr11, hr13, hr15, hs0, hs8, hs16, hs32, hs40, hs56, hs64, hs72, hs88, hs96, hs104, hs136, hs168, hs176, hs200, hs304, hs312, hs320, hs328, hs336, hs344, hs352, constant27, constant28]
  simp only [rotate, a27, a28, e27, e28, w27, w28, choice_xor, choice_xor_commuted]
  generalize (a h block 23) = va23
  generalize (a h block 24) = va24
  generalize (a h block 25) = va25
  generalize (a h block 26) = va26
  generalize (a h block 27) = va27
  generalize (a h block 28) = va28
  generalize (e h block 23) = ve23
  generalize (e h block 24) = ve24
  generalize (e h block 25) = ve25
  generalize (e h block 26) = ve26
  generalize (e h block 27) = ve27
  generalize (e h block 28) = ve28
  generalize (word block 11) = vw11
  generalize (word block 12) = vw12
  generalize (word block 13) = vw13
  generalize (word block 14) = vw14
  generalize (word block 15) = vw15
  generalize (word block 16) = vw16
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
  generalize (NIST.SHA512.roundConstants[26]!).toBitVec = vk26
  generalize (NIST.SHA512.roundConstants[27]!).toBitVec = vk27
  generalize (NIST.SHA512.roundConstants[28]!).toBitVec = vk28
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
