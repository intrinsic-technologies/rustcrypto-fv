import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part24 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant24 h block s) : invariant25 h block (run context Program.part24 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  have constant20 : context.constants 160 = (NIST.SHA512.roundConstants[20]!).toBitVec := constants 20 (by decide)
  have constant21 : context.constants 168 = (NIST.SHA512.roundConstants[21]!).toBitVec := constants 21 (by decide)
  rcases start with ⟨hr1, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hs8, hs16, hs24, hs32, hs48, hs56, hs88, hs96, hs120, hs128, hs136, hs152, hs160, hs168, hs176, hs192, hs200, hs256, hs264, hs272, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant25, Program.part24, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr1, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hs8, hs16, hs24, hs32, hs48, hs56, hs88, hs96, hs120, hs128, hs136, hs152, hs160, hs168, hs176, hs192, hs200, hs256, hs264, hs272, hs304, hs312, hs320, hs328, hs336, hs344, hs352, constant20, constant21]
  simp only [rotate, a21, e21, w20, w21, choice_xor, choice_xor_commuted]
  generalize (a h block 17) = va17
  generalize (a h block 18) = va18
  generalize (a h block 19) = va19
  generalize (a h block 20) = va20
  generalize (a h block 21) = va21
  generalize (e h block 17) = ve17
  generalize (e h block 18) = ve18
  generalize (e h block 19) = ve19
  generalize (e h block 20) = ve20
  generalize (e h block 21) = ve21
  generalize (word block 10) = vw10
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
  generalize (word block 4) = vw4
  generalize (word block 5) = vw5
  generalize (word block 6) = vw6
  generalize (word block 7) = vw7
  generalize (word block 8) = vw8
  generalize (word block 9) = vw9
  generalize (NIST.SHA512.roundConstants[20]!).toBitVec = vk20
  generalize (NIST.SHA512.roundConstants[21]!).toBitVec = vk21
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
