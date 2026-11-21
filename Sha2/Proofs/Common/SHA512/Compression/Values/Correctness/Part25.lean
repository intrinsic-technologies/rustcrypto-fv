import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part25 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant25 h block s) : invariant26 h block (run context Program.part25 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  have constant22 : context.constants 176 = (NIST.SHA512.roundConstants[22]!).toBitVec := constants 22 (by decide)
  rcases start with ⟨hr0, hr1, hr3, hr5, hr6, hr7, hr9, hr12, hr13, hr14, hr15, hs0, hs8, hs16, hs32, hs48, hs56, hs72, hs80, hs88, hs96, hs136, hs152, hs160, hs168, hs176, hs192, hs200, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant26, Program.part25, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr3, hr5, hr6, hr7, hr9, hr12, hr13, hr14, hr15, hs0, hs8, hs16, hs32, hs48, hs56, hs72, hs80, hs88, hs96, hs136, hs152, hs160, hs168, hs176, hs192, hs200, hs304, hs312, hs320, hs328, hs336, hs344, hs352, constant22]
  simp only [rotate, a22, a23, e22, e23, w22, choice_xor, choice_xor_commuted]
  generalize (a h block 18) = va18
  generalize (a h block 19) = va19
  generalize (a h block 20) = va20
  generalize (a h block 21) = va21
  generalize (a h block 22) = va22
  generalize (a h block 23) = va23
  generalize (e h block 18) = ve18
  generalize (e h block 19) = ve19
  generalize (e h block 20) = ve20
  generalize (e h block 21) = ve21
  generalize (e h block 22) = ve22
  generalize (e h block 23) = ve23
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
  generalize (word block 22) = vw22
  generalize (word block 6) = vw6
  generalize (word block 7) = vw7
  generalize (word block 8) = vw8
  generalize (word block 9) = vw9
  generalize (NIST.SHA512.roundConstants[21]!).toBitVec = vk21
  generalize (NIST.SHA512.roundConstants[22]!).toBitVec = vk22
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
