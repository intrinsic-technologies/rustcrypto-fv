import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part43 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant43 h block s) : invariant44 h block (run context Program.part43 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  have constant54 : context.constants 432 = (NIST.SHA512.roundConstants[54]!).toBitVec := constants 54 (by decide)
  have constant55 : context.constants 440 = (NIST.SHA512.roundConstants[55]!).toBitVec := constants 55 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr14, hr15, hs0, hs16, hs24, hs32, hs40, hs48, hs56, hs64, hs72, hs80, hs104, hs112, hs120, hs128, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant44, Program.part43, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr14, hr15, hs0, hs16, hs24, hs32, hs40, hs48, hs56, hs64, hs72, hs80, hs104, hs112, hs120, hs128, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352, constant54, constant55]
  simp only [rotate, a54, a55, e55, w54, w55, choice_xor, choice_xor_commuted]
  generalize (a h block 51) = va51
  generalize (a h block 52) = va52
  generalize (a h block 53) = va53
  generalize (a h block 54) = va54
  generalize (a h block 55) = va55
  generalize (e h block 50) = ve50
  generalize (e h block 51) = ve51
  generalize (e h block 52) = ve52
  generalize (e h block 53) = ve53
  generalize (e h block 54) = ve54
  generalize (e h block 55) = ve55
  generalize (word block 38) = vw38
  generalize (word block 39) = vw39
  generalize (word block 40) = vw40
  generalize (word block 41) = vw41
  generalize (word block 42) = vw42
  generalize (word block 43) = vw43
  generalize (word block 44) = vw44
  generalize (word block 45) = vw45
  generalize (word block 46) = vw46
  generalize (word block 47) = vw47
  generalize (word block 48) = vw48
  generalize (word block 49) = vw49
  generalize (word block 50) = vw50
  generalize (word block 51) = vw51
  generalize (word block 52) = vw52
  generalize (word block 53) = vw53
  generalize (word block 54) = vw54
  generalize (word block 55) = vw55
  generalize (NIST.SHA512.roundConstants[53]!).toBitVec = vk53
  generalize (NIST.SHA512.roundConstants[54]!).toBitVec = vk54
  generalize (NIST.SHA512.roundConstants[55]!).toBitVec = vk55
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl
  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
