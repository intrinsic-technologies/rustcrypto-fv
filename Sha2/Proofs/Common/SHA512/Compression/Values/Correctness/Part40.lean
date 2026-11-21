import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part40 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant40 h block s) : invariant41 h block (run context Program.part40 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  have constant49 : context.constants 392 = (NIST.SHA512.roundConstants[49]!).toBitVec := constants 49 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr3, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hs0, hs8, hs32, hs40, hs48, hs56, hs64, hs72, hs80, hs88, hs104, hs112, hs144, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant41, Program.part40, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr2, hr3, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hs0, hs8, hs32, hs40, hs48, hs56, hs64, hs72, hs80, hs88, hs104, hs112, hs144, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352, constant49]
  simp only [rotate, a49, a50, e49, e50, w49, choice_xor, choice_xor_commuted]
  generalize (a h block 45) = va45
  generalize (a h block 46) = va46
  generalize (a h block 47) = va47
  generalize (a h block 48) = va48
  generalize (a h block 49) = va49
  generalize (a h block 50) = va50
  generalize (e h block 45) = ve45
  generalize (e h block 46) = ve46
  generalize (e h block 47) = ve47
  generalize (e h block 48) = ve48
  generalize (e h block 49) = ve49
  generalize (e h block 50) = ve50
  generalize (word block 33) = vw33
  generalize (word block 34) = vw34
  generalize (word block 35) = vw35
  generalize (word block 36) = vw36
  generalize (word block 37) = vw37
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
  generalize (NIST.SHA512.roundConstants[48]!).toBitVec = vk48
  generalize (NIST.SHA512.roundConstants[49]!).toBitVec = vk49
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl
  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
