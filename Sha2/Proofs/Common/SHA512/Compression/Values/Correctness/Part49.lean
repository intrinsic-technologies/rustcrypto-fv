import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part49 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant49 h block s) : invariant50 h block (run context Program.part49 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  have constant65 : context.constants 520 = (NIST.SHA512.roundConstants[65]!).toBitVec := constants 65 (by decide)
  have constant66 : context.constants 528 = (NIST.SHA512.roundConstants[66]!).toBitVec := constants 66 (by decide)
  rcases start with ⟨hr1, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr12, hr14, hr15, hs0, hs8, hs24, hs32, hs40, hs48, hs56, hs64, hs72, hs80, hs88, hs96, hs120, hs128, hs144, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant50, Program.part49, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr1, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr12, hr14, hr15, hs0, hs8, hs24, hs32, hs40, hs48, hs56, hs64, hs72, hs80, hs88, hs96, hs120, hs128, hs144, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352, constant65, constant66]
  simp only [rotate, a66, a67, e66, e67, w65, w66, w67, choice_xor, choice_xor_commuted]
  generalize (a h block 62) = va62
  generalize (a h block 63) = va63
  generalize (a h block 64) = va64
  generalize (a h block 65) = va65
  generalize (a h block 66) = va66
  generalize (a h block 67) = va67
  generalize (e h block 62) = ve62
  generalize (e h block 63) = ve63
  generalize (e h block 64) = ve64
  generalize (e h block 65) = ve65
  generalize (e h block 66) = ve66
  generalize (e h block 67) = ve67
  generalize (word block 49) = vw49
  generalize (word block 50) = vw50
  generalize (word block 51) = vw51
  generalize (word block 52) = vw52
  generalize (word block 53) = vw53
  generalize (word block 54) = vw54
  generalize (word block 55) = vw55
  generalize (word block 56) = vw56
  generalize (word block 57) = vw57
  generalize (word block 58) = vw58
  generalize (word block 59) = vw59
  generalize (word block 60) = vw60
  generalize (word block 61) = vw61
  generalize (word block 62) = vw62
  generalize (word block 63) = vw63
  generalize (word block 64) = vw64
  generalize (word block 65) = vw65
  generalize (word block 66) = vw66
  generalize (word block 67) = vw67
  generalize (NIST.SHA512.roundConstants[65]!).toBitVec = vk65
  generalize (NIST.SHA512.roundConstants[66]!).toBitVec = vk66
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl
  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
