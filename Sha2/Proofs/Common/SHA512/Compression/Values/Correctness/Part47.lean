import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part47 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant47 h block s) : invariant48 h block (run context Program.part47 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  have constant61 : context.constants 488 = (NIST.SHA512.roundConstants[61]!).toBitVec := constants 61 (by decide)
  have constant62 : context.constants 496 = (NIST.SHA512.roundConstants[62]!).toBitVec := constants 62 (by decide)
  rcases start with ⟨hr0, hr3, hr5, hr6, hr7, hr8, hr9, hr11, hr12, hr14, hr15, hs0, hs8, hs16, hs24, hs32, hs40, hs48, hs56, hs72, hs80, hs88, hs96, hs120, hs128, hs144, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant48, Program.part47, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr3, hr5, hr6, hr7, hr8, hr9, hr11, hr12, hr14, hr15, hs0, hs8, hs16, hs24, hs32, hs40, hs48, hs56, hs72, hs80, hs88, hs96, hs120, hs128, hs144, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352, constant61, constant62]
  simp only [rotate, a62, a63, e62, e63, w61, w62, choice_xor, choice_xor_commuted]
  generalize (a h block 58) = va58
  generalize (a h block 59) = va59
  generalize (a h block 60) = va60
  generalize (a h block 61) = va61
  generalize (a h block 62) = va62
  generalize (a h block 63) = va63
  generalize (e h block 58) = ve58
  generalize (e h block 59) = ve59
  generalize (e h block 60) = ve60
  generalize (e h block 61) = ve61
  generalize (e h block 62) = ve62
  generalize (e h block 63) = ve63
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
  generalize (word block 56) = vw56
  generalize (word block 57) = vw57
  generalize (word block 58) = vw58
  generalize (word block 59) = vw59
  generalize (word block 60) = vw60
  generalize (word block 61) = vw61
  generalize (word block 62) = vw62
  generalize (NIST.SHA512.roundConstants[61]!).toBitVec = vk61
  generalize (NIST.SHA512.roundConstants[62]!).toBitVec = vk62
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl
  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
