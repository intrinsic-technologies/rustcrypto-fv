import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Part01
import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Rounds

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Instructions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem part48 (h : BitVecState) (block : Array Bool) (context : ValueContext) (s : Values)
    (_input : ∀ i, i < 16 → bswap64 (context.inputWords (8*i)) = word block i)
    (constants : ∀ i, i < 80 → context.constants (8*i) = (NIST.SHA512.roundConstants[i]!).toBitVec)
    (start : invariant48 h block s) : invariant49 h block (run context Program.part48 s) := by
  have rotate (x : BitVec 64) : x.rotateRight 1 = x.rotateLeft 63 := by
    rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
    exact BitVec.or_comm _ _
  have constant63 : context.constants 504 = (NIST.SHA512.roundConstants[63]!).toBitVec := constants 63 (by decide)
  have constant64 : context.constants 512 = (NIST.SHA512.roundConstants[64]!).toBitVec := constants 64 (by decide)
  rcases start with ⟨hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr13, hr14, hs0, hs8, hs16, hs24, hs40, hs48, hs56, hs72, hs80, hs88, hs96, hs120, hs128, hs144, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352⟩
  simp only [invariant49, Program.part48, run]
  simp only [↓Op.eval_regs, ↓Op.stack_eval, Source.read64, read64, Binary.apply,
    BitVec.reduceEq, Nat.reduceEqDiff, Nat.reduceAdd, ite_true, ite_false,
    BitVec.shiftLeft_zero, BitVec.add_zero, bswap64_bswap64, true_and, and_true,
    hr0, hr1, hr2, hr3, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr13, hr14, hs0, hs8, hs16, hs24, hs40, hs48, hs56, hs72, hs80, hs88, hs96, hs120, hs128, hs144, hs176, hs304, hs312, hs320, hs328, hs336, hs344, hs352, constant63, constant64]
  simp only [rotate, a64, a65, e64, e65, w63, w64, choice_xor, choice_xor_commuted]
  generalize (a h block 60) = va60
  generalize (a h block 61) = va61
  generalize (a h block 62) = va62
  generalize (a h block 63) = va63
  generalize (a h block 64) = va64
  generalize (a h block 65) = va65
  generalize (e h block 60) = ve60
  generalize (e h block 61) = ve61
  generalize (e h block 62) = ve62
  generalize (e h block 63) = ve63
  generalize (e h block 64) = ve64
  generalize (e h block 65) = ve65
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
  generalize (word block 63) = vw63
  generalize (word block 64) = vw64
  generalize (NIST.SHA512.roundConstants[63]!).toBitVec = vk63
  generalize (NIST.SHA512.roundConstants[64]!).toBitVec = vk64
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl
  all_goals simp only [BitVec.add_zero, BitVec.zero_add]

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
