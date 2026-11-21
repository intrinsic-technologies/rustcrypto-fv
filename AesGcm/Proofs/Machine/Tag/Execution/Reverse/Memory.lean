import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Common.Bitwise
import AesGcm.Proofs.Machine.GHASHUpdate.ByteReverse

namespace AesGcm.Proofs.Machine.Tag.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def reverseMemory (mem : Ram) (sp ret : BitVec 64) : Ram :=
  let lo := memLoad mem (sp + 64) 64
  let hi := memLoad mem (sp + 72) 64
  let mem := memStore mem (sp + 24) hi
  let mem := memStore mem (sp + 16) lo
  let b31 := memLoad mem (sp + 31) 8
  let mem := memStore mem (sp + 16) b31
  let mem := memStore mem (sp + 31) (lo.setWidth 8)
  let w17 := memLoad mem (sp + 17) 16
  let r17 := (mergeGPR 16 (w17.rotateLeft 8) (w17.setWidth 64)).setWidth 16
  let w29 := memLoad mem (sp + 29) 16
  let r29 := (mergeGPR 16 (w29.rotateLeft 8) (w29.setWidth 64)).setWidth 16
  let w19 := memLoad mem (sp + 19) 16
  let mem := memStore mem (sp + 17) r29
  let r19 := (mergeGPR 16 (w19.rotateLeft 8) (w19.setWidth 64)).setWidth 16
  let mem := memStore mem (sp + 29) r17
  let w27 := memLoad mem (sp + 27) 16
  let r27 := (mergeGPR 16 (w27.rotateLeft 8) (w27.setWidth 64)).setWidth 16
  let mem := memStore mem (sp + 19) r27
  let mem := memStore mem (sp + 27) r19
  let b21 := memLoad mem (sp + 21) 8
  let b26 := memLoad mem (sp + 26) 8
  let mem := memStore mem (sp + 21) b26
  let mem := memStore mem (sp + 26) b21
  let b22 := memLoad mem (sp + 22) 8
  let b25 := memLoad mem (sp + 25) 8
  let mem := memStore mem (sp + 22) b25
  let mem := memStore mem (sp + 25) b22
  let mem := memStore mem (sp + 23) ((memLoad mem (sp + 23) 16).rotateLeft 8)
  memStore mem (sp - 8) ret

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem reverseMemory_byte (mem : Ram) (sp ret : BitVec 64) (i : Nat) (hi : i < 16) :
    memLoad (reverseMemory mem sp ret) (sp + 16 + BitVec.ofNat 64 i) 8 =
      if i < 8 then (memLoad mem (sp + 72) 64).extractLsb' (8 * (7 - i)) 8
      else (memLoad mem (sp + 64) 64).extractLsb' (8 * (15 - i)) 8 := by
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Nat.reduceLT, Nat.reduceSub, Nat.reduceMul, ite_true, ite_false]
    refine_norm [reverseMemory, AesGcm.Proofs.setWidth_mergeGPR16,
      GHASHUpdate.rotate16_extract_low, GHASHUpdate.rotate16_extract_high]
    all_goals simp only [BitVec.ofNat_eq_ofNat]
  change (memLoad mem (sp + 64) 64).extractLsb' 0 8 = _
  rw [extractLsb'_memLoad _ _ 0 8 (by decide) (by decide) (by decide)]
  simp only [Nat.zero_div, BitVec.add_zero]
  rfl

theorem reverseMemory_words (mem : Ram) (sp ret : BitVec 64) :
    memLoad (reverseMemory mem sp ret) (sp + 16) 64 =
      bswapSpec (memLoad mem (sp + 72) 64) ∧
    memLoad (reverseMemory mem sp ret) (sp + 24) 64 =
      bswapSpec (memLoad mem (sp + 64) 64) := by
  constructor
  · apply GHASHUpdate.word64_eq_of_bytes
    intro i
    rw [GHASHUpdate.bswap64_extract_byte _ i.val i.isLt,
      extractLsb'_memLoad _ _ (8 * i.val) 8 (by omega) (by decide)
        (by have := i.isLt; omega)]
    have hdiv : 8 * i.val / 8 = i.val := by omega
    rw [hdiv]
    simpa only [i.isLt, ite_true] using reverseMemory_byte mem sp ret i.val (by omega)
  · apply GHASHUpdate.word64_eq_of_bytes
    intro i
    rw [GHASHUpdate.bswap64_extract_byte _ i.val i.isLt,
      extractLsb'_memLoad _ _ (8 * i.val) 8 (by omega) (by decide)
        (by have := i.isLt; omega)]
    have h := reverseMemory_byte mem sp ret (8 + i.val) (by have := i.isLt; omega)
    have hi : ¬8 + i.val < 8 := by omega
    have he : 15 - (8 + i.val) = 7 - i.val := by omega
    simp only [hi, ite_false, he] at h
    have haddr : sp + 24 + BitVec.ofNat 64 (8 * i.val / 8) =
        sp + 16 + BitVec.ofNat 64 (8 + i.val) := by bv_omega
    rw [haddr]
    exact h

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
theorem reverseMemory_frame (mem : Ram) (sp ret : BitVec 64)
    (hroom : 8 ≤ sp.toNat) (hlow : (sp - 8).toNat + 40 ≤ 2^32) :
    RamWriteFrame mem (reverseMemory mem sp ret) [span (sp - 8) 40] := by
  dsimp only [reverseMemory]
  runtime_finish [span]

theorem reverseMemory_return (mem : Ram) (sp ret : BitVec 64) :
    memLoad (reverseMemory mem sp ret) (sp - 8) 64 = ret := by
  exact memLoad_memStore_same _ _ _ (by decide) (by decide)

end AesGcm.Proofs.Machine.Tag.Execution
