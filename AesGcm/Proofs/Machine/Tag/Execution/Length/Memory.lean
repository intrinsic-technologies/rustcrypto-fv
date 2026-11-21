import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Common.Bitwise
import AesGcm.Proofs.Machine.GHASHUpdate.ByteReverse

namespace AesGcm.Proofs.Machine.Tag.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def lengthMemory (mem : Ram) (sp aad message ret : BitVec 64) : Ram :=
  let x := bswapSpec (message <<< 3)
  let y := bswapSpec (aad <<< 3)
  let mem := memStore mem (sp + 16) ((x >>> 56).setWidth 8)
  let mem := memStore mem (sp + 31) (y.setWidth 8)
  let mem := memStore mem (sp + 17) ((x >>> 48).setWidth 8)
  let mem := memStore mem (sp + 30) (y.extractLsb' 8 8)
  let mem := memStore mem (sp + 18) ((x >>> 40).setWidth 8)
  let mem := memStore mem (sp + 29) (((y.setWidth 32) >>> 16).setWidth 8)
  let mem := memStore mem (sp + 19) ((x >>> 32).setWidth 8)
  let mem := memStore mem (sp + 28) (((y.setWidth 32) >>> 24).setWidth 8)
  let mem := memStore mem (sp + 20) (((x.setWidth 32) >>> 24).setWidth 8)
  let mem := memStore mem (sp + 27) ((y >>> 32).setWidth 8)
  let mem := memStore mem (sp + 21) (0 : BitVec 8)
  let mem := memStore mem (sp + 26) ((y >>> 40).setWidth 8)
  let mem := memStore mem (sp + 22) (0 : BitVec 16)
  let mem := memStore mem (sp + 25) ((y >>> 48).setWidth 8)
  let mem := memStore mem (sp + 24) ((y >>> 56).setWidth 8)
  memStore mem (sp - 8) ret

private theorem length_bswap_extract (x : BitVec 64) (start : Nat)
    (hs : start < 64) (ha : start % 8 = 0) :
    (bswapSpec x).extractLsb' start 8 = x.extractLsb' (56 - start) 8 := by
  have he : start = 8 * (start / 8) := by omega
  rw [he, GHASHUpdate.bswap64_extract_byte x (start / 8) (by omega)]
  congr 1
  omega

private theorem length_message_highByte (message : BitVec 64)
    (hmessage : message.toNat < 2 ^ 36) (start : Nat) (hs : 40 ≤ start) :
    (message <<< 3).extractLsb' start 8 = 0 := by
  have hbits := (BitVec.toNat_lt_iff_getLsbD_eq_false 36 (by decide)).mp hmessage
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and,
    BitVec.getLsbD_shiftLeft]
  rw [show start + k - 3 = 36 + (start + k - 3 - 36) by omega, hbits]
  simp only [Bool.and_false]
  exact BitVec.getLsbD_zero.symm

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem lengthMemory_byte (mem : Ram) (sp aad message ret : BitVec 64)
    (hmessage : message.toNat < 2 ^ 36) (i : Nat) (hi : i < 16) :
    memLoad (lengthMemory mem sp aad message ret) (sp + 16 + BitVec.ofNat 64 i) 8 =
      if i < 8 then (message <<< 3).extractLsb' (8 * i) 8
      else (aad <<< 3).extractLsb' (8 * (i - 8)) 8 := by
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Nat.reduceLT, Nat.reduceSub, Nat.reduceMul, ite_true, ite_false]
    refine_norm [lengthMemory]
    all_goals first
      | (simp (disch := omega) only [BitVec.setWidth_ushiftRight_eq_extractLsb,
          BitVec.extractLsb'_setWidth_of_le, length_bswap_extract, Nat.reduceSub]; done)
      | (change (0 : BitVec 8) = _; symm;
          apply length_message_highByte message hmessage; omega)
      | (rw [BitVec.setWidth_eq_extractLsb' (by decide),
          length_bswap_extract _ 0 (by decide) (by decide)])

theorem lengthMemory_words (mem : Ram) (sp aad message ret : BitVec 64)
    (hmessage : message.toNat < 2 ^ 36) :
    memLoad (lengthMemory mem sp aad message ret) (sp + 16) 64 = message <<< 3 ∧
    memLoad (lengthMemory mem sp aad message ret) (sp + 24) 64 = aad <<< 3 := by
  constructor
  · apply GHASHUpdate.word64_eq_of_bytes
    intro i
    rw [extractLsb'_memLoad _ _ (8 * i.val) 8 (by omega) (by decide)
      (by have := i.isLt; omega)]
    have hdiv : 8 * i.val / 8 = i.val := by omega
    rw [hdiv]
    simpa only [i.isLt, ite_true] using lengthMemory_byte mem sp aad message ret hmessage
      i.val (by have := i.isLt; omega)
  · apply GHASHUpdate.word64_eq_of_bytes
    intro i
    rw [extractLsb'_memLoad _ _ (8 * i.val) 8 (by omega) (by decide)
      (by have := i.isLt; omega)]
    have h := lengthMemory_byte mem sp aad message ret hmessage (8 + i.val)
      (by have := i.isLt; omega)
    have hi : ¬8 + i.val < 8 := by omega
    simp only [hi, ite_false, Nat.add_sub_cancel_left] at h
    have ha : sp + 24 + BitVec.ofNat 64 (8 * i.val / 8) =
        sp + 16 + BitVec.ofNat 64 (8 + i.val) := by bv_omega
    rw [ha]
    exact h

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
theorem lengthMemory_frame (mem : Ram) (sp aad message ret : BitVec 64)
    (hroom : 8 ≤ sp.toNat) (hlow : (sp - 8).toNat + 40 ≤ 2 ^ 32) :
    RamWriteFrame mem (lengthMemory mem sp aad message ret) [span (sp - 8) 40] := by
  dsimp only [lengthMemory]
  runtime_finish [span]

theorem lengthMemory_return (mem : Ram) (sp aad message ret : BitVec 64) :
    memLoad (lengthMemory mem sp aad message ret) (sp - 8) 64 = ret := by
  exact memLoad_memStore_same _ _ _ (by decide) (by decide)

end AesGcm.Proofs.Machine.Tag.Execution
