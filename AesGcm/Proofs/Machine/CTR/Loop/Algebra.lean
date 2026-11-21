import AesGcm.Proofs.Machine.CTR.BatchFull
import AesGcm.Proofs.Machine.KeySchedule.Memory

namespace AesGcm.Proofs.Machine.CTR.Loop

open Standards.NIST.AES Prelude
open AesGcm.Proofs.Machine.Fixslice
open AesGcm.Proofs.Machine.AESCore
open AesGcm.Proofs.Machine.KeySchedule

def batchRoundMix (round : Nat) : Planes → Planes :=
  match round % 4 with
  | 0 => mixColumns0
  | 1 => mixColumns1
  | 2 => mixColumns2
  | _ => mixColumns3

theorem batchRoundMix_encode (round : Nat) (blocks : Blocks) :
    batchRoundMix round (encode blocks) =
      encode (mixColumnsBlocks (rotateBlocks 1 (round % 4))
        (rotateBlocks 2 (2 * (round % 4))) blocks) := by
  have h : round % 4 = 0 ∨ round % 4 = 1 ∨ round % 4 = 2 ∨ round % 4 = 3 := by omega
  rcases h with h | h | h | h
  · simpa only [batchRoundMix, h, Nat.mul_zero] using mixColumns0_encode blocks
  · simpa only [batchRoundMix, h] using mixColumns1_encode blocks
  · simp only [batchRoundMix, h]
    rw [mixColumns2_encode, rotateBlocks_mod 2 4]
  · simp only [batchRoundMix, h]
    rw [mixColumns3_encode, rotateBlocks_mod 2 6]

theorem batchRoundState_step
    (use256 : Bool) (key : Vector UInt8 ((AES16.variant use256).keyBytes))
    (blocks : Blocks) (count : Nat) (hcount : count + 1 < (AES16.variant use256).Nr) :
    xorPlanes (batchRoundMix (count + 1)
      (Fixslice.subBytes (batchRoundState use256 key blocks count)))
      (KeySchedule.expectedKey (AES16.variant use256) key
        ⟨count + 1, by omega⟩) =
      batchRoundState use256 key blocks (count + 1) := by
  simpa only [batchRoundState] using
    (encryptRounds_succ_expectedKey (AES16.variant use256) key count hcount
      (batchRoundMix (count + 1)) (batchRoundMix_encode (count + 1)) (toStandard blocks))

def ctrDelayedPlanes (planes keys : Planes) : Planes :=
  fun p ↦ if p.val = 7 then planes p ^^^ keys p else planes p

theorem restore_batchDelayed (planes keys : Planes) :
    (fun p : Fin 8 ↦ if p.val = 7 then ctrDelayedPlanes planes keys 7 ^^^ keys 7
      else ctrDelayedPlanes planes keys p) = planes := by
  funext p
  by_cases hp : p.val = 7
  · have he : p = 7 := Fin.ext hp
    subst p
    simp only [ctrDelayedPlanes, show (7 : Fin 8).val = 7 from rfl, ite_true, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]
  · simp only [ctrDelayedPlanes, hp, ite_false]

theorem batchDelayed_xor (planes keys : Planes) :
    ctrDelayedPlanes (xorPlanes planes keys) keys =
      (fun p : Fin 8 ↦ if p.val = 7 then planes p else planes p ^^^ keys p) := by
  funext p
  by_cases hp : p.val = 7
  · simp only [ctrDelayedPlanes, xorPlanes, hp, ite_true, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero]
  · simp only [ctrDelayedPlanes, xorPlanes, hp, ite_false]

theorem keyWords_eq (use256 : Bool) :
    keyWords use256 = 8 * ((AES16.variant use256).Nr + 1) := by
  cases use256 <;> rfl

theorem scheduleWords_phaseKey
    (use256 : Bool) (key : Vector UInt8 ((AES16.variant use256).keyBytes))
    (i : Fin (keyWords use256)) :
    Fixslice16.widenWord ((narrowScheduleWords (AES16.variant use256) key)[i.val]'(by
      cases use256 <;> exact i.isLt)) =
      KeySchedule.expectedKey (AES16.variant use256) key
        ⟨i.val / 8, by have hi := i.isLt; have he := keyWords_eq use256; omega⟩
        ⟨i.val % 8, by omega⟩ := by
  let r : Fin ((AES16.variant use256).Nr + 1) :=
    ⟨i.val / 8, by have hi := i.isLt; have he := keyWords_eq use256; omega⟩
  let p : Fin 8 := ⟨i.val % 8, by omega⟩
  simp only [narrowScheduleWords, Vector.getElem_ofFn]
  change Fixslice16.widenWord (AES16.expectedKey _ key r p) = _
  exact congrFun (widenPlanes_expectedKey _ key r) p

theorem batch_iteration
    (use256 : Bool) (key : Vector UInt8 ((AES16.variant use256).keyBytes))
    (blocks : Blocks) (j : Nat) (hnext : 4 * (j + 1) < (AES16.variant use256).Nr) :
    let s0 := batchRoundState use256 key blocks (4 * j)
    let k1 := KeySchedule.expectedKey (AES16.variant use256) key ⟨4 * j + 1, by omega⟩
    let k2 := KeySchedule.expectedKey (AES16.variant use256) key ⟨4 * j + 2, by omega⟩
    let k3 := KeySchedule.expectedKey (AES16.variant use256) key ⟨4 * j + 3, by omega⟩
    let k4 := KeySchedule.expectedKey (AES16.variant use256) key ⟨4 * (j + 1), by omega⟩
    let s1 := xorPlanes (mixColumns1 (Fixslice.subBytes s0)) k1
    let s2 := xorPlanes (mixColumns2 (Fixslice.subBytes s1)) k2
    let s3 := xorPlanes (mixColumns3 (Fixslice.subBytes s2)) k3
    (fun p : Fin 8 ↦ if p.val = 7 then
      mixColumns0 (Fixslice.subBytes s3) p
      else mixColumns0 (Fixslice.subBytes s3) p ^^^ k4 p) =
      batchDelayedPlanes use256 key blocks (4 * (j + 1)) := by
  dsimp only
  have hstep (k : Nat) (hk : k < 4) := batchRoundState_step use256 key blocks (4 * j + k)
    (by omega : 4 * j + k + 1 < (AES16.variant use256).Nr)
  have hm (k : Nat) : (4 * j + k + 1) % 4 = (k + 1) % 4 := by omega
  simp only [batchRoundMix, hm] at hstep
  have h4 : 4 * (j + 1) = 4 * j + 3 + 1 := by omega
  have hs1 := hstep 0 (by decide)
  have hs2 := hstep 1 (by decide)
  have hs3 := hstep 2 (by decide)
  have hs4 := hstep 3 (by decide)
  simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMod] at hs1 hs2 hs3 hs4
  simp only [h4, Nat.add_assoc, Nat.reduceAdd]
  rw [hs1, hs2, hs3]
  simp only [batchDelayedPlanes, Nat.min_eq_left (show 4 * j + 4 ≤ (AES16.variant use256).Nr by omega)]
  rw [← hs4]
  exact (batchDelayed_xor _ _).symm

end AesGcm.Proofs.Machine.CTR.Loop
