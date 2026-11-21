import AesGcm.Proofs.Machine.Fixslice.Operations
import AesGcm.Proofs.Machine.Fixslice.Sbox
import Standards.NIST.AES.KeyExpansion

namespace AesGcm.Proofs.Machine.KeySchedule

open Standards.NIST.AES AesGcm.Proofs.Machine.Fixslice

def roundKeyBlock (v : Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) : Block :=
  let words := roundKey v (keyExpansion v key) round
  Vector.ofFn fun j ↦ words[j.val / 4][j.val % 4]

def invRowsPow : Nat → Block → Block
  | 0, block => block
  | n + 1, block => invShiftRows (invRowsPow n block)

def compensateRound (round : Nat) (planes : Planes) : Planes :=
  if round = 0 then planes
  else subBytesNots planes

def roundPhase (v : Variant) (round : Nat) : Nat :=
  if round = v.Nr then 0 else round % 4

def expectedKey (v : Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) : Planes :=
  compensateRound round.val (encodeStandard fun _ ↦
    invRowsPow (roundPhase v round.val) (roundKeyBlock v key round))

def scheduleWords (v : Variant) : Nat := 8 * (v.Nr + 1)

def scheduleBytes (v : Variant) : Nat := 64 * (v.Nr + 1)

theorem compensateRound_zero (planes : Planes) : compensateRound 0 planes = planes := by
  simp only [compensateRound, ↓reduceIte]

theorem compensateRound_involutive (round : Nat) (planes : Planes) :
    compensateRound round (compensateRound round planes) = planes := by
  simp only [compensateRound]
  split
  · rfl
  · exact subBytesNots_involutive planes

theorem expectedKey_zero (v : Variant) (key : Vector UInt8 v.keyBytes) :
    expectedKey v key ⟨0, by cases v <;> decide⟩ =
      encodeStandard (fun _ ↦ roundKeyBlock v key ⟨0, by cases v <;> decide⟩) := by
  have h : roundPhase v 0 = 0 := by cases v <;> rfl
  simp only [expectedKey, h, invRowsPow, compensateRound_zero]

theorem decode_expectedKey (v : Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) :
    decodeStandard (compensateRound round.val (expectedKey v key round)) =
      fun _ ↦ invRowsPow (roundPhase v round.val) (roundKeyBlock v key round) := by
  simp only [expectedKey, compensateRound_involutive, decodeStandard_encodeStandard]

theorem roundPhase_final (v : Variant) : roundPhase v v.Nr = 0 := by
  simp only [roundPhase, ↓reduceIte]

theorem expectedKey_final (v : Variant) (key : Vector UInt8 v.keyBytes) :
    expectedKey v key ⟨v.Nr, by omega⟩ = compensateRound v.Nr
      (encodeStandard fun _ ↦ roundKeyBlock v key ⟨v.Nr, by omega⟩) := by
  simp only [expectedKey, roundPhase_final, invRowsPow]

theorem scheduleBytes_eq_words (v : Variant) : scheduleBytes v = 8 * scheduleWords v := by
  simp only [scheduleBytes, scheduleWords]
  omega

end AesGcm.Proofs.Machine.KeySchedule
