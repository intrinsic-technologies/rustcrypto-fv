import AesGcm.Proofs.Machine.AESCore.Phase
import AesGcm.Proofs.Machine.AESCore.Standard

namespace AesGcm.Proofs.Machine.AESCore

open Standards.NIST.AES AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.KeySchedule

theorem xorPlanes_subBytesNots (a b : Planes) :
    xorPlanes (subBytesNots a) (subBytesNots b) = xorPlanes a b := by
  funext p
  simp only [xorPlanes, subBytesNots]
  split
  · simp only [← BitVec.not_xor_left, ← BitVec.not_xor_right, BitVec.not_not]
  · rfl

theorem xorPlanes_subBytesNots_right (a b : Planes) :
    xorPlanes a (subBytesNots b) = subBytesNots (xorPlanes a b) := by
  funext p
  simp only [xorPlanes, subBytesNots]
  split
  · exact BitVec.not_xor_right.symm
  · rfl

theorem phaseEncode_addRoundKey (round : Nat) (x : StandardBlocks) (key : RoundKey) :
    phaseEncode round (fun b ↦ addRoundKey (x b) key) =
      xorPlanes (phaseEncode round x)
        (phaseEncode round (fun _ ↦ Vector.ofFn fun j ↦ key[j.val / 4][j.val % 4])) := by
  simp only [phaseEncode, encodeStandard]
  rw [← encode_xorBlocks]
  apply congrArg encode
  funext b j
  simp only [fromStandard, phase, invRowsPow_eq_shiftRowsBy, shiftRowsBy,
    Vector.getElem_ofFn, Fin.getElem_fin, addRoundKey, UInt8.toBitVec_xor, xorBlocks]

theorem subBytes_encodeStandard (x : StandardBlocks) :
    Fixslice.subBytes (encodeStandard x) =
      subBytesNots (encodeStandard (fun b ↦ Standards.NIST.AES.subBytes (x b))) := by
  rw [← subBytesNots_involutive (Fixslice.subBytes (encodeStandard x))]
  congr 1
  rw [encodeStandard, subBytesNots_subBytes_encode]
  apply congrArg encode
  funext b j
  simp only [fromStandard, Standards.NIST.AES.subBytes, Vector.getElem_map,
    UInt8.ofBitVec_toBitVec]
theorem encryptStep_phase (round : Nat) (hround : 0 < round) (mc : Planes → Planes)
    (hmc : ∀ x, mc (encode x) = encode
      (mixColumnsBlocks (rotateBlocks 1 (round % 4))
        (rotateBlocks 2 (2 * (round % 4))) x))
    (x : StandardBlocks) (key : RoundKey) :
    xorPlanes (mc (Fixslice.subBytes (phaseEncode (round - 1) x)))
      (subBytesNots (phaseEncode round
        (fun _ ↦ Vector.ofFn fun j ↦ key[j.val / 4][j.val % 4]))) =
      phaseEncode round (fun b ↦ addRoundKey
        (Standards.NIST.AES.mixColumns
          (shiftRows (Standards.NIST.AES.subBytes (x b)))) key) := by
  have hmask (a : Planes) : mc (subBytesNots a) = subBytesNots (mc a) := by
    rw [← encode_decode a, subBytesNots_encode, hmc, hmc, subBytesNots_encode]
    apply congrArg encode
    exact mixColumnsBlocks_xor63 (round % 4) (decode a)
  have hphase (y : StandardBlocks) : mc (phaseEncode round y) =
      phaseEncode round (fun b ↦ Standards.NIST.AES.mixColumns (y b)) := by
    simp only [phaseEncode, encodeStandard, hmc]
    apply congrArg encode
    simpa only [Fin.val_mk, phase_mod] using
      mixColumnsBlocks_phase ⟨round % 4, by omega⟩ y
  have hp := phase_succ_shiftRows (round - 1) x
  rw [show round - 1 + 1 = round by omega] at hp
  change xorPlanes (mc (Fixslice.subBytes (encodeStandard (phase (round - 1) x)))) _ = _
  rw [← hp, subBytes_encodeStandard, ← phase_subBytes]
  change xorPlanes
    (mc (subBytesNots (phaseEncode round
      (fun b ↦ Standards.NIST.AES.subBytes (shiftRows (x b)))))) _ = _
  rw [hmask, hphase, xorPlanes_subBytesNots, ← phaseEncode_addRoundKey]
  apply congrArg (phaseEncode round)
  funext b
  apply congrArg (fun y ↦ addRoundKey (Standards.NIST.AES.mixColumns y) key)
  simpa only [shiftRowsBy_one] using (shiftRowsBy_subBytes 1 (x b)).symm
theorem encryptLast_phase (v : Variant) (x : StandardBlocks) (key : RoundKey) :
    xorPlanes
      (Fixslice.subBytes (match v with
        | .aes192 => phaseEncode (v.Nr - 1) x
        | _ => shiftRows2 (phaseEncode (v.Nr - 1) x)))
      (subBytesNots (encodeStandard
        (fun _ ↦ Vector.ofFn fun j ↦ key[j.val / 4][j.val % 4]))) =
      encodeStandard (fun b ↦ addRoundKey
        (shiftRows (Standards.NIST.AES.subBytes (x b))) key) := by
  have hstart : (match v with
      | .aes192 => phaseEncode (v.Nr - 1) x
      | _ => shiftRows2 (phaseEncode (v.Nr - 1) x)) =
        encodeStandard (fun b ↦ shiftRows (x b)) := by
    cases v <;>
      simp only [Variant.Nr, Nat.reduceSub, phaseEncode, phase, Nat.reduceMod,
        invRowsPow_eq_shiftRowsBy, shiftRows2_encodeStandard, shiftRowsBy_add]
    all_goals
      apply congrArg encodeStandard
      funext b
      simp only [phase, Nat.reduceMod, invRowsPow_eq_shiftRowsBy, ← shiftRowsBy_one]
      rw [← shiftRowsBy_mod]
  rw [hstart, subBytes_encodeStandard]
  rw [xorPlanes_subBytesNots]
  change xorPlanes (phaseEncode 0 _) (phaseEncode 0 _) = _
  apply Eq.trans (phaseEncode_addRoundKey 0 _ key).symm
  rw [phaseEncode_zero]
  apply congrArg encodeStandard
  funext b
  apply congrArg (fun y ↦ addRoundKey y key)
  change Standards.NIST.AES.subBytes (shiftRows (x b)) =
    shiftRows (Standards.NIST.AES.subBytes (x b))
  simpa only [shiftRowsBy_one] using (shiftRowsBy_subBytes 1 (x b)).symm
theorem roundKeyBlock_cipherKeys (v : Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) :
    roundKeyBlock v key round =
      Vector.ofFn fun j ↦ (cipherKeys v key round.val)[j.val / 4][j.val % 4] := by
  simp only [roundKeyBlock, cipherKeys, Nat.min_eq_left (Nat.le_of_lt_succ round.isLt)]

theorem expectedKey_middle (v : Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) (hzero : 0 < round.val) (hfinal : round.val < v.Nr) :
    expectedKey v key round = subBytesNots (phaseEncode round.val
      (fun _ ↦ Vector.ofFn fun j ↦ (cipherKeys v key round.val)[j.val / 4][j.val % 4])) := by
  simp only [expectedKey, roundPhase, ite_eq_right (Nat.ne_of_lt hfinal), compensateRound,
    ite_eq_right (Nat.ne_of_gt hzero)]
  rw [roundKeyBlock_cipherKeys]
  rfl

theorem expectedKey_last (v : Variant) (key : Vector UInt8 v.keyBytes) :
    expectedKey v key ⟨v.Nr, by omega⟩ = subBytesNots (encodeStandard
      (fun _ ↦ Vector.ofFn fun j ↦ (cipherKeys v key v.Nr)[j.val / 4][j.val % 4])) := by
  rw [expectedKey_final, compensateRound,
    ite_eq_right (show v.Nr ≠ 0 by cases v <;> decide), roundKeyBlock_cipherKeys]

theorem encryptInitial_expectedKey (v : Variant) (key : Vector UInt8 v.keyBytes)
    (input : StandardBlocks) :
    xorPlanes (encodeStandard input) (expectedKey v key ⟨0, by cases v <;> decide⟩) =
      phaseEncode 0 (encryptRounds (cipherKeys v key) 0 input) := by
  rw [expectedKey_zero, roundKeyBlock_cipherKeys, encryptRounds_zero]
  exact (phaseEncode_addRoundKey 0 input (cipherKeys v key 0)).symm

theorem encryptStep_expectedKey (v : Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) (hzero : 0 < round.val) (hfinal : round.val < v.Nr)
    (mc : Planes → Planes)
    (hmc : ∀ x, mc (encode x) = encode
      (mixColumnsBlocks (rotateBlocks 1 (round.val % 4))
        (rotateBlocks 2 (2 * (round.val % 4))) x)) (x : StandardBlocks) :
    xorPlanes (mc (Fixslice.subBytes (phaseEncode (round.val - 1) x)))
      (expectedKey v key round) =
        phaseEncode round.val (encryptRound (cipherKeys v key) round.val x) := by
  rw [expectedKey_middle v key round hzero hfinal]
  exact encryptStep_phase round.val hzero mc hmc x (cipherKeys v key round.val)

theorem encryptLast_expectedKey (v : Variant) (key : Vector UInt8 v.keyBytes)
    (x : StandardBlocks) :
    xorPlanes (Fixslice.subBytes (match v with
        | .aes192 => phaseEncode (v.Nr - 1) x
        | _ => shiftRows2 (phaseEncode (v.Nr - 1) x)))
      (expectedKey v key ⟨v.Nr, by omega⟩) =
        encodeStandard (encryptLast (cipherKeys v key) v.Nr x) := by
  rw [expectedKey_last]
  cases v with
  | aes128 => exact encryptLast_phase .aes128 x (cipherKeys .aes128 key 10)
  | aes192 => exact encryptLast_phase .aes192 x (cipherKeys .aes192 key 12)
  | aes256 => exact encryptLast_phase .aes256 x (cipherKeys .aes256 key 14)

theorem encryptRounds_succ_expectedKey (v : Variant) (key : Vector UInt8 v.keyBytes)
    (count : Nat) (hcount : count + 1 < v.Nr) (mc : Planes → Planes)
    (hmc : ∀ x, mc (encode x) = encode
      (mixColumnsBlocks (rotateBlocks 1 ((count + 1) % 4))
        (rotateBlocks 2 (2 * ((count + 1) % 4))) x)) (input : StandardBlocks) :
    xorPlanes (mc (Fixslice.subBytes
      (phaseEncode count (encryptRounds (cipherKeys v key) count input))))
      (expectedKey v key ⟨count + 1, by omega⟩) =
      phaseEncode (count + 1) (encryptRounds (cipherKeys v key) (count + 1) input) := by
  simpa only [Fin.val_mk, Nat.add_sub_cancel, encryptRounds_succ] using
    encryptStep_expectedKey v key ⟨count + 1, by omega⟩
      (show 0 < count + 1 from Nat.zero_lt_succ count) hcount mc hmc
      (encryptRounds (cipherKeys v key) count input)

end AesGcm.Proofs.Machine.AESCore
