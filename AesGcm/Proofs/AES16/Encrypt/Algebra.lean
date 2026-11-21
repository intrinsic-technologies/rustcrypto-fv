import AesGcm.Proofs.AES16.Layout
import AesGcm.Proofs.AES16.MixColumnsAlgebra
import AesGcm.Proofs.Machine.AESCore.Rounds

namespace AesGcm.Proofs.Machine.AES16.Encrypt

open Standards.NIST.AES Fixslice16

def roundState (v : Variant) (key : Vector UInt8 v.keyBytes)
    (input : Standards.NIST.AES.Block) (count : Nat) : Planes16 :=
  projectPlanes (AESCore.phaseEncode count
    (AESCore.encryptRounds (AESCore.cipherKeys v key) count (fun _ ↦ input))) 0

theorem initial_roundState (v : Variant) (key : Vector UInt8 v.keyBytes)
    (input : Standards.NIST.AES.Block) :
    xorPlanes (encodeStandard input) (expectedKey v key ⟨0, by cases v <;> decide⟩) =
      roundState v key input 0 := by
  have h := congrArg (fun x ↦ projectPlanes x 0)
    (AESCore.encryptInitial_expectedKey v key (fun _ ↦ input))
  simpa only [roundState, projectPlanes_xorPlanes, projectPlanes_encodeStandard,
    KeySchedule.projectPlanes_expectedKey, expectedKey] using h

theorem roundState_succ (v : Variant) (key : Vector UInt8 v.keyBytes)
    (input : Standards.NIST.AES.Block) (count : Nat) (hcount : count + 1 < v.Nr)
    (wide : Fixslice.Planes → Fixslice.Planes) (narrow : Planes16 → Planes16)
    (hproject : ∀ x, projectPlanes (wide x) 0 = narrow (projectPlanes x 0))
    (hwide : ∀ x, wide (Fixslice.encode x) = Fixslice.encode
      (Fixslice.mixColumnsBlocks (Fixslice.rotateBlocks 1 ((count + 1) % 4))
        (Fixslice.rotateBlocks 2 (2 * ((count + 1) % 4))) x)) :
    xorPlanes (narrow (subBytes (roundState v key input count)))
      (expectedKey v key ⟨count + 1, by omega⟩) = roundState v key input (count + 1) := by
  have h := congrArg (fun x ↦ projectPlanes x 0)
    (AESCore.encryptRounds_succ_expectedKey v key count hcount wide hwide (fun _ ↦ input))
  simpa only [roundState, projectPlanes_xorPlanes, hproject, projectPlanes_subBytes,
    KeySchedule.projectPlanes_expectedKey, expectedKey] using h

def roundMix (phase : Fin 4) : Planes16 → Planes16 :=
  match phase.val with
  | 0 => mixColumns0
  | 1 => mixColumns1
  | 2 => mixColumns2
  | _ => mixColumns3

private def wideRoundMix (phase : Fin 4) : Fixslice.Planes → Fixslice.Planes :=
  match phase.val with
  | 0 => Fixslice.mixColumns0
  | 1 => Fixslice.mixColumns1
  | 2 => Fixslice.mixColumns2
  | _ => Fixslice.mixColumns3

private theorem project_wideRoundMix (phase : Fin 4) (x : Fixslice.Planes) :
    projectPlanes (wideRoundMix phase x) 0 = roundMix phase (projectPlanes x 0) := by
  have h : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl
  · exact projectPlanes_mixColumns0 x 0
  · exact projectPlanes_mixColumns1 x 0
  · exact projectPlanes_mixColumns2 x 0
  · exact projectPlanes_mixColumns3 x 0

private theorem wideRoundMix_encode (phase : Fin 4) (x : Fixslice.Blocks) :
    wideRoundMix phase (Fixslice.encode x) = Fixslice.encode
      (Fixslice.mixColumnsBlocks (Fixslice.rotateBlocks 1 phase.val)
        (Fixslice.rotateBlocks 2 (2 * phase.val)) x) := by
  have h : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl
  · exact Fixslice.mixColumns0_encode x
  · exact Fixslice.mixColumns1_encode x
  · change Fixslice.mixColumns2 (Fixslice.encode x) = Fixslice.encode
      (Fixslice.mixColumnsBlocks (Fixslice.rotateBlocks 1 2) (Fixslice.rotateBlocks 2 4) x)
    rw [AESCore.rotateBlocks_mod 2 4]
    exact Fixslice.mixColumns2_encode x
  · change Fixslice.mixColumns3 (Fixslice.encode x) = Fixslice.encode
      (Fixslice.mixColumnsBlocks (Fixslice.rotateBlocks 1 3) (Fixslice.rotateBlocks 2 6) x)
    rw [AESCore.rotateBlocks_mod 2 6]
    exact Fixslice.mixColumns3_encode x

theorem roundState_next (v : Variant) (key : Vector UInt8 v.keyBytes)
    (input : Standards.NIST.AES.Block) (count : Nat) (hcount : count + 1 < v.Nr) :
    xorPlanes (roundMix ⟨(count + 1) % 4, by omega⟩
      (subBytes (roundState v key input count)))
      (expectedKey v key ⟨count + 1, by omega⟩) = roundState v key input (count + 1) :=
  roundState_succ v key input count hcount _ _
    (project_wideRoundMix ⟨(count + 1) % 4, by omega⟩)
    (wideRoundMix_encode ⟨(count + 1) % 4, by omega⟩)

theorem last_roundState (use256 : Bool) (key : Vector UInt8 (variant use256).keyBytes)
    (input : Standards.NIST.AES.Block) :
    xorPlanes (subBytes (shiftRows2
      (roundState (variant use256) key input ((variant use256).Nr - 1))))
      (expectedKey (variant use256) key ⟨(variant use256).Nr, by omega⟩) =
      encodeStandard (cipher (variant use256) key input) := by
  have h := congrArg (fun x ↦ projectPlanes x 0)
    (AESCore.encryptLast_expectedKey (variant use256) key
      (AESCore.encryptRounds (AESCore.cipherKeys (variant use256) key)
        ((variant use256).Nr - 1) (fun _ ↦ input)))
  rw [AESCore.encryptRounds_correct] at h
  cases use256
  all_goals
    change projectPlanes (Fixslice.xorPlanes
      (Fixslice.subBytes (Fixslice.shiftRows2 _)) _) 0 = _ at h
    simpa only [roundState, projectPlanes_xorPlanes, projectPlanes_subBytes,
      projectPlanes_shiftRows2, KeySchedule.projectPlanes_expectedKey, expectedKey,
      projectPlanes_encodeStandard] using h

end AesGcm.Proofs.Machine.AES16.Encrypt
