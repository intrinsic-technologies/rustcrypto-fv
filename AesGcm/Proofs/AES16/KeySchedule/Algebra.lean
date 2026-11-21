import AesGcm.Proofs.AES16.KeySchedule.Columns16
import AesGcm.Proofs.AES16.Layout
import AesGcm.Proofs.Machine.AESCore.Phase

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open Standards.NIST.AES Fixslice16

def adjustRows (phase : Nat) (planes : Planes16) : Planes16 :=
  match phase with
  | 0 => planes
  | 1 => shiftRows3 planes
  | 2 => shiftRows2 planes
  | _ => shiftRows1 planes

theorem encode_invRowsPow (phase : Fin 4) (block : Standards.NIST.AES.Block) :
    encodeStandard (Machine.KeySchedule.invRowsPow phase.val block) =
      adjustRows phase.val (encodeStandard block) := by
  have h64 : Fixslice.encodeStandard (fun _ ↦ Machine.KeySchedule.invRowsPow phase.val block) =
      (match phase.val with
      | 0 => Fixslice.encodeStandard (fun _ ↦ block)
      | 1 => Fixslice.shiftRows3 (Fixslice.encodeStandard (fun _ ↦ block))
      | 2 => Fixslice.shiftRows2 (Fixslice.encodeStandard (fun _ ↦ block))
      | _ => Fixslice.shiftRows1 (Fixslice.encodeStandard (fun _ ↦ block))) := by
    have h : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 := by
      have := phase.isLt
      omega
    rcases h with rfl | rfl | rfl | rfl
    · rfl
    · exact (congrArg (fun t : Standards.NIST.AES.Block ↦ Fixslice.encodeStandard (fun _ ↦ t))
        (AESCore.invRowsPow_eq_shiftRowsBy 1 block)).trans
        (AESCore.shiftRows3_encodeStandard (fun _ ↦ block)).symm
    · exact (congrArg (fun t : Standards.NIST.AES.Block ↦ Fixslice.encodeStandard (fun _ ↦ t))
        ((AESCore.invRowsPow_eq_shiftRowsBy 2 block).trans
          (AESCore.shiftRowsBy_mod 6 block).symm)).trans
        (AESCore.shiftRows2_encodeStandard (fun _ ↦ block)).symm
    · exact (congrArg (fun t : Standards.NIST.AES.Block ↦ Fixslice.encodeStandard (fun _ ↦ t))
        ((AESCore.invRowsPow_eq_shiftRowsBy 3 block).trans
          (AESCore.shiftRowsBy_mod 9 block).symm)).trans
        (AESCore.shiftRows1_encodeStandard (fun _ ↦ block)).symm
  have h := congrArg (fun p ↦ projectPlanes p 0) h64
  rw [projectPlanes_encodeStandard] at h
  have hp : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 := by
    have := phase.isLt
    omega
  rcases hp with rfl | rfl | rfl | rfl
  all_goals simpa only [adjustRows, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.reduceFinMk,
    projectPlanes_shiftRows1, projectPlanes_shiftRows2, projectPlanes_shiftRows3,
    projectPlanes_encodeStandard] using h

def adjustKey (v : Variant) (round : Nat) (planes : Planes16) : Planes16 :=
  let shifted := adjustRows (Machine.KeySchedule.roundPhase v round) planes
  if round = 0 then shifted else subBytesNots shifted

theorem adjustKey_encode (v : Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) :
    adjustKey v round.val (encodeStandard (Machine.KeySchedule.roundKeyBlock v key round)) =
      AES16.expectedKey v key round := by
  have hp : Machine.KeySchedule.roundPhase v round.val < 4 := by
    unfold Machine.KeySchedule.roundPhase
    split <;> omega
  simp only [adjustKey, AES16.expectedKey,
    encode_invRowsPow ⟨Machine.KeySchedule.roundPhase v round.val, hp⟩]

open X86 X86.Machine X86Proofs X86Proofs.Refine

theorem memoryBlock_roundKeyBlock_initial (v : Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) (hi : 4 * (round.val + 1) ≤ v.Nk)
    {mem : Ram} {src : BitVec 64}
    (hkey : ∀ i : Fin v.keyBytes, mem[src + BitVec.ofNat 64 i.val]? = some key[i.val]) :
    Fixslice.memoryBlock mem (src + BitVec.ofNat 64 (16 * round.val)) =
      fromStandard (Machine.KeySchedule.roundKeyBlock v key round) := by
  rw [Machine.KeySchedule.roundKeyBlock_initial v key round hi]
  funext j
  have hb := hkey ⟨16 * round.val + j.val, by
    have := j.isLt
    unfold Variant.keyBytes
    omega⟩
  simp only [BitVec.ofNat_add] at hb
  simp only [Fixslice.memoryBlock, fromStandard, Vector.getElem_ofFn, memByte,
    PhysicalMemory.read, BitVec.add_assoc, hb, Option.getD_some]

end AesGcm.Proofs.Machine.AES16.KeySchedule
