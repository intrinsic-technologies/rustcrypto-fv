import AesGcm.Proofs.Machine.Fixslice16.Projection
import AesGcm.Proofs.AES16.KeySchedule.RoundKeys
import AesGcm.Proofs.AES16.KeySchedule.Projection

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open Fixslice16

def xorColumnsWord (previous substituted : BitVec 16) (rotation : Nat) : BitVec 16 :=
  let rk := previous ^^^ (0x1111 &&& substituted.rotateRight rotation)
  rk ^^^ (0xeeee &&& (rk <<< 1)) ^^^ (0xcccc &&& (rk <<< 2)) ^^^
    (0x8888 &&& (rk <<< 3))

def xorColumns (previous substituted : Planes16) (rotation : Nat) : Planes16 :=
  fun p ↦ xorColumnsWord (previous p) (substituted p) rotation

theorem projectWord_xorColumnsWord (previous substituted : BitVec 64) (b : Fin 4)
    (rotation : Nat) :
    projectWord (Machine.KeySchedule.xorColumnsWord previous substituted (4 * rotation)) b =
      xorColumnsWord (projectWord previous b) (projectWord substituted b) rotation := by
  have hm : ∀ b : Fin 4,
      projectWord (Fixslice.uniformRow 0x03) b = 0x1111 ∧
      projectWord (Fixslice.uniformRow 0xfc) b = 0xeeee ∧
      projectWord (Fixslice.uniformRow 0xf0) b = 0xcccc ∧
      projectWord (Fixslice.uniformRow 0xc0) b = 0x8888 := by decide +kernel
  rcases hm b with ⟨hm0, hm1, hm2, hm3⟩
  simp only [Machine.KeySchedule.xorColumnsWord, xorColumnsWord, projectWord_xor,
    projectWord_and, hm0, hm1, hm2, hm3, projectWord_rotateRight,
    projectWord_shiftLeft _ b 1, projectWord_shiftLeft _ b 2, projectWord_shiftLeft _ b 3]
  rfl

theorem projectPlanes_xorColumns (previous substituted : Fixslice.Planes) (b : Fin 4)
    (rotation : Nat) :
    projectPlanes (Machine.KeySchedule.xorColumns previous substituted (4 * rotation)) b =
      xorColumns (projectPlanes previous b) (projectPlanes substituted b) rotation := by
  funext p
  exact projectWord_xorColumnsWord (previous p) (substituted p) b rotation

open Standards.NIST.AES

theorem xorColumns_roundKeyBlock (v : Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) (hv : v ≠ .aes192) (hstart : v.Nk ≤ 4 * round.val) :
    let boundary := 4 * round.val % v.Nk = 0
    let previous := Machine.KeySchedule.roundKeyBlock v key
      ⟨round.val - 1, by have := round.isLt; omega⟩
    let back := Machine.KeySchedule.roundKeyBlock v key
      ⟨round.val - v.Nk / 4, by have := round.isLt; omega⟩
    let c := if boundary then (rcon (4 * round.val / v.Nk))[0] else 0
    xorColumns (encodeStandard back)
      (fun p ↦ encodeStandard (subBytes previous) p ^^^
        (if c.toBitVec.getLsbD p.val then (0x80 : BitVec 16) else 0))
      (if boundary then 7 else 3) =
        encodeStandard (Machine.KeySchedule.roundKeyBlock v key round) := by
  have h := congrArg (fun x ↦ projectPlanes x 0)
    (Machine.KeySchedule.xorColumns_roundKeyBlock v key round hv hstart)
  dsimp only at h ⊢
  have hm : projectWord (0xf0000000 : BitVec 64) 0 = 0x80 := by decide +kernel
  have hz : projectWord (0 : BitVec 64) 0 = 0 := by decide +kernel
  have hrot : (if 4 * round.val % v.Nk = 0 then 28 else 12) =
      4 * (if 4 * round.val % v.Nk = 0 then 7 else 3) := by split <;> rfl
  rw [hrot, projectPlanes_xorColumns, projectPlanes_encodeStandard,
    projectPlanes_encodeStandard] at h
  have hp (x : Standards.NIST.AES.Block) (c : UInt8) :
      projectPlanes (fun p ↦ Fixslice.encodeStandard (fun _ ↦ x) p ^^^
        (if c.toBitVec.getLsbD p.val then (0xf0000000 : BitVec 64) else 0)) 0 =
      fun p ↦ encodeStandard x p ^^^
        (if c.toBitVec.getLsbD p.val then (0x80 : BitVec 16) else 0) := by
    funext p
    change projectWord (_ ^^^ _) 0 = _
    rw [projectWord_xor]
    change projectPlanes (Fixslice.encodeStandard (fun _ ↦ x)) 0 p ^^^ _ = _
    rw [projectPlanes_encodeStandard]
    split <;> simp only [hm, hz]
  simpa only [hp] using h

end AesGcm.Proofs.Machine.AES16.KeySchedule
