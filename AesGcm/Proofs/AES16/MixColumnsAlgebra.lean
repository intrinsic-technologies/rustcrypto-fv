import AesGcm.Proofs.AES16.Linear
import AesGcm.Proofs.Machine.Fixslice.MixColumns

namespace AesGcm.Proofs.Machine.AES16

open Fixslice16

def xtimePlanes (a : Planes16) : Planes16 := fun p ↦
  match p.val with
  | 0 => a 7
  | 1 => a 0 ^^^ a 7
  | 2 => a 1
  | 3 => a 2 ^^^ a 7
  | 4 => a 3 ^^^ a 7
  | 5 => a 4
  | 6 => a 5
  | _ => a 6

def mapPlanes (f : BitVec 16 → BitVec 16) (a : Planes16) : Planes16 := fun p ↦ f (a p)

def mixColumnsCircuit (first second : BitVec 16 → BitVec 16) (a : Planes16) : Planes16 :=
  let b := mapPlanes first a
  let c := xorPlanes a b
  xorPlanes (xorPlanes b (xtimePlanes c)) (mapPlanes second c)

def mixColumns0 := mixColumnsCircuit rotateRows1 rotateRows2
def mixColumns1 := mixColumnsCircuit rotateRowsAndColumns11 rotateRowsAndColumns22
def mixColumns2 := mixColumnsCircuit rotateRowsAndColumns12 rotateRows2
def mixColumns3 := mixColumnsCircuit rotateRowsAndColumns13 rotateRowsAndColumns22

theorem projectWord_xor (x y : BitVec 64) (b : Fin 4) :
    projectWord (x ^^^ y) b = projectWord x b ^^^ projectWord y b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, getLsbD_projectWord _ b ⟨i, hi⟩]

theorem projectPlanes_xorPlanes (x y : Fixslice.Planes) (b : Fin 4) :
    projectPlanes (Fixslice.xorPlanes x y) b =
      xorPlanes (projectPlanes x b) (projectPlanes y b) := by
  funext p
  exact projectWord_xor (x p) (y p) b

theorem projectPlanes_xtimePlanes (x : Fixslice.Planes) (b : Fin 4) :
    projectPlanes (Fixslice.xtimePlanes x) b = xtimePlanes (projectPlanes x b) := by
  funext p
  have hp : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by
    have := p.isLt
    omega
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | exact projectWord_xor _ _ _

theorem projectPlanes_mapPlanes (f : BitVec 64 → BitVec 64) (g : BitVec 16 → BitVec 16)
    (h : ∀ x b, projectWord (f x) b = g (projectWord x b))
    (x : Fixslice.Planes) (b : Fin 4) :
    projectPlanes (Fixslice.mapPlanes f x) b = mapPlanes g (projectPlanes x b) := by
  funext p
  exact h (x p) b

theorem projectPlanes_mixColumnsCircuit
    (f₁ f₂ : BitVec 64 → BitVec 64) (g₁ g₂ : BitVec 16 → BitVec 16)
    (h₁ : ∀ x b, projectWord (f₁ x) b = g₁ (projectWord x b))
    (h₂ : ∀ x b, projectWord (f₂ x) b = g₂ (projectWord x b))
    (x : Fixslice.Planes) (b : Fin 4) :
    projectPlanes (Fixslice.mixColumnsCircuit f₁ f₂ x) b =
      mixColumnsCircuit g₁ g₂ (projectPlanes x b) := by
  simp only [Fixslice.mixColumnsCircuit, mixColumnsCircuit,
    projectPlanes_xorPlanes, projectPlanes_xtimePlanes,
    projectPlanes_mapPlanes f₁ g₁ h₁, projectPlanes_mapPlanes f₂ g₂ h₂]

theorem projectPlanes_mixColumns0 (x : Fixslice.Planes) (b : Fin 4) :
    projectPlanes (Fixslice.mixColumns0 x) b = mixColumns0 (projectPlanes x b) :=
  projectPlanes_mixColumnsCircuit _ _ _ _ projectWord_rotateRows1
    projectWord_rotateRows2 x b

theorem mixColumns0_encode (x : Block) :
    mixColumns0 (encode x) =
      encode (Fixslice.mixColumnsBlocks (Fixslice.rotateBlocks 1 0)
        (Fixslice.rotateBlocks 2 0) (Fixslice.broadcast x) 0) := by
  have h := congrArg (fun a ↦ projectPlanes a 0)
    (Fixslice.mixColumns0_encode (Fixslice.broadcast x))
  simpa only [projectPlanes_mixColumns0, projectPlanes_encode, Fixslice.broadcast] using h

theorem projectPlanes_mixColumns1 (x : Fixslice.Planes) (b : Fin 4) :
    projectPlanes (Fixslice.mixColumns1 x) b = mixColumns1 (projectPlanes x b) :=
  projectPlanes_mixColumnsCircuit _ _ _ _ projectWord_rotateRowsAndColumns11
    projectWord_rotateRowsAndColumns22 x b

theorem mixColumns1_encode (x : Block) :
    mixColumns1 (encode x) =
      encode (Fixslice.mixColumnsBlocks (Fixslice.rotateBlocks 1 1)
        (Fixslice.rotateBlocks 2 2) (Fixslice.broadcast x) 0) := by
  have h := congrArg (fun a ↦ projectPlanes a 0)
    (Fixslice.mixColumns1_encode (Fixslice.broadcast x))
  simpa only [projectPlanes_mixColumns1, projectPlanes_encode, Fixslice.broadcast] using h

theorem projectPlanes_mixColumns2 (x : Fixslice.Planes) (b : Fin 4) :
    projectPlanes (Fixslice.mixColumns2 x) b = mixColumns2 (projectPlanes x b) :=
  projectPlanes_mixColumnsCircuit _ _ _ _ projectWord_rotateRowsAndColumns12
    projectWord_rotateRows2 x b

theorem mixColumns2_encode (x : Block) :
    mixColumns2 (encode x) =
      encode (Fixslice.mixColumnsBlocks (Fixslice.rotateBlocks 1 2)
        (Fixslice.rotateBlocks 2 0) (Fixslice.broadcast x) 0) := by
  have h := congrArg (fun a ↦ projectPlanes a 0)
    (Fixslice.mixColumns2_encode (Fixslice.broadcast x))
  simpa only [projectPlanes_mixColumns2, projectPlanes_encode, Fixslice.broadcast] using h

theorem projectPlanes_mixColumns3 (x : Fixslice.Planes) (b : Fin 4) :
    projectPlanes (Fixslice.mixColumns3 x) b = mixColumns3 (projectPlanes x b) :=
  projectPlanes_mixColumnsCircuit _ _ _ _ projectWord_rotateRowsAndColumns13
    projectWord_rotateRowsAndColumns22 x b

theorem mixColumns3_encode (x : Block) :
    mixColumns3 (encode x) =
      encode (Fixslice.mixColumnsBlocks (Fixslice.rotateBlocks 1 3)
        (Fixslice.rotateBlocks 2 2) (Fixslice.broadcast x) 0) := by
  have h := congrArg (fun a ↦ projectPlanes a 0)
    (Fixslice.mixColumns3_encode (Fixslice.broadcast x))
  simpa only [projectPlanes_mixColumns3, projectPlanes_encode, Fixslice.broadcast] using h

end AesGcm.Proofs.Machine.AES16
