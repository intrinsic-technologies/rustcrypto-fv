import AesGcm.Proofs.Machine.Fixslice16.Widening

namespace AesGcm.Proofs.Machine.Fixslice16

theorem projectPlanes_injective {x y : Fixslice.Planes}
    (h : ∀ b : Fin 4, projectPlanes x b = projectPlanes y b) : x = y := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have he := congrArg (fun z ↦ (z p).getLsbD (i / 4)) (h ⟨i % 4, by omega⟩)
  change (projectWord (x p) ⟨i % 4, by omega⟩).getLsbD (i / 4) =
    (projectWord (y p) ⟨i % 4, by omega⟩).getLsbD (i / 4) at he
  rw [getLsbD_projectWord _ _ ⟨i / 4, by omega⟩,
    getLsbD_projectWord _ _ ⟨i / 4, by omega⟩] at he
  simpa only [show 4 * (i / 4) + i % 4 = i by omega] using he

theorem widenPlanes_subBytesNots (x : Planes16) :
    widenPlanes (subBytesNots x) = Fixslice.subBytesNots (widenPlanes x) := by
  funext p
  simp only [subBytesNots, Fixslice.subBytesNots, widenPlanes]
  split
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [getLsbD_widenWord _ ⟨i, hi⟩, BitVec.getLsbD_not,
      hi, show i / 4 < 16 by omega, decide_true, Bool.true_and]
  · rfl

theorem projectPlanes_subBytesNots (x : Fixslice.Planes) (b : Fin 4) :
    projectPlanes (Fixslice.subBytesNots x) b = subBytesNots (projectPlanes x b) := by
  funext p
  simp only [subBytesNots, Fixslice.subBytesNots, projectPlanes]
  split
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [getLsbD_projectWord _ b ⟨i, hi⟩, BitVec.getLsbD_not,
      hi, show 4 * i + b.val < 64 by omega, decide_true, Bool.true_and]
  · rfl

set_option maxHeartbeats 800000 in
theorem projectPlanes_subBytes (x : Fixslice.Planes) (b : Fin 4) :
    projectPlanes (Fixslice.subBytes x) b = subBytes (projectPlanes x b) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (projectWord (Fixslice.subBytesCircuit x p) b).getLsbD i =
    (Fixslice.subBytesCircuit (projectPlanes x b) p).getLsbD i
  rw [getLsbD_projectWord _ b ⟨i, hi⟩, getLsbD_subBytesCircuit, getLsbD_subBytesCircuit]
  simp only [projectPlanes, getLsbD_projectWord _ b ⟨i, hi⟩]

theorem widenPlanes_encodeStandard (x : Standards.NIST.AES.Block) :
    widenPlanes (encodeStandard x) = Fixslice.encodeStandard (fun _ ↦ x) := by
  rw [encodeStandard, widenPlanes_encode]
  rfl

theorem projectPlanes_encodeStandard (x : Fixslice.StandardBlocks) (b : Fin 4) :
    projectPlanes (Fixslice.encodeStandard x) b = encodeStandard (x b) := by
  rw [Fixslice.encodeStandard, projectPlanes_encode]
  rfl

end AesGcm.Proofs.Machine.Fixslice16
