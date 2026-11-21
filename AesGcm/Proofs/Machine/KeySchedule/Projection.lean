import AesGcm.Proofs.Machine.KeySchedule.Layout
import AesGcm.Proofs.Machine.Fixslice16.Projection

namespace AesGcm.Proofs.Machine.KeySchedule
open Standards.NIST.AES

theorem widenPlanes_expectedKey (v : Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) :
    Fixslice16.widenPlanes
      (let planes := Fixslice16.encodeStandard
        (invRowsPow (roundPhase v round.val) (roundKeyBlock v key round))
       if round.val = 0 then planes else Fixslice16.subBytesNots planes) =
      expectedKey v key round := by
  simp only [expectedKey, compensateRound]
  split
  · exact Fixslice16.widenPlanes_encodeStandard _
  · rw [Fixslice16.widenPlanes_subBytesNots, Fixslice16.widenPlanes_encodeStandard]

theorem projectPlanes_expectedKey (v : Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) (b : Fin 4) :
    Fixslice16.projectPlanes (expectedKey v key round) b =
      (let planes := Fixslice16.encodeStandard
        (invRowsPow (roundPhase v round.val) (roundKeyBlock v key round))
       if round.val = 0 then planes else Fixslice16.subBytesNots planes) := by
  rw [← widenPlanes_expectedKey v key round, Fixslice16.projectPlanes_widenPlanes]

end AesGcm.Proofs.Machine.KeySchedule
