import K256.Proofs.Sec1.LIR.Labels
import K256.Proofs.Generate.LIR.Labels
import Lean.Elab.Tactic

namespace K256.Proofs.Generate.Serialize

open Lean Elab Tactic

scoped elab "same_target" : tactic => do
  let tag ← (← getMainGoal).getTag
  let label := Name.str ``LIR.Label tag.getString!
  let val := mkIdent label
  evalTactic (← `(tactic| exact some $val))

private def targets0 : Sec1.LIR.Label.G0 → Option LIR.Label
  | .l100a20 => some .l100a20
  | .l1148d0 => some .l1148d0
  | .l114930 => some .l114930
  | .l114a10 => some .l114a10
  | _ => none

private def targets1 : Sec1.LIR.Label.G1 → Option LIR.Label
  | _ => none

private def targets2 : Sec1.LIR.Label.G2 → Option LIR.Label := by
  intro label
  cases label
  case l120298 => exact none
  case l12031e => exact none
  case l120330 => exact none
  case l1205b0 => exact none
  case l120653 => exact none
  case l12065f => exact none
  case l120d03 => exact none
  case l120d83 => exact none
  case l120dff => exact none
  case l120e0b => exact none
  case l120e17 => exact none
  case l120e9b => exact none
  case l120f13 => exact none
  case l121480 => exact none
  case l1214a0 => exact none
  case l1214ae => exact none
  case l1214b5 => exact none
  case l1214b9 => exact none
  case l1214bb => exact none
  case l1214c0 => exact none
  case l1214ce => exact none
  case l1214d0 => exact none
  case l1214d8 => exact none
  case l1214f3 => exact none
  case l121502 => exact none
  case l121599 => exact none
  case l1215a9 => exact none
  case l1215d2 => exact none
  all_goals same_target

private def targets3 : Sec1.LIR.Label.G3 → Option LIR.Label := by
  intro label
  cases label
  all_goals same_target

private def targets4 : Sec1.LIR.Label.G4 → Option LIR.Label := by
  intro label
  cases label
  all_goals same_target

private def targets5 : Sec1.LIR.Label.G5 → Option LIR.Label := by
  intro label
  cases label
  all_goals same_target

private def targets6 : Sec1.LIR.Label.G6 → Option LIR.Label := by
  intro label
  cases label
  all_goals same_target

private def targets7 : Sec1.LIR.Label.G7 → Option LIR.Label := by
  intro label
  cases label
  all_goals same_target

private def targets8 : Sec1.LIR.Label.G8 → Option LIR.Label := by
  intro label
  cases label
  all_goals same_target

private def targets9 : Sec1.LIR.Label.G9 → Option LIR.Label := by
  intro label
  cases label
  case l128910 => exact none
  case l12892f => exact none
  all_goals same_target

private def targets10 : Sec1.LIR.Label.G10 → Option LIR.Label
  | .l128b20 => some .l128b20
  | .l128b81 => some .l128b81
  | .l128b93 => some .l128b93
  | .l128bb1 => some .l128bb1
  | .l128bbd => some .l128bbd
  | .l128bdc => some .l128bdc
  | .l128be2 => some .l128be2
  | .l128be7 => some .l128be7
  | .l128bf4 => some .l128bf4
  | .l128bfa => some .l128bfa
  | .l128c09 => some .l128c09
  | .l128c0e => some .l128c0e
  | .l128c12 => some .l128c12
  | .l128c20 => some .l128c20
  | .l128c63 => some .l128c63
  | .l128c68 => some .l128c68
  | .l128c70 => some .l128c70
  | .l128c85 => some .l128c85
  | .l128c97 => some .l128c97
  | .l128ca8 => some .l128ca8
  | .l128cd0 => some .l128cd0
  | .l128d06 => some .l128d06
  | .l128d12 => some .l128d12
  | .l128d20 => some .l128d20
  | .l128d25 => some .l128d25
  | .l128d37 => some .l128d37
  | .l128e28 => some .l128e28
  | _ => none

private def targets11 : Sec1.LIR.Label.G11 → Option LIR.Label
  | .l129560 => some .l129560
  | .l129594 => some .l129594
  | .l1295a0 => some .l1295a0
  | _ => none

private def targets12 : Sec1.LIR.Label.G12 → Option LIR.Label := by
  intro label
  cases label
  case l129c56 => exact none
  all_goals same_target

private def targets13 : Sec1.LIR.Label.G13 → Option LIR.Label
  | .l129d39 => some .l129d39
  | .l129d5f => some .l129d5f
  | .l12a820 => some .l12a820
  | _ => none

def sharedTarget : Sec1.LIR.Label → Option LIR.Label
  | .g0 l => targets0 l
  | .g1 l => targets1 l
  | .g2 l => targets2 l
  | .g3 l => targets3 l
  | .g4 l => targets4 l
  | .g5 l => targets5 l
  | .g6 l => targets6 l
  | .g7 l => targets7 l
  | .g8 l => targets8 l
  | .g9 l => targets9 l
  | .g10 l => targets10 l
  | .g11 l => targets11 l
  | .g12 l => targets12 l
  | .g13 l => targets13 l

end K256.Proofs.Generate.Serialize
