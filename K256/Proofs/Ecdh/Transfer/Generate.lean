import K256.Proofs.Ecdh.LIR.Program
import K256.Proofs.Generate.LIR.Program
import K256.Proofs.Generate.Serialize.Transfer.Relabel

namespace K256.Proofs.Ecdh.Transfer

open Lean Elab Tactic K256.Proofs.Generate.Serialize

local elab "generate_label" : tactic => do
  let tag ← (← getMainGoal).getTag
  let target := Name.str ``LIR.Label tag.getString!
  if (← getEnv).contains target then
    let label := mkIdent target
    evalTactic (← `(tactic| exact some $label))
  else
    evalTactic (← `(tactic| exact none))

def generateTarget : Generate.LIR.Label → Option LIR.Label := by
  intro a
  cases a <;> rename_i l <;> cases l <;> generate_label

def merged : CFG.Program Lift.Op LIR.Label Lift.signature Lift.Reg.count where
  blocks
    | .l11f77b => Relabel.block (fun a => (generateTarget a).getD .l101660)
        (Generate.LIR.program.blocks .l11f77b)
    | l => LIR.program.blocks l

local elab "relabel_chunks " label:ident " through " last:num : tactic => do
  let stem := label.getId.toString
  let h := mkIdent `relabeled
  for offset in [:last.getNat + 1] do
    let i := last.getNat - offset
    let name := if i = 0 then stem else stem ++ "_" ++ toString i
    let src := mkIdent (Name.str `K256.Proofs.Generate.LIR name)
    let dst := mkIdent (Name.str `K256.Proofs.Ecdh.LIR name)
    if offset = 0 then
      evalTactic (← `(tactic|
        have $h : Relabel.block generateTarget $src = Relabel.block some $dst := by rfl))
    else
      evalTactic (← `(tactic|
        have $h : Relabel.block generateTarget $src = Relabel.block some $dst := by
          simp only [$src:ident, $dst:ident, Relabel.block, $h:ident]))
  evalTactic (← `(tactic| exact $h))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem relabel_l10a410 :
    Relabel.block generateTarget Generate.LIR.b_l10a410 = Relabel.block some LIR.b_l10a410 := by
  relabel_chunks b_l10a410 through 171

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem relabel_l11d880 :
    Relabel.block generateTarget Generate.LIR.b_l11d880 = Relabel.block some LIR.b_l11d880 := by
  relabel_chunks b_l11d880 through 83

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem generateBlocks (a : Generate.LIR.Label) (b : LIR.Label)
    (h : generateTarget a = some b) :
    Relabel.block generateTarget (Generate.LIR.program.blocks a) =
      Relabel.block some (merged.blocks b) := by
  cases a <;> rename_i l <;> cases l
  case g0.l10a410 => cases h; exact relabel_l10a410
  case g2.l11d880 => cases h; exact relabel_l11d880
  all_goals cases h <;> rfl

end K256.Proofs.Ecdh.Transfer
