import K256.Proofs.Ecdh.LIR.Program
import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Generate.Serialize.Transfer.Relabel

namespace K256.Proofs.Ecdh.Transfer

open Lean Elab Tactic K256.Proofs.Generate.Serialize

local elab "same_label" : tactic => do
  let tag ← (← getMainGoal).getTag
  let target := mkIdent (Name.str ``LIR.Label tag.getString!)
  evalTactic (← `(tactic| exact some $target))

def sec1Target : Sec1.LIR.Label → Option LIR.Label := by
  intro a
  cases a <;> rename_i l <;> cases l <;> same_label

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem sec1Blocks (a : Sec1.LIR.Label) (b : LIR.Label) (h : sec1Target a = some b) :
    Relabel.block sec1Target (Sec1.LIR.program.blocks a) =
      Relabel.block some (LIR.program.blocks b) := by
  cases a <;> rename_i l <;> cases l <;> cases h <;> rfl

end K256.Proofs.Ecdh.Transfer
