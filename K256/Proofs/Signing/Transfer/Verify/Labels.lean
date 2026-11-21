import K256.Proofs.Signing.LIR.Program
import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Generate.Serialize.Transfer.Relabel

namespace K256.Proofs.Signing.Transfer.VerifyProgram

open Lean Elab Tactic Generate.Serialize

local elab "shared_target" : tactic => do
  let label := (← (← getMainGoal).getTag).getString!
  let excluded := [
    "l102fc0", "l102fe9", "l102ff4", "l10302c", "l103037", "l103101", "l103115",
    "l10311e", "l103154", "l103170", "l1031c3", "l1031cd", "l10324a", "l103289",
    "l103306", "l1033a2", "l104f20", "l104fa4", "l104fb0", "l104fbc", "l105051",
    "l10505d", "l105069", "l1050a9", "l1050c1", "l10513d", "l105145", "l10518b",
    "l10519d", "l1051b1", "l105216", "l105256", "l10526c", "l10527f", "l105292",
    "l105306", "l105393", "l105398", "l1053af", "l1053cb", "l1053d5", "l1053ef",
    "l105415"]
  if excluded.contains label then
    evalTactic (← `(tactic| exact none))
  else
    let target := mkIdent (Name.str ``Signing.LIR.Label label)
    evalTactic (← `(tactic| exact some $target))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
def target (label : Verify.LIR.Label) : Option Signing.LIR.Label := by
  cases label <;> rename_i group <;> cases group <;> shared_target

abbrev Matches (src : Verify.LIR.Label) (dst : Signing.LIR.Label) :=
  Relabel.block target (Verify.LIR.program.blocks src) =
    Relabel.block some (Signing.LIR.program.blocks dst)

end K256.Proofs.Signing.Transfer.VerifyProgram
