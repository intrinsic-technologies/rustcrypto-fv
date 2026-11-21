import K256.Proofs.Signing.Transfer.Generator.Labels

namespace K256.Proofs.Signing.Transfer.Generator

open Lean Elab Tactic Generate.Serialize
local elab "transfer_chunks " label:ident " through " last:num : tactic => do
  let h := mkIdent `relabeled
  for offset in [:last.getNat + 1] do
    let i := last.getNat - offset
    let stem := label.getId.toString
    let name := if i = 0 then stem else stem ++ "_" ++ toString i
    let src := mkIdent (Name.str `K256.Proofs.Generate.LIR name)
    let dst := mkIdent (Name.str `K256.Proofs.Verify.LIR name)
    if offset = 0 then
      evalTactic (← `(tactic|
        have $h : Relabel.block target $src = Relabel.block some $dst := by rfl))
    else
      evalTactic (← `(tactic|
        have $h : Relabel.block target $src = Relabel.block some $dst := by
          simp only [$src:ident, $dst:ident, Relabel.block, $h:ident]))
  evalTactic (← `(tactic| exact $h))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem pointAddition : Matches .l10a410 .l10a410 := by
  transfer_chunks b_l10a410 through 171

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem pointDoubling : Matches .l11d880 .l11d880 := by
  transfer_chunks b_l11d880 through 83

end K256.Proofs.Signing.Transfer.Generator
