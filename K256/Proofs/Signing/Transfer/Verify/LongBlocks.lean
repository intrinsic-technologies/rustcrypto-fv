import K256.Proofs.Signing.Transfer.Verify.Labels

namespace K256.Proofs.Signing.Transfer.VerifyProgram

open Lean Elab Tactic Generate.Serialize

local elab "transfer_chunks " label:ident " through " last:num : tactic => do
  let previous := mkIdent `previous
  for offset in [:last.getNat + 1] do
    let i := last.getNat - offset
    let stem := label.getId.toString
    let name := if i = 0 then stem else stem ++ "_" ++ toString i
    let src := mkIdent (Name.str `K256.Proofs.Verify.LIR name)
    let dst := mkIdent (Name.str `K256.Proofs.Signing.LIR name)
    if offset = 0 then
      evalTactic (← `(tactic|
        have $previous : Relabel.block target $src = Relabel.block some $dst := by
          with_unfolding_all rfl))
    else
      evalTactic (← `(tactic|
        have $previous : Relabel.block target $src = Relabel.block some $dst := by
          simp only [$src:ident, $dst:ident, Relabel.block, $previous:ident]))
  evalTactic (← `(tactic| exact $previous))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem matches_l10a410 : Matches .l10a410 .l10a410 := by
  transfer_chunks b_l10a410 through 171

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem matches_l10e4c0 : Matches .l10e4c0 .l10e4c0 := by
  transfer_chunks b_l10e4c0 through 24

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem matches_l110d64 : Matches .l110d64 .l110d64 := by
  transfer_chunks b_l110d64 through 82

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem matches_l11d880 : Matches .l11d880 .l11d880 := by
  transfer_chunks b_l11d880 through 83

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem matches_l11f8f6 : Matches .l11f8f6 .l11f8f6 := by
  transfer_chunks b_l11f8f6 through 31

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem matches_l12065f : Matches .l12065f .l12065f := by
  transfer_chunks b_l12065f through 21

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem matches_l121930 : Matches .l121930 .l121930 := by
  transfer_chunks b_l121930 through 166

end K256.Proofs.Signing.Transfer.VerifyProgram
