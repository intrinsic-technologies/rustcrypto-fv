import K256.Proofs.Signing.Transfer.Generator.Arithmetic

namespace K256.Proofs.Signing.Transfer.Generator

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem blocks (a : Generate.LIR.Label) (b : Verify.LIR.Label) (h : target a = some b) :
    Matches a b := by
  cases a <;> rename_i l <;> cases l
  case g0.l10a410 => cases h; exact pointAddition
  case g2.l11d880 => cases h; exact pointDoubling
  all_goals cases h <;> with_unfolding_all rfl

end K256.Proofs.Signing.Transfer.Generator
