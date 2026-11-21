import K256.Proofs.Signing.Transfer.Verify.LongBlocks

namespace K256.Proofs.Signing.Transfer.VerifyProgram

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG0 (src : Verify.LIR.Label.G0) (dst : Signing.LIR.Label)
    (h : target (.g0 src) = some dst) : Matches (.g0 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG1 (src : Verify.LIR.Label.G1) (dst : Signing.LIR.Label)
    (h : target (.g1 src) = some dst) : Matches (.g1 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG2 (src : Verify.LIR.Label.G2) (dst : Signing.LIR.Label)
    (h : target (.g2 src) = some dst) : Matches (.g2 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG3 (src : Verify.LIR.Label.G3) (dst : Signing.LIR.Label)
    (h : target (.g3 src) = some dst) : Matches (.g3 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG4 (src : Verify.LIR.Label.G4) (dst : Signing.LIR.Label)
    (h : target (.g4 src) = some dst) : Matches (.g4 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG5 (src : Verify.LIR.Label.G5) (dst : Signing.LIR.Label)
    (h : target (.g5 src) = some dst) : Matches (.g5 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG6 (src : Verify.LIR.Label.G6) (dst : Signing.LIR.Label)
    (h : target (.g6 src) = some dst) : Matches (.g6 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG7 (src : Verify.LIR.Label.G7) (dst : Signing.LIR.Label)
    (h : target (.g7 src) = some dst) : Matches (.g7 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG8 (src : Verify.LIR.Label.G8) (dst : Signing.LIR.Label)
    (h : target (.g8 src) = some dst) : Matches (.g8 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG9 (src : Verify.LIR.Label.G9) (dst : Signing.LIR.Label)
    (h : target (.g9 src) = some dst) : Matches (.g9 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG10 (src : Verify.LIR.Label.G10) (dst : Signing.LIR.Label)
    (h : target (.g10 src) = some dst) : Matches (.g10 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG11 (src : Verify.LIR.Label.G11) (dst : Signing.LIR.Label)
    (h : target (.g11 src) = some dst) : Matches (.g11 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG12 (src : Verify.LIR.Label.G12) (dst : Signing.LIR.Label)
    (h : target (.g12 src) = some dst) : Matches (.g12 src) dst := by
  cases src
  case l10a410 => cases h; exact matches_l10a410
  case l10e4c0 => cases h; exact matches_l10e4c0
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG13 (src : Verify.LIR.Label.G13) (dst : Signing.LIR.Label)
    (h : target (.g13 src) = some dst) : Matches (.g13 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG14 (src : Verify.LIR.Label.G14) (dst : Signing.LIR.Label)
    (h : target (.g14 src) = some dst) : Matches (.g14 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG15 (src : Verify.LIR.Label.G15) (dst : Signing.LIR.Label)
    (h : target (.g15 src) = some dst) : Matches (.g15 src) dst := by
  cases src
  case l110d64 => cases h; exact matches_l110d64
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG16 (src : Verify.LIR.Label.G16) (dst : Signing.LIR.Label)
    (h : target (.g16 src) = some dst) : Matches (.g16 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG17 (src : Verify.LIR.Label.G17) (dst : Signing.LIR.Label)
    (h : target (.g17 src) = some dst) : Matches (.g17 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG18 (src : Verify.LIR.Label.G18) (dst : Signing.LIR.Label)
    (h : target (.g18 src) = some dst) : Matches (.g18 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG19 (src : Verify.LIR.Label.G19) (dst : Signing.LIR.Label)
    (h : target (.g19 src) = some dst) : Matches (.g19 src) dst := by
  cases src
  case l11d880 => cases h; exact matches_l11d880
  case l11f8f6 => cases h; exact matches_l11f8f6
  case l12065f => cases h; exact matches_l12065f
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG20 (src : Verify.LIR.Label.G20) (dst : Signing.LIR.Label)
    (h : target (.g20 src) = some dst) : Matches (.g20 src) dst := by
  cases src
  case l121930 => cases h; exact matches_l121930
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG21 (src : Verify.LIR.Label.G21) (dst : Signing.LIR.Label)
    (h : target (.g21 src) = some dst) : Matches (.g21 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG22 (src : Verify.LIR.Label.G22) (dst : Signing.LIR.Label)
    (h : target (.g22 src) = some dst) : Matches (.g22 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG23 (src : Verify.LIR.Label.G23) (dst : Signing.LIR.Label)
    (h : target (.g23 src) = some dst) : Matches (.g23 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG24 (src : Verify.LIR.Label.G24) (dst : Signing.LIR.Label)
    (h : target (.g24 src) = some dst) : Matches (.g24 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG25 (src : Verify.LIR.Label.G25) (dst : Signing.LIR.Label)
    (h : target (.g25 src) = some dst) : Matches (.g25 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG26 (src : Verify.LIR.Label.G26) (dst : Signing.LIR.Label)
    (h : target (.g26 src) = some dst) : Matches (.g26 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG27 (src : Verify.LIR.Label.G27) (dst : Signing.LIR.Label)
    (h : target (.g27 src) = some dst) : Matches (.g27 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG28 (src : Verify.LIR.Label.G28) (dst : Signing.LIR.Label)
    (h : target (.g28 src) = some dst) : Matches (.g28 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG29 (src : Verify.LIR.Label.G29) (dst : Signing.LIR.Label)
    (h : target (.g29 src) = some dst) : Matches (.g29 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG30 (src : Verify.LIR.Label.G30) (dst : Signing.LIR.Label)
    (h : target (.g30 src) = some dst) : Matches (.g30 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG31 (src : Verify.LIR.Label.G31) (dst : Signing.LIR.Label)
    (h : target (.g31 src) = some dst) : Matches (.g31 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG32 (src : Verify.LIR.Label.G32) (dst : Signing.LIR.Label)
    (h : target (.g32 src) = some dst) : Matches (.g32 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG33 (src : Verify.LIR.Label.G33) (dst : Signing.LIR.Label)
    (h : target (.g33 src) = some dst) : Matches (.g33 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem matchesG34 (src : Verify.LIR.Label.G34) (dst : Signing.LIR.Label)
    (h : target (.g34 src) = some dst) : Matches (.g34 src) dst := by
  cases src
  all_goals cases h <;> with_unfolding_all rfl

theorem blocks : ∀ src dst, target src = some dst → Matches src dst
  | .g0 src, dst, h => matchesG0 src dst h
  | .g1 src, dst, h => matchesG1 src dst h
  | .g2 src, dst, h => matchesG2 src dst h
  | .g3 src, dst, h => matchesG3 src dst h
  | .g4 src, dst, h => matchesG4 src dst h
  | .g5 src, dst, h => matchesG5 src dst h
  | .g6 src, dst, h => matchesG6 src dst h
  | .g7 src, dst, h => matchesG7 src dst h
  | .g8 src, dst, h => matchesG8 src dst h
  | .g9 src, dst, h => matchesG9 src dst h
  | .g10 src, dst, h => matchesG10 src dst h
  | .g11 src, dst, h => matchesG11 src dst h
  | .g12 src, dst, h => matchesG12 src dst h
  | .g13 src, dst, h => matchesG13 src dst h
  | .g14 src, dst, h => matchesG14 src dst h
  | .g15 src, dst, h => matchesG15 src dst h
  | .g16 src, dst, h => matchesG16 src dst h
  | .g17 src, dst, h => matchesG17 src dst h
  | .g18 src, dst, h => matchesG18 src dst h
  | .g19 src, dst, h => matchesG19 src dst h
  | .g20 src, dst, h => matchesG20 src dst h
  | .g21 src, dst, h => matchesG21 src dst h
  | .g22 src, dst, h => matchesG22 src dst h
  | .g23 src, dst, h => matchesG23 src dst h
  | .g24 src, dst, h => matchesG24 src dst h
  | .g25 src, dst, h => matchesG25 src dst h
  | .g26 src, dst, h => matchesG26 src dst h
  | .g27 src, dst, h => matchesG27 src dst h
  | .g28 src, dst, h => matchesG28 src dst h
  | .g29 src, dst, h => matchesG29 src dst h
  | .g30 src, dst, h => matchesG30 src dst h
  | .g31 src, dst, h => matchesG31 src dst h
  | .g32 src, dst, h => matchesG32 src dst h
  | .g33 src, dst, h => matchesG33 src dst h
  | .g34 src, dst, h => matchesG34 src dst h

end K256.Proofs.Signing.Transfer.VerifyProgram
