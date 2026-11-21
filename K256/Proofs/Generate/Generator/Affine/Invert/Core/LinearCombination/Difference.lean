import K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination.Segment

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
open K256.Proofs.Common.Invert.LinearCombination
open K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem eval1086c8 : Segment b_l1084e0_7 b_l1084e0_8 At1086c8 At108709 := by
  linear_segment model [v1086cb, v1086ce, v1086d2, v1086d5, v1086db, v1086de, v1086e1, v1086e4, v1086e7, v1086f2,
    v1086f9, v1086fc, v108700, v108703]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem eval108709 : Segment b_l1084e0_8 b_l1084e0_9 At108709 At10874b := by
  linear_segment model [v108709, v10870c, v10870f, v108712, v108715, v108720, v108727, v10872a, v10872e, v108731,
    v108737, v10873a, v10873d, v108740, v108743]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem eval10874b : Segment b_l1084e0_9 b_l1084e0_10 At10874b At10878d := by
  linear_segment model [v10874d, v108756, v108762, v108765, v108768, v10876b, v10876e, v108771, v108777, v10877a,
    v108780, v108783, v108786, v10878a]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem eval10878d : Segment b_l1084e0_10 b_l1084e0_11 At10878d At1087d9 := by
  linear_segment model [v10878d, v108790, v108793, v1087a3, v1087bb, v1087c4, v1087cd, v1087d0, v1087d6]

end K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
