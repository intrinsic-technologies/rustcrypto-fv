import K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination.Segment

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
open K256.Proofs.Common.Invert.LinearCombination
open K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem eval1085f2 : Segment b_l1084e0_4 b_l1084e0_5 At1085f2 At108640 := by
  linear_segment model [v1085f2, v1085fa, v108606, v10860e, v108617, v10861f, v108639]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem eval108640 : Segment b_l1084e0_5 b_l1084e0_6 At108640 At108684 := by
  linear_segment model [v108640, v108643, v108646, v108650, v108658, v10865b, v10865e, v10866d, v108674, v108677,
    v10867a, v108681]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem eval108684 : Segment b_l1084e0_6 b_l1084e0_7 At108684 At1086c8 := by
  linear_segment model [v108689, v10868c, v10868f, v10869c, v10869f, v1086a5, v1086a8, v1086ab, v1086ae, v1086b1,
    v1086c4]

end K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
