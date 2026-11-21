import K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination.Segment

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
open K256.Proofs.Common.Invert.LinearCombination
open K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem eval1084e0 : Segment b_l1084e0 b_l1084e0_1 At1084e0 At108519 := by
  linear_segment model [v1084f4, v108500, v10850d, v108510, v108513, v108516]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem eval108519 : Segment b_l1084e0_1 b_l1084e0_2 At108519 At10855c := by
  linear_segment model [v10851c, v10852e, v10853a, v108540, v10854f, v108555]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem eval10855c : Segment b_l1084e0_2 b_l1084e0_3 At10855c At1085a1 := by
  linear_segment model [v10855f, v108562, v108568, v108572, v108575, v108578, v10857b, v10857e, v108585, v108595]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem eval1085a1 : Segment b_l1084e0_3 b_l1084e0_4 At1085a1 At1085f2 := by
  linear_segment model [v1085a4, v1085b3, v1085bf, v1085c3, v1085c8, v1085d5, v1085d8, v1085e6]

end K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
