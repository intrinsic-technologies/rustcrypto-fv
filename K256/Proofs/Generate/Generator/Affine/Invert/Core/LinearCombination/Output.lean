import K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination.Segment

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
open K256.Proofs.Common.Invert.LinearCombination
open K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem eval1087d9 : Segment b_l1084e0_11 b_l1084e0_12 At1087d9 At10881b := by
  linear_segment model [v1087e4, v1087e7, v1087f0, v1087f7, v1087fa, v1087fd, v108807, v10880a, v10880d, v108810]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem eval10881b : Segment b_l1084e0_12 b_l1084e0_13 At10881b At10885c := by
  linear_segment model [v10881b, v10881e, v108821, v108824, v10882f, v108832, v108835, v108838, v108846, v108849,
    v10884c, v10884f, v108857, v108859]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem eval10885c : Segment b_l1084e0_13 returnBlock At10885c At10888a := by
  linear_segment model [resultWords, resultSign, v10885c, v108876]

theorem emit (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs)
    (b : Values Value 589) (m : Ram) (h : At10888a a sp dst ret left right p b m) :
    ∃ out, returnBlock.eval (dialect Extracted.programImage) b m = .returned out ∧
      out.store = m ∧ Returned a sp dst ret p out := by
  refine ⟨_, rfl, rfl, ?_⟩
  constructor
  · exact congrArg some h.r586
  · exact h.r587
  · exact h.r568
  · exact h.r583
  · exact h.r571
  · exact h.r574
  · exact h.r577
  · exact h.r580
  · exact h.r22
  · exact h.r39
  · exact h.r50
  · exact h.r51
  · exact h.mdst0_64
  · exact h.mdst8_64
  · exact h.mdst16_64
  · exact h.mdst24_64
  · exact h.mdst32_64
  · exact h.mdst40_8

end K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
