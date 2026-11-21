import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Sec1.Affine.Uncompressed
open Common.Point Common.Field Common.Point.DoubleWords.Replay

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment12 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_12 b_l11d880_13 := by
  replay_segment using code_l11d880_12 from 569 to 606
    registers [4 => ⟨64, sp⟩] slots 25
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w262, w264, w265, w266, w267,
      w270, w271, w272, w273, w274, w275, w276, w280, w281, w282, w283, w284, w285, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment13 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_13 b_l11d880_14 := by
  replay_segment using code_l11d880_13 from 606 to 644
    registers [4 => ⟨64, sp⟩, 558 => ⟨64, w257 p yy zz sp⟩, 581 => ⟨64, w273 p yy zz sp⟩, 598 => ⟨64, w283 p
      yy zz sp⟩, 604 => ⟨64, w285 p yy zz sp⟩] slots 25
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w286, w290, w291, w292,
      w293, w294, w295, w298, w299, w300, w301, w303, w304, w306, w312, w322, w334, w336, w364, w373, w607,
      w615, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment14 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_14 b_l11d880_15 := by
  replay_segment using code_l11d880_14 from 644 to 681
    registers [4 => ⟨64, sp⟩, 587 => ⟨64, w160 p yy zz sp⟩, 602 => ⟨64, w276 p yy zz sp⟩, 638 => ⟨64, w306 p
      yy zz sp⟩, 640 => ⟨64, w304 p yy zz sp⟩] slots 25
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w307, w308, w310, w312,
      w313, w314, w315, w316, w317, w318, w319, w321, w322, w324, w326, w334, w336, w364, w373, w607, w615,
      w666, w1266, w1270]

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
