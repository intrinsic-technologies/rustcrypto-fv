import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment10 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_10 b_l110d64_11 := by
  replay_segment using code_l110d64_10 from 475 to 523
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 409 => ⟨64, w190 p yy zz sp⟩, 437 => ⟨64, w212 p yy zz sp⟩, 451 => ⟨64, w208 p
      yy zz sp⟩, 453 => ⟨64, w209 p yy zz sp⟩, 460 => ⟨64, w210 p yy zz sp⟩, 462 => ⟨64, w211 p yy zz sp⟩,
      469 => ⟨64, w213 p yy zz sp⟩, 471 => ⟨64, w214 p yy zz sp⟩, 473 => ⟨64, w10 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w215, w216, w217, w218, w219, w220, w221,
      w222, w223, w224, w225, w226, w227, w228, w229, w230, w231, w232, w233, w234, w235, w236, w237, w238,
      w239, w240, w241, w242, w243, w257, w284, w322, w334, w336, w364, w373, w615, w666, v1580,
      BitVec.mul_one]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment11 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_11 b_l110d64_12 := by
  replay_segment using code_l110d64_11 from 523 to 566
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 485 => ⟨64, w221 p yy zz sp⟩, 488 => ⟨64, w224 p yy zz sp⟩, 492 => ⟨64, w59 p
      yy zz sp⟩, 496 => ⟨64, w1 p yy zz sp⟩, 518 => ⟨64, w240 p yy zz sp⟩, 521 => ⟨64, w243 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w244, w245, w246, w247, w248, w249, w250,
      w251, w252, w253, w254, w255, w256, w257, w258, w259, w260, w284, w322, w334, w336, w364, w369, w373,
      w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment12 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_12 b_l110d64_13 := by
  replay_segment using code_l110d64_12 from 566 to 600
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 432 => ⟨64, w202 p yy zz sp⟩, 518 => ⟨64, w240 p yy zz sp⟩, 543 => ⟨64, w253 p
      yy zz sp⟩, 562 => ⟨64, w369 p yy zz sp⟩, 564 => ⟨64, w373 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w264, w265, w266, w267, w270, w271,
      w272, w273, w284, w322, w334, w336, w364, w371, w373, w374, w375, w376, w378, w380, w386, w615, w666,
      v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment13 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_13 b_l110d64_14 := by
  replay_segment using code_l110d64_13 from 600 to 638
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 589 => ⟨64, w267 p yy zz sp⟩, 598 => ⟨64, w273 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w274, w275, w276, w280, w281, w282,
      w283, w284, w285, w286, w290, w291, w292, w293, w294, w295, w322, w334, w336, w364, w373, w615, w666,
      v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment14 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_14 b_l110d64_15 := by
  replay_segment using code_l110d64_14 from 638 to 676
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 492 => ⟨64, w59 p yy zz sp⟩, 536 => ⟨64, w59 p yy zz sp⟩, 550 => ⟨64, w257 p
      yy zz sp⟩, 596 => ⟨64, w273 p yy zz sp⟩, 602 => ⟨64, w160 p yy zz sp⟩, 617 => ⟨64, w276 p yy zz sp⟩,
      621 => ⟨64, w286 p yy zz sp⟩, 634 => ⟨64, w295 p yy zz sp⟩, 636 => ⟨64, w25 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w298, w299, w300, w301, w303,
      w304, w306, w307, w308, w310, w312, w313, w314, w315, w316, w317, w318, w319, w322, w327, w334, w336,
      w364, w373, w615, w666, v1580]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
