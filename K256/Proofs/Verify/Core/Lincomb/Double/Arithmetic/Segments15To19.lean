import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment15 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (_rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_15 b_l110d64_16 := by
  replay_segment using code_l110d64_15 from 676 to 716
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [536 => ⟨64, w59 p yy zz sp⟩, 550 => ⟨64, w257 p yy zz sp⟩, 634 => ⟨64, w295 p yy zz sp⟩, 647
      => ⟨64, w304 p yy zz sp⟩, 660 => ⟨64, w314 p yy zz sp⟩, 672 => ⟨64, w319 p yy zz sp⟩, 674 => ⟨64, w327
      p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w328, w329, w330,
      w331, w334, w336, w340, w341, w342, w343, w344, w350, w351, w352, w356, w364, w373, w615, w666, v1547,
      v1548, v1550, v1552, v1580]

private theorem negationOffset_eq (p : PointWords) (yy zz : Limbs) (sp : Word) :
    w337 p yy zz sp = 0x3ffffffffffffc := BitVec.mul_one _

private theorem ySquareLimb_unitScale (p : PointWords) (yy zz : Limbs) (sp : Word) :
    v1558 p yy zz sp = w18 p yy zz sp := BitVec.mul_one _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1700000 in
theorem segment16 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_16 b_l110d64_17 := by
  replay_segment using code_l110d64_16 from 716 to 753
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 536 => ⟨64, w59 p yy zz sp⟩, 672 => ⟨64, w319 p yy zz sp⟩, 684 => ⟨64, w331 p
      yy zz sp⟩, 696 => ⟨64, w344 p yy zz sp⟩, 708 => ⟨64, v1550 p yy zz sp⟩, 710 => ⟨64, w356 p yy zz sp⟩,
      714 => ⟨64, v1552 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w321, w322, w333, w334, w336,
      ↓negationOffset_eq, w346, w348, w349, w364, w373, w615, w666, v1553, v1555, v1556, ↓ySquareLimb_unitScale, v1559, v1560, v1561,
      v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment17 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_17 b_l110d64_18 := by
  replay_segment using code_l110d64_17 from 753 to 788
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 558 => ⟨64, w260 p yy zz sp⟩, 670 => ⟨64, w310 p yy zz sp⟩, 682 => ⟨64, w327 p
      yy zz sp⟩, 716 => ⟨64, v1553 p yy zz sp⟩, 720 => ⟨64, w17 p yy zz sp⟩, 733 => ⟨64, w334 p yy zz sp⟩,
      735 => ⟨64, w18 p yy zz sp⟩, 751 => ⟨64, v1561 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w382, w383, w388, w398, w400, w615, w666, v1562, v1564, v1565, v1566, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment18 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_18 b_l110d64_19 := by
  replay_segment using code_l110d64_18 from 788 to 826
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 694 => ⟨64, w340 p yy zz sp⟩, 735 => ⟨64, w18 p yy zz sp⟩, 744 => ⟨64, w19 p
      yy zz sp⟩, 753 => ⟨64, w20 p yy zz sp⟩, 784 => ⟨64, w383 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w390, w391, w394, w395, w403, w404, w407, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment19 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_19 b_l110d64_20 := by
  replay_segment using code_l110d64_19 from 826 to 870
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 698 => ⟨64, w350 p yy zz sp⟩, 760 => ⟨64, w21 p yy zz sp⟩, 809 => ⟨64, w395 p
      yy zz sp⟩, 813 => ⟨64, w20 p yy zz sp⟩, 818 => ⟨64, w403 p yy zz sp⟩, 820 => ⟨64, w404 p yy zz sp⟩,
      824 => ⟨64, w26 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w405, w406, w410, w411, w413, w414, w415, w417, w418, w419, w420, w421, w422, w423, w424, w425, w426,
      w427, w428, w429, w430, w615, w666, v1580]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
