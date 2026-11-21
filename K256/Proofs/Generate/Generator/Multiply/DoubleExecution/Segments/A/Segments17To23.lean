import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Sec1.Affine.Uncompressed
open Common.Point Common.Field Common.Point.DoubleWords.Replay

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment17 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_17 b_l11d880_18 := by
  replay_segment using code_l11d880_17 from 759 to 794
    registers [4 => ⟨64, sp⟩, 522 => ⟨64, w240 p yy zz sp⟩, 554 => ⟨64, w253 p yy zz sp⟩, 749 => ⟨64, w358 p
      yy zz sp⟩, 753 => ⟨64, w360 p yy zz sp⟩, 757 => ⟨64, w362 p yy zz sp⟩] slots 30
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w363, w364, w366, w368, w369, w371, w373, w374, w375, w376, w378, w380, w607, w615, w666, w1266,
      w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment18 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_18 b_l11d880_19 := by
  replay_segment using code_l11d880_18 from 794 to 830
    registers [4 => ⟨64, sp⟩, 623 => ⟨64, w25 p yy zz sp⟩, 674 => ⟨64, w17 p yy zz sp⟩, 699 => ⟨64, w18 p yy
      zz sp⟩, 722 => ⟨64, w19 p yy zz sp⟩, 779 => ⟨64, w373 p yy zz sp⟩, 792 => ⟨64, w380 p yy zz sp⟩] slots
      33
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w382, w383, w386, w388, w390, w391, w394, w395, w607, w615, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment19 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_19 b_l11d880_20 := by
  replay_segment using code_l11d880_19 from 830 to 868
    registers [4 => ⟨64, sp⟩, 674 => ⟨64, w17 p yy zz sp⟩, 683 => ⟨64, w327 p yy zz sp⟩, 699 => ⟨64, w18 p
      yy zz sp⟩, 708 => ⟨64, w340 p yy zz sp⟩, 737 => ⟨64, w350 p yy zz sp⟩, 755 => ⟨64, w20 p yy zz sp⟩,
      824 => ⟨64, w19 p yy zz sp⟩, 827 => ⟨64, w394 p yy zz sp⟩] slots 39
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w398, w400, w403, w404, w405, w406, w407, w410, w411, w607, w615, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment20 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_20 b_l11d880_21 := by
  replay_segment using code_l11d880_20 from 868 to 910
    registers [4 => ⟨64, sp⟩, 796 => ⟨64, w17 p yy zz sp⟩, 840 => ⟨64, w404 p yy zz sp⟩, 842 => ⟨64, w403 p
      yy zz sp⟩, 844 => ⟨64, w26 p yy zz sp⟩, 848 => ⟨64, w21 p yy zz sp⟩, 853 => ⟨64, w406 p yy zz sp⟩, 855
      => ⟨64, w405 p yy zz sp⟩, 864 => ⟨64, w410 p yy zz sp⟩, 866 => ⟨64, w411 p yy zz sp⟩] slots 42
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w413, w414, w415, w417, w418, w419, w420, w421, w422, w423, w424, w425, w426, w427, w428,
      w429, w430, w431, w432, w433, w434, w435, w607, w615, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment21 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_21 b_l11d880_22 := by
  replay_segment using code_l11d880_21 from 910 to 953
    registers [4 => ⟨64, sp⟩, 755 => ⟨64, w20 p yy zz sp⟩, 811 => ⟨64, w24 p yy zz sp⟩, 820 => ⟨64, w23 p yy
      zz sp⟩, 860 => ⟨64, w19 p yy zz sp⟩, 875 => ⟨64, w21 p yy zz sp⟩, 892 => ⟨64, w429 p yy zz sp⟩, 895 =>
      ⟨64, w432 p yy zz sp⟩, 897 => ⟨64, w433 p yy zz sp⟩, 908 => ⟨64, w25 p yy zz sp⟩] slots 39
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w436, w437, w438, w439, w440, w441, w442, w443, w444, w445, w446, w607, w615, w666, w1266,
      w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment22 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_22 b_l11d880_23 := by
  replay_segment using code_l11d880_22 from 953 to 999
    registers [4 => ⟨64, sp⟩, 920 => ⟨64, w439 p yy zz sp⟩, 922 => ⟨64, w438 p yy zz sp⟩, 924 => ⟨64, w440 p
      yy zz sp⟩, 931 => ⟨64, w442 p yy zz sp⟩, 933 => ⟨64, w441 p yy zz sp⟩, 935 => ⟨64, w22 p yy zz sp⟩,
      942 => ⟨64, w443 p yy zz sp⟩, 944 => ⟨64, w444 p yy zz sp⟩, 950 => ⟨64, w446 p yy zz sp⟩, 951 => ⟨64,
      w445 p yy zz sp⟩] slots 41
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w447, w448, w449, w450, w451, w452, w453, w454, w455, w456, w457, w458, w459, w460, w461,
      w462, w463, w464, w465, w466, w467, w468, w469, w470, w471, w472, w473, w474, w607, w615, w666, w1266,
      w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment23 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_23 b_l11d880_24 := by
  replay_segment using code_l11d880_23 from 999 to 1044
    registers [4 => ⟨64, sp⟩, 906 => ⟨64, w25 p yy zz sp⟩, 978 => ⟨64, w467 p yy zz sp⟩, 981 => ⟨64, w470 p
      yy zz sp⟩, 996 => ⟨64, w474 p yy zz sp⟩, 997 => ⟨64, w473 p yy zz sp⟩] slots 39
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w475, w476, w477, w478, w479, w480, w481, w482, w483, w484, w485, w486, w487, w488, w489,
      w607, w615, w666, w1266, w1270]

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
