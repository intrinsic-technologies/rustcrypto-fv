import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment20 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_20 b_l110d64_21 := by
  replay_segment using code_l110d64_20 from 870 to 911
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 780 => ⟨64, w25 p yy zz sp⟩, 789 => ⟨64, w24 p yy zz sp⟩, 801 => ⟨64, w23 p yy
      zz sp⟩, 822 => ⟨64, w26 p yy zz sp⟩, 831 => ⟨64, w406 p yy zz sp⟩, 833 => ⟨64, w405 p yy zz sp⟩, 838
      => ⟨64, w20 p yy zz sp⟩, 847 => ⟨64, w413 p yy zz sp⟩, 865 => ⟨64, w428 p yy zz sp⟩, 867 => ⟨64, w429
      p yy zz sp⟩, 868 => Value.ofBool (addSpec (w425 p yy zz sp) (w414 p yy zz sp)).2.CF]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w383, w391, w395, w404, w410, w414, w417, w421, w425, w430, w431, w432, w433, w434, w435, w436, w437,
      w438, w439, w440, w441, w442, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment21 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_21 b_l110d64_22 := by
  replay_segment using code_l110d64_21 from 911 to 959
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 850 => ⟨64, w21 p yy zz sp⟩, 872 => ⟨64, w433 p yy zz sp⟩, 874 => ⟨64, w440 p
      yy zz sp⟩, 891 => ⟨64, w437 p yy zz sp⟩, 898 => ⟨64, w438 p yy zz sp⟩, 900 => ⟨64, w439 p yy zz sp⟩,
      907 => ⟨64, w441 p yy zz sp⟩, 909 => ⟨64, w442 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w443, w444, w445, w446, w447, w448, w449, w450, w451, w452, w453, w454, w455, w456, w457, w458, w459,
      w460, w461, w462, w463, w464, w465, w466, w467, w468, w469, w470, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment22 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_22 b_l110d64_23 := by
  replay_segment using code_l110d64_22 from 959 to 999
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 878 => ⟨64, w17 p yy zz sp⟩, 911 => ⟨64, w22 p yy zz sp⟩, 954 => ⟨64, w467 p
      yy zz sp⟩, 957 => ⟨64, w470 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w471, w472, w473, w474, w475, w476, w477, w478, w479, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment23 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_23 b_l110d64_24 := by
  replay_segment using code_l110d64_23 from 999 to 1045
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 959 => ⟨64, w478 p yy zz sp⟩, 980 => ⟨64, w474 p yy zz sp⟩, 989 => ⟨64, w477 p
      yy zz sp⟩, 991 => ⟨64, w476 p yy zz sp⟩, 993 => ⟨64, w479 p yy zz sp⟩, 995 => ⟨64, w24 p yy zz sp⟩,
      997 => ⟨64, w20 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w480, w481, w482, w483, w484, w485, w486, w487, w488, w489, w490, w491, w492, w493, w494, w495, w496,
      w497, w498, w499, w500, w501, w502, w503, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment24 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_24 b_l110d64_25 := by
  replay_segment using code_l110d64_24 from 1045 to 1088
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 974 => ⟨64, w18 p yy zz sp⟩, 984 => ⟨64, w19 p yy zz sp⟩, 1006 => ⟨64, w23 p
      yy zz sp⟩, 1041 => ⟨64, w503 p yy zz sp⟩, 1043 => ⟨64, w160 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w504, w505, w506, w507, w508, w509, w510, w511, w512, w513, w514, w515, w516, w615, w666, v1580,
      BitVec.mul_one]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
