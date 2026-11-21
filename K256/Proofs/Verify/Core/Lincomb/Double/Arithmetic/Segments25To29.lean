import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment25 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_25 b_l110d64_26 := by
  replay_segment using code_l110d64_25 from 1088 to 1132
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 997 => ⟨64, w20 p yy zz sp⟩, 1033 => ⟨64, w500 p yy zz sp⟩, 1057 => ⟨64, w506
      p yy zz sp⟩, 1082 => ⟨64, w515 p yy zz sp⟩, 1084 => ⟨64, w514 p yy zz sp⟩, 1086 => ⟨64, w59 p yy zz
      sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w517, w518, w519, w520, w521, w522, w523, w524, w525, w526, w527, w528, w529, w530, w531, w532, w533,
      w534, w535, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment26 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_26 b_l110d64_27 := by
  replay_segment using code_l110d64_26 from 1132 to 1177
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1055 => ⟨64, w516 p yy zz sp⟩, 1061 => ⟨64, w17 p yy zz sp⟩, 1073 => ⟨64, w512
      p yy zz sp⟩, 1075 => ⟨64, w513 p yy zz sp⟩, 1100 => ⟨64, w24 p yy zz sp⟩, 1128 => ⟨64, w535 p yy zz
      sp⟩, 1130 => ⟨64, w1 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w536, w537, w538, w539, w540, w541, w542, w543, w544, w545, w546, w547, w548, w549, w550, w551, w552,
      w553, w554, w555, w556, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment27 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_27 b_l110d64_28 := by
  replay_segment using code_l110d64_27 from 1177 to 1224
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1104 => ⟨64, w21 p yy zz sp⟩, 1124 => ⟨64, w534 p yy zz sp⟩, 1126 => ⟨64, w59
      p yy zz sp⟩, 1145 => ⟨64, w546 p yy zz sp⟩, 1164 => ⟨64, w552 p yy zz sp⟩, 1166 => ⟨64, w553 p yy zz
      sp⟩, 1173 => ⟨64, w555 p yy zz sp⟩, 1175 => ⟨64, w554 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w557, w558, w559, w560, w561, w562, w563, w564, w565, w566, w567, w568, w569, w570, w571, w572, w573,
      w574, w575, w576, w577, w578, w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment28 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_28 b_l110d64_29 := by
  replay_segment using code_l110d64_28 from 1224 to 1269
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 867 => ⟨64, w429 p yy zz sp⟩, 954 => ⟨64, w467 p yy zz sp⟩, 1150 => ⟨64, w556
      p yy zz sp⟩, 1200 => ⟨64, w566 p yy zz sp⟩, 1203 => ⟨64, w569 p yy zz sp⟩, 1207 => ⟨64, w59 p yy zz
      sp⟩, 1211 => ⟨64, w1 p yy zz sp⟩, 1213 => ⟨64, w572 p yy zz sp⟩, 1214 => ⟨64, w571 p yy zz sp⟩, 1219
      => ⟨64, w576 p yy zz sp⟩, 1221 => ⟨64, w577 p yy zz sp⟩, 1222 => Value.ofBool (addSpec (w573 p yy zz
      sp) (w551 p yy zz sp)).2.CF]
    normalize [w1, w22, w23, w24, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336,
      w364, w373, w551, w553, w555, w573, w578, w579, w580, w581, w582, w583, w584, w585, w586, w587, w588,
      w589, w590, w591, w592, w593, w594, w595, w596, w597, w598, w599, w600, w601, w602, w603, w604, w605,
      w615, w666, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment29 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_29 b_l110d64_30 := by
  replay_segment using code_l110d64_29 from 1269 to 1309
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1177 => ⟨64, w557 p yy zz sp⟩, 1240 => ⟨64, w593 p yy zz sp⟩, 1267 => ⟨64,
      w605 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336, w364,
      w373, w607, w608, w609, w613, w614, w615, w616, w618, w619, w621, w623, w624, w626, w666, v1568,
      v1569, v1571, v1572, v1573, v1574, v1575, v1576, v1577, v1580]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
