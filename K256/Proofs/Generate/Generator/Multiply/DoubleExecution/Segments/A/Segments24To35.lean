import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Sec1.Affine.Uncompressed
open Common.Point Common.Field Common.Point.DoubleWords.Replay

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment24 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_24 b_l11d880_25 := by
  replay_segment using code_l11d880_24 from 1044 to 1087
    registers [4 => ⟨64, sp⟩, 985 => ⟨64, w17 p yy zz sp⟩, 999 => ⟨64, w474 p yy zz sp⟩, 1001 => ⟨64, w473 p
      yy zz sp⟩, 1014 => ⟨64, w476 p yy zz sp⟩, 1016 => ⟨64, w478 p yy zz sp⟩, 1018 => ⟨64, w479 p yy zz
      sp⟩, 1029 => ⟨64, w23 p yy zz sp⟩, 1039 => ⟨64, w487 p yy zz sp⟩, 1041 => ⟨64, w488 p yy zz sp⟩, 1042
      => Value.ofBool (addSpec (w484 p yy zz sp) (w477 p yy zz sp)).2.CF] slots 39
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w477, w481, w483, w484, w489, w490, w491, w492, w493, w494, w495, w496, w497, w498, w499,
      w500, w501, w502, w503, w504, w505, w506, w507, w508, w509, w510, w511, w607, w615, w666, w1266,
      w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment25 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_25 b_l11d880_26 := by
  replay_segment using code_l11d880_25 from 1087 to 1128
    registers [4 => ⟨64, sp⟩, 994 => ⟨64, w18 p yy zz sp⟩, 1075 => ⟨64, w506 p yy zz sp⟩, 1078 => ⟨64, w509
      p yy zz sp⟩] slots 39
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w512, w513, w514, w515, w516, w517, w518, w519, w607, w615, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment26 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_26 b_l11d880_27 := by
  replay_segment using code_l11d880_26 from 1128 to 1176
    registers [4 => ⟨64, sp⟩, 1056 => ⟨64, w500 p yy zz sp⟩, 1092 => ⟨64, w512 p yy zz sp⟩, 1094 => ⟨64,
      w513 p yy zz sp⟩, 1103 => ⟨64, w515 p yy zz sp⟩, 1106 => ⟨64, w516 p yy zz sp⟩, 1120 => ⟨64, w519 p yy
      zz sp⟩, 1122 => ⟨64, w518 p yy zz sp⟩, 1124 => ⟨64, w24 p yy zz sp⟩, 1126 => ⟨64, w24 p yy zz sp⟩]
      slots 40
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w520, w521, w522, w523, w524, w525, w526, w527, w528, w529, w530, w531, w532, w533, w534,
      w535, w536, w537, w538, w539, w540, w541, w542, w543, w544, w545, w546, w547, w548, w549, w607, w615,
      w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment27 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_27 b_l11d880_28 := by
  replay_segment using code_l11d880_27 from 1176 to 1219
    registers [4 => ⟨64, sp⟩, 1098 => ⟨64, w19 p yy zz sp⟩, 1115 => ⟨64, w20 p yy zz sp⟩, 1128 => ⟨64, w21 p
      yy zz sp⟩, 1169 => ⟨64, w546 p yy zz sp⟩, 1172 => ⟨64, w549 p yy zz sp⟩, 1174 => ⟨64, w24 p yy zz sp⟩]
      slots 37
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w550, w551, w552, w553, w554, w555, w556, w557, w558, w559, w560, w561, w607, w615, w666,
      w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment28 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_28 b_l11d880_29 := by
  replay_segment using code_l11d880_28 from 1219 to 1266
    registers [4 => ⟨64, sp⟩, 1148 => ⟨64, w534 p yy zz sp⟩, 1186 => ⟨64, w552 p yy zz sp⟩, 1188 => ⟨64,
      w553 p yy zz sp⟩, 1195 => ⟨64, w555 p yy zz sp⟩, 1197 => ⟨64, w554 p yy zz sp⟩, 1199 => ⟨64, w556 p yy
      zz sp⟩, 1210 => ⟨64, w559 p yy zz sp⟩, 1212 => ⟨64, w558 p yy zz sp⟩, 1216 => ⟨64, w561 p yy zz sp⟩,
      1217 => ⟨64, w560 p yy zz sp⟩] slots 35
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w562, w563, w564, w565, w566, w567, w568, w569, w570, w571, w572, w573, w574, w575, w576,
      w577, w578, w579, w580, w581, w582, w583, w584, w585, w586, w587, w588, w589, w607, w615, w666, w1266,
      w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment29 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_29 b_l11d880_30 := by
  replay_segment using code_l11d880_29 from 1266 to 1309
    registers [4 => ⟨64, sp⟩, 892 => ⟨64, w429 p yy zz sp⟩, 978 => ⟨64, w467 p yy zz sp⟩, 1237 => ⟨64, w1 p
      yy zz sp⟩, 1257 => ⟨64, w585 p yy zz sp⟩, 1260 => ⟨64, w588 p yy zz sp⟩, 1264 => ⟨64, w589 p yy zz
      sp⟩] slots 33
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w590, w591, w592, w593, w594, w595, w596, w597, w598, w599, w600, w601, w602, w603, w604,
      w605, w607, w608, w609, w610, w611, w612, w615, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment30 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_30 b_l11d880_31 := by
  replay_segment using code_l11d880_30 from 1309 to 1349
    registers [4 => ⟨64, sp⟩, 1203 => ⟨64, w557 p yy zz sp⟩, 1273 => ⟨64, w593 p yy zz sp⟩, 1282 => ⟨64,
      w599 p yy zz sp⟩, 1297 => ⟨64, w610 p yy zz sp⟩, 1305 => ⟨64, w612 p yy zz sp⟩, 1307 => ⟨64, w517 p yy
      zz sp⟩] slots 32
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w613, w614, w615, w616, w617, w618, w619, w620, w621, w622, w623, w624, w625, w626,
      w627, w628, w629, w630, w631, w632, w633, w635, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment31 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_31 b_l11d880_32 := by
  replay_segment using code_l11d880_31 from 1349 to 1385
    registers [4 => ⟨64, sp⟩, 1317 => ⟨64, w617 p yy zz sp⟩, 1327 => ⟨64, w622 p yy zz sp⟩, 1341 => ⟨64,
      w627 p yy zz sp⟩, 1345 => ⟨64, w633 p yy zz sp⟩, 1347 => ⟨64, w635 p yy zz sp⟩] slots 32
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w636, w637, w639, w640, w641, w642, w643, w644, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment32 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_32 b_l11d880_33 := by
  replay_segment using code_l11d880_32 from 1385 to 1430
    registers [4 => ⟨64, sp⟩, 1373 => ⟨64, w642 p yy zz sp⟩, 1375 => ⟨64, w641 p yy zz sp⟩] slots 37
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w645, w646, w647, w648, w649, w650, w651, w652, w653, w654, w655, w656, w657,
      w658, w666, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment33 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_33 b_l11d880_34 := by
  replay_segment using code_l11d880_33 from 1430 to 1473
    registers [4 => ⟨64, sp⟩, 1366 => ⟨64, w374 p yy zz sp⟩, 1414 => ⟨64, w653 p yy zz sp⟩, 1417 => ⟨64,
      w656 p yy zz sp⟩, 1425 => ⟨64, w658 p yy zz sp⟩, 1428 => ⟨64, w657 p yy zz sp⟩] slots 37
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w659, w660, w661, w662, w663, w664, w665, w666, w667, w668, w669, w670, w671,
      w672, w673, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment34 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_34 b_l11d880_35 := by
  replay_segment using code_l11d880_34 from 1473 to 1515
    registers [4 => ⟨64, sp⟩, 1385 => ⟨64, w375 p yy zz sp⟩, 1401 => ⟨64, w378 p yy zz sp⟩, 1405 => ⟨64,
      w339 p yy zz sp⟩, 1419 => ⟨64, w386 p yy zz sp⟩, 1423 => ⟨64, w326 p yy zz sp⟩, 1437 => ⟨64, w388 p yy
      zz sp⟩, 1441 => ⟨64, w368 p yy zz sp⟩, 1471 => ⟨64, w374 p yy zz sp⟩] slots 38
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w674, w675, w676, w677, w678, w679, w680, w681, w682, w683, w1266,
      w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment35 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_35 b_l11d880_36 := by
  replay_segment using code_l11d880_35 from 1515 to 1562
    registers [4 => ⟨64, sp⟩, 1446 => ⟨64, w663 p yy zz sp⟩, 1450 => ⟨64, w665 p yy zz sp⟩, 1466 => ⟨64,
      w670 p yy zz sp⟩, 1469 => ⟨64, w673 p yy zz sp⟩, 1483 => ⟨64, w677 p yy zz sp⟩, 1485 => ⟨64, w676 p yy
      zz sp⟩, 1495 => ⟨64, w679 p yy zz sp⟩, 1502 => ⟨64, w680 p yy zz sp⟩, 1504 => ⟨64, w681 p yy zz sp⟩,
      1511 => ⟨64, w683 p yy zz sp⟩, 1513 => ⟨64, w682 p yy zz sp⟩] slots 41
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w684, w685, w686, w687, w688, w689, w691, w692, w693, w694, w695, w696,
      w697, w698, w699, w700, w701, w702, w703, w704, w705, w706, w707, w708, w709, w710, w711, w712, w1266,
      w1270]

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
