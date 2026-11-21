import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment30 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_30 b_l110d64_31 := by
  replay_segment using code_l110d64_30 from 1309 to 1344
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1207 => ⟨64, w59 p yy zz sp⟩, 1249 => ⟨64, w59 p yy zz sp⟩, 1256 => ⟨64, w599
      p yy zz sp⟩, 1263 => ⟨64, w257 p yy zz sp⟩, 1277 => ⟨64, v1569 p yy zz sp⟩, 1293 => ⟨64, v1573 p yy zz
      sp⟩, 1303 => ⟨64, v1575 p yy zz sp⟩, 1307 => ⟨64, v1577 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336, w364,
      w373, w615, w628, w629, w630, w632, w666, v1578, v1579, v1580, v1581, v1582, v1583, v1584, v1586,
      v1587, v1588]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment31 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_31 b_l110d64_32 := by
  replay_segment using code_l110d64_31 from 1344 to 1387
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1326 => ⟨64, v1579 p yy zz sp⟩, 1342 => ⟨64, w59 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w645, w646, w666, v1580, v1589, v1590, v1591, v1592, v1593, v1594, v1595, v1596, v1597,
      BitVec.mul_one]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment32 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_32 b_l110d64_33 := by
  replay_segment using code_l110d64_32 from 1387 to 1431
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1369 => ⟨64, v1592 p yy zz sp⟩, 1372 => ⟨64, v1595 p yy zz sp⟩, 1383 => ⟨64,
      v1596 p yy zz sp⟩, 1385 => ⟨64, v1597 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, v1580, v1598, v1599, v1600, v1601, v1602, v1603, v1604, v1605, v1606, v1607, v1608, v1609,
      v1610, v1611]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment33 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_33 b_l110d64_34 := by
  replay_segment using code_l110d64_33 from 1431 to 1472
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1344 => ⟨64, w374 p yy zz sp⟩, 1358 => ⟨64, w375 p yy zz sp⟩, 1374 => ⟨64,
      w378 p yy zz sp⟩, 1405 => ⟨64, v1604 p yy zz sp⟩, 1408 => ⟨64, v1607 p yy zz sp⟩, 1414 => ⟨64, v1566 p
      yy zz sp⟩, 1427 => ⟨64, v1611 p yy zz sp⟩, 1429 => ⟨64, w1 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w678, w679, v1580, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621,
      v1622]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment34 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_34 b_l110d64_35 := by
  replay_segment using code_l110d64_34 from 1472 to 1518
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1378 => ⟨64, v1560 p yy zz sp⟩, 1392 => ⟨64, w386 p yy zz sp⟩, 1396 => ⟨64,
      v1556 p yy zz sp⟩, 1410 => ⟨64, w388 p yy zz sp⟩, 1419 => ⟨64, v1608 p yy zz sp⟩, 1423 => ⟨64, v1610 p
      yy zz sp⟩, 1456 => ⟨64, v1621 p yy zz sp⟩, 1458 => ⟨64, v1622 p yy zz sp⟩, 1470 => ⟨64, w679 p yy zz
      sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, v1580, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1633, v1634, v1635,
      v1636, v1637, v1638, v1639, v1640, v1641, v1642]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
