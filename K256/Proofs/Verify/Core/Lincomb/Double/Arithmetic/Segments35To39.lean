import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment35 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_35 b_l110d64_36 := by
  replay_segment using code_l110d64_35 from 1518 to 1560
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1442 => ⟨64, v1618 p yy zz sp⟩, 1477 => ⟨64, v1623 p yy zz sp⟩, 1486 => ⟨64,
      v1556 p yy zz sp⟩, 1488 => ⟨64, v1626 p yy zz sp⟩, 1490 => ⟨64, v1625 p yy zz sp⟩, 1500 => ⟨64, v1630
      p yy zz sp⟩, 1503 => ⟨64, v1631 p yy zz sp⟩, 1513 => ⟨64, v1640 p yy zz sp⟩, 1515 => ⟨64, v1641 p yy
      zz sp⟩, 1516 => Value.ofBool (addSpec (v1637 p yy zz sp) (v1624 p yy zz sp)).2.CF]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w679, v1580, v1620, v1622, v1624, v1633, v1637, v1642, v1643, v1644, v1645, v1646, v1647,
      v1648, v1649, v1650, v1651, v1652, v1653, v1654, v1655, v1656, v1657, v1658, v1659, v1660, v1661,
      v1662]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment36 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_36 b_l110d64_37 := by
  replay_segment using code_l110d64_36 from 1560 to 1606
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1462 => ⟨64, w378 p yy zz sp⟩, 1464 => ⟨64, w349 p yy zz sp⟩, 1540 => ⟨64,
      v1658 p yy zz sp⟩, 1556 => ⟨64, v1662 p yy zz sp⟩, 1558 => ⟨64, v1661 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w721, w722, v1580, v1663, v1664, v1665, v1666, v1667, v1668, v1669, v1670, v1671, v1672,
      v1673, v1674, v1675, v1676, v1677, v1678, v1679]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment37 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_37 b_l110d64_38 := by
  replay_segment using code_l110d64_37 from 1606 to 1649
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1536 => ⟨64, v1657 p yy zz sp⟩, 1549 => ⟨64, w375 p yy zz sp⟩, 1560 => ⟨64,
      v1663 p yy zz sp⟩, 1586 => ⟨64, v1560 p yy zz sp⟩, 1601 => ⟨64, v1676 p yy zz sp⟩, 1604 => ⟨64, v1679
      p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, v1580, v1680, v1681, v1682, v1683, v1684, v1685, v1686, v1687, v1688, v1689, v1690, v1691,
      v1692, v1693, v1694, v1695, v1696, v1697, v1698]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment38 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_38 b_l110d64_39 := by
  replay_segment using code_l110d64_38 from 1649 to 1693
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1571 => ⟨64, w386 p yy zz sp⟩, 1582 => ⟨64, w388 p yy zz sp⟩, 1635 => ⟨64,
      v1690 p yy zz sp⟩, 1646 => ⟨64, v1698 p yy zz sp⟩, 1647 => ⟨64, v1697 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w764, w765, v1580, v1699, v1700, v1701, v1702, v1703, v1704, v1705, v1706, v1707, v1708,
      v1709]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment39 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_39 b_l110d64_40 := by
  replay_segment using code_l110d64_39 from 1693 to 1739
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1611 => ⟨64, v1684 p yy zz sp⟩, 1633 => ⟨64, v1694 p yy zz sp⟩, 1649 => ⟨64,
      v1697 p yy zz sp⟩, 1651 => ⟨64, v1698 p yy zz sp⟩, 1664 => ⟨64, w59 p yy zz sp⟩, 1680 => ⟨64, w349 p
      yy zz sp⟩, 1683 => ⟨64, w764 p yy zz sp⟩, 1688 => ⟨64, v1707 p yy zz sp⟩, 1690 => ⟨64, v1708 p yy zz
      sp⟩, 1691 => Value.ofBool (addSpec (w765 p yy zz sp) (v1704 p yy zz sp)).2.CF]
    normalize [w1, w2, w3, w4, w5, w6, w28, w40, w41, w43, w44, w45, w46, w50, w51, w57, w58, w59, w60, w61,
      w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w78, w79, w80, w81, w82,
      w83, w85, w86, w90, w91, w92, w93, w94, w95, w96, w97, w98, w99, w100, w101, w102, w103, w104, w105,
      w106, w107, w108, w109, w110, w111, w112, w113, w114, w115, w116, w117, w118, w119, w120, w121, w122,
      w123, w124, w125, w126, w127, w128, w129, w130, w131, w132, w133, w134, w135, w136, w137, w138, w139,
      w140, w141, w142, w143, w144, w145, w146, w147, w148, w149, w150, w151, w152, w153, w154, w155, w156,
      w157, w158, w159, w160, w161, w162, w163, w164, w165, w166, w167, w168, w169, w170, w171, w172, w173,
      w174, w175, w176, w177, w178, w179, w180, w181, w182, w183, w184, w185, w186, w187, w188, w189, w190,
      w191, w192, w193, w194, w195, w196, w197, w198, w199, w200, w201, w202, w203, w204, w205, w206, w207,
      w208, w209, w210, w211, w212, w213, w214, w215, w216, w217, w218, w219, w220, w221, w222, w223, w224,
      w225, w226, w227, w228, w229, w230, w231, w232, w233, w234, w235, w236, w237, w238, w239, w240, w241,
      w242, w243, w244, w245, w246, w247, w248, w249, w250, w251, w252, w253, w254, w255, w256, w257, w258,
      w259, w260, w284, w322, w334, w336, w364, w373, w376, w378, w380, w386, w388, w615, w666, w765, w794,
      w795, v1580, v1700, v1703, v1704, v1709, v1710, v1711, v1712, v1713, v1714, v1715, v1716, v1717,
      v1718, v1719, v1720, v1721, v1722, v1723, v1724, v1725, v1726, v1727, v1728, v1729, v1730, v1731,
      v1732]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
