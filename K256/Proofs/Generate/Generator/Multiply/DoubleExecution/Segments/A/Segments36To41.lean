import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Sec1.Affine.Uncompressed
open Common.Point Common.Field Common.Point.DoubleWords.Replay

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment36 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_36 b_l11d880_37 := by
  replay_segment using code_l11d880_36 from 1562 to 1603
    registers [4 => ⟨64, sp⟩, 1423 => ⟨64, w326 p yy zz sp⟩, 1489 => ⟨64, w349 p yy zz sp⟩, 1555 => ⟨64,
      w710 p yy zz sp⟩, 1557 => ⟨64, w711 p yy zz sp⟩, 1558 => Value.ofBool (addSpec (w707 p yy zz sp) (w684
      p yy zz sp)).2.CF] slots 38
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w641, w642, w645, w646, w647, w648, w649, w650, w651, w652, w653, w654, w655,
      w656, w657, w658, w659, w660, w661, w662, w663, w664, w665, w666, w667, w668, w669, w671, w672, w673,
      w675, w677, w679, w681, w683, w684, w688, w691, w695, w699, w703, w707, w712, w713, w714, w715, w716,
      w717, w718, w719, w720, w721, w722, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment37 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_37 b_l11d880_38 := by
  replay_segment using code_l11d880_37 from 1603 to 1648
    registers [4 => ⟨64, sp⟩, 1560 => ⟨64, w711 p yy zz sp⟩, 1563 => ⟨64, w714 p yy zz sp⟩, 1581 => ⟨64,
      w717 p yy zz sp⟩, 1583 => ⟨64, w718 p yy zz sp⟩, 1590 => ⟨64, w719 p yy zz sp⟩, 1592 => ⟨64, w720 p yy
      zz sp⟩, 1599 => ⟨64, w721 p yy zz sp⟩, 1601 => ⟨64, w722 p yy zz sp⟩] slots 40
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w723, w724, w725, w726, w727, w728, w729, w730, w731, w732, w733, w734,
      w735, w736, w737, w738, w739, w740, w741, w742, w743, w744, w745, w746, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment38 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_38 b_l11d880_39 := by
  replay_segment using code_l11d880_38 from 1648 to 1691
    registers [4 => ⟨64, sp⟩, 1565 => ⟨64, w374 p yy zz sp⟩, 1574 => ⟨64, w375 p yy zz sp⟩, 1609 => ⟨64,
      w724 p yy zz sp⟩, 1613 => ⟨64, w339 p yy zz sp⟩, 1646 => ⟨64, w746 p yy zz sp⟩] slots 40
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w747, w748, w749, w750, w751, w752, w753, w754, w755, w756, w757, w758,
      w759, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment39 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_39 b_l11d880_40 := by
  replay_segment using code_l11d880_39 from 1691 to 1735
    registers [4 => ⟨64, sp⟩, 1594 => ⟨64, w386 p yy zz sp⟩, 1640 => ⟨64, w744 p yy zz sp⟩, 1659 => ⟨64,
      w750 p yy zz sp⟩, 1662 => ⟨64, w753 p yy zz sp⟩, 1687 => ⟨64, w759 p yy zz sp⟩, 1689 => ⟨64, w758 p yy
      zz sp⟩] slots 40
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w760, w761, w762, w763, w764, w765, w766, w767, w768, w769, w770, w771,
      w772, w773, w774, w775, w776, w777, w778, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment40 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_40 b_l11d880_41 := by
  replay_segment using code_l11d880_40 from 1735 to 1780
    registers [4 => ⟨64, sp⟩, 1673 => ⟨64, w326 p yy zz sp⟩, 1678 => ⟨64, w756 p yy zz sp⟩, 1680 => ⟨64,
      w757 p yy zz sp⟩, 1691 => ⟨64, w760 p yy zz sp⟩, 1713 => ⟨64, w349 p yy zz sp⟩, 1728 => ⟨64, w774 p yy
      zz sp⟩] slots 40
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w779, w780, w781, w782, w783, w784, w785, w786, w787, w788, w789, w790,
      w791, w792, w793, w794, w795, w796, w797, w798, w799, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment41 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_41 b_l11d880_42 := by
  replay_segment using code_l11d880_41 from 1780 to 1823
    registers [4 => ⟨64, sp⟩, 1594 => ⟨64, w386 p yy zz sp⟩, 1700 => ⟨64, w363 p yy zz sp⟩, 1709 => ⟨64,
      w388 p yy zz sp⟩, 1733 => ⟨64, w778 p yy zz sp⟩, 1754 => ⟨64, w790 p yy zz sp⟩, 1757 => ⟨64, w793 p yy
      zz sp⟩, 1777 => ⟨64, w799 p yy zz sp⟩, 1778 => ⟨64, w798 p yy zz sp⟩] slots 37
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w800, w801, w802, w803, w804, w805, w806, w807, w808, w809, w810, w811,
      w812, w813, w814, w1266, w1270]

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
