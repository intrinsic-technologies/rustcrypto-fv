import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment40 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_40 b_l110d64_41 := by
  replay_segment using code_l110d64_40 from 1739 to 1784
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1571 => ⟨64, w386 p yy zz sp⟩, 1582 => ⟨64, w388 p yy zz sp⟩, 1653 => ⟨64,
      w378 p yy zz sp⟩, 1664 => ⟨64, w59 p yy zz sp⟩, 1700 => ⟨64, v1716 p yy zz sp⟩, 1726 => ⟨64, v1728 p
      yy zz sp⟩, 1737 => ⟨64, w375 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, v1580, v1733, v1734, v1735, v1736, v1737, v1738, v1739, v1740, v1741, v1742, v1743, v1744,
      v1745, v1746, v1747, v1748, v1749]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment41 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_41 b_l110d64_42 := by
  replay_segment using code_l110d64_41 from 1784 to 1828
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1724 => ⟨64, v1732 p yy zz sp⟩, 1733 => ⟨64, w794 p yy zz sp⟩, 1735 => ⟨64,
      w795 p yy zz sp⟩, 1742 => ⟨64, v1733 p yy zz sp⟩, 1744 => ⟨64, v1734 p yy zz sp⟩, 1751 => ⟨64, v1736 p
      yy zz sp⟩, 1753 => ⟨64, v1735 p yy zz sp⟩, 1779 => ⟨64, v1746 p yy zz sp⟩, 1782 => ⟨64, v1749 p yy zz
      sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, v1580, v1750, v1751, v1752, v1753, v1754, v1755, v1756, v1757, v1758, v1759, v1760, v1761,
      v1762, v1763, v1764, v1765, v1766, v1767, v1768, v1769, v1770, v1771, v1772]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment42 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_42 b_l110d64_43 := by
  replay_segment using code_l110d64_42 from 1828 to 1868
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1790 => ⟨64, w1 p yy zz sp⟩, 1815 => ⟨64, v1769 p yy zz sp⟩, 1821 => ⟨64,
      v1770 p yy zz sp⟩, 1823 => ⟨64, v1771 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w847, w848, w849, w850, v1580, v1773, v1774, v1775, v1776, v1777, v1778, v1779, v1780,
      v1781, v1782, v1783]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment43 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_43 b_l110d64_44 := by
  replay_segment using code_l110d64_43 from 1868 to 1909
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1846 => ⟨64, v1783 p yy zz sp⟩, 1866 => ⟨64, w257 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w851, w852, w853, w854, w856, w857, v1580, v1784, v1786]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment44 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_44 b_l110d64_45 := by
  replay_segment using code_l110d64_44 from 1909 to 1951
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1850 => ⟨64, w17 p yy zz sp⟩, 1892 => ⟨64, w853 p yy zz sp⟩, 1894 => ⟨64, w854
      p yy zz sp⟩, 1896 => ⟨64, w11 p yy zz sp⟩, 1900 => ⟨64, w857 p yy zz sp⟩, 1903 => ⟨64, w857 p yy zz
      sp⟩, 1905 => ⟨64, w856 p yy zz sp⟩, 1907 => ⟨64, v1786 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w861, w862, w863, w865, w866, w867, w868, w869, w870, w871, w872, w873, w874, w875, w876,
      w877, w878, w879, w880, w881, w882, w883, w888, v1580, v1788]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
