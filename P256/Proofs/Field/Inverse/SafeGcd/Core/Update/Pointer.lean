import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Model

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift

private theorem v1b15bc_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b15bc { p with modulusPtr := ptr } = v1b15bc p := by
  simp only [v1b15bc]

private theorem v1b15c0_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b15c0 { p with modulusPtr := ptr } = v1b15c0 p := by
  simp only [v1b15c0, v1b15bc_withPtr]

private theorem v1b15c3_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b15c3 { p with modulusPtr := ptr } = v1b15c3 p := by
  simp only [v1b15c3, v1b15c0_withPtr]

private theorem v1b15dc_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b15dc { p with modulusPtr := ptr } = v1b15dc p := by
  simp only [v1b15dc, v1b15c3_withPtr]

private theorem v1b15ed_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b15ed { p with modulusPtr := ptr } = v1b15ed p := by
  simp only [v1b15ed, v1b15c3_withPtr]

private theorem v1b15ff_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b15ff { p with modulusPtr := ptr } = v1b15ff p := by
  simp only [v1b15ff, v1b15c3_withPtr]

private theorem v1b1611_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1611 { p with modulusPtr := ptr } = v1b1611 p := by
  simp only [v1b1611, v1b15c3_withPtr]

private theorem v1b1614_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1614 { p with modulusPtr := ptr } = v1b1614 p := by
  simp only [v1b1614, v1b15dc_withPtr, v1b15ed_withPtr]

private theorem v1b161c_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b161c { p with modulusPtr := ptr } = v1b161c p := by
  simp only [v1b161c, v1b15ed_withPtr, v1b15ff_withPtr, v1b1614_withPtr]

private theorem v1b161f_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b161f { p with modulusPtr := ptr } = v1b161f p := by
  simp only [v1b161f, v1b15ff_withPtr, v1b1611_withPtr, v1b161c_withPtr]

private theorem v1b1622_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1622 { p with modulusPtr := ptr } = v1b1622 p := by
  simp only [v1b1622, v1b1611_withPtr, v1b161f_withPtr]

private theorem v1b1629_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1629 { p with modulusPtr := ptr } = v1b1629 p := by
  simp only [v1b1629, v1b15dc_withPtr]

private theorem v1b162c_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b162c { p with modulusPtr := ptr } = v1b162c p := by
  simp only [v1b162c]

private theorem v1b1632_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1632 { p with modulusPtr := ptr } = v1b1632 p := by
  simp only [v1b1632, v1b15dc_withPtr, v1b162c_withPtr]

private theorem v1b1635_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1635 { p with modulusPtr := ptr } = v1b1635 p := by
  simp only [v1b1635, v1b15dc_withPtr, v1b162c_withPtr]

private theorem v1b163d_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b163d { p with modulusPtr := ptr } = v1b163d p := by
  simp only [v1b163d, v1b1629_withPtr, v1b1635_withPtr]

private theorem v1b1640_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1640 { p with modulusPtr := ptr } = v1b1640 p := by
  simp only [v1b1640, v1b1632_withPtr, v1b163d_withPtr]

private theorem v1b164e_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b164e { p with modulusPtr := ptr } = v1b164e p := by
  simp only [v1b164e, v1b1640_withPtr]

private theorem v1b165f_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b165f { p with modulusPtr := ptr } = v1b165f p := by
  simp only [v1b165f, v1b164e_withPtr]

private theorem v1b1667_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1667 { p with modulusPtr := ptr } = v1b1667 p := by
  simp only [v1b1667, v1b1614_withPtr]

private theorem v1b166a_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b166a { p with modulusPtr := ptr } = v1b166a p := by
  simp only [v1b166a, v1b165f_withPtr]

private theorem v1b166e_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b166e { p with modulusPtr := ptr } = v1b166e p := by
  simp only [v1b166e, v1b1667_withPtr, v1b166a_withPtr]

private theorem v1b1671_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1671 { p with modulusPtr := ptr } = v1b1671 p := by
  simp only [v1b1671]

private theorem v1b1677_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1677 { p with modulusPtr := ptr } = v1b1677 p := by
  simp only [v1b1677, v1b1614_withPtr, v1b1671_withPtr]

private theorem v1b167a_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b167a { p with modulusPtr := ptr } = v1b167a p := by
  simp only [v1b167a, v1b1614_withPtr, v1b1671_withPtr]

private theorem v1b167d_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b167d { p with modulusPtr := ptr } = v1b167d p := by
  simp only [v1b167d, v1b166e_withPtr, v1b167a_withPtr]

private theorem v1b1680_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1680 { p with modulusPtr := ptr } = v1b1680 p := by
  simp only [v1b1680, v1b1677_withPtr, v1b167d_withPtr]

private theorem v1b1683_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1683 { p with modulusPtr := ptr } = v1b1683 p := by
  simp only [v1b1683, v1b1680_withPtr]

private theorem v1b168f_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b168f { p with modulusPtr := ptr } = v1b168f p := by
  simp only [v1b168f, v1b1683_withPtr]

private theorem v1b1697_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1697 { p with modulusPtr := ptr } = v1b1697 p := by
  simp only [v1b1697, v1b161c_withPtr]

private theorem v1b169a_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b169a { p with modulusPtr := ptr } = v1b169a p := by
  simp only [v1b169a, v1b168f_withPtr]

private theorem v1b169e_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b169e { p with modulusPtr := ptr } = v1b169e p := by
  simp only [v1b169e, v1b1697_withPtr, v1b169a_withPtr]

private theorem v1b16a1_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16a1 { p with modulusPtr := ptr } = v1b16a1 p := by
  simp only [v1b16a1]

private theorem v1b16a7_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16a7 { p with modulusPtr := ptr } = v1b16a7 p := by
  simp only [v1b16a7, v1b161c_withPtr, v1b16a1_withPtr]

private theorem v1b16aa_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16aa { p with modulusPtr := ptr } = v1b16aa p := by
  simp only [v1b16aa, v1b161c_withPtr, v1b16a1_withPtr]

private theorem v1b16ad_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16ad { p with modulusPtr := ptr } = v1b16ad p := by
  simp only [v1b16ad, v1b169e_withPtr, v1b16aa_withPtr]

private theorem v1b16b0_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16b0 { p with modulusPtr := ptr } = v1b16b0 p := by
  simp only [v1b16b0, v1b16a7_withPtr, v1b16ad_withPtr]

private theorem v1b16b3_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16b3 { p with modulusPtr := ptr } = v1b16b3 p := by
  simp only [v1b16b3, v1b16b0_withPtr]

private theorem v1b16bf_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16bf { p with modulusPtr := ptr } = v1b16bf p := by
  simp only [v1b16bf, v1b16b3_withPtr]

private theorem v1b16c7_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16c7 { p with modulusPtr := ptr } = v1b16c7 p := by
  simp only [v1b16c7, v1b161f_withPtr]

private theorem v1b16ca_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16ca { p with modulusPtr := ptr } = v1b16ca p := by
  simp only [v1b16ca, v1b16bf_withPtr]

private theorem v1b16ce_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16ce { p with modulusPtr := ptr } = v1b16ce p := by
  simp only [v1b16ce, v1b16c7_withPtr, v1b16ca_withPtr]

private theorem v1b16d1_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16d1 { p with modulusPtr := ptr } = v1b16d1 p := by
  simp only [v1b16d1]

private theorem v1b16d7_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16d7 { p with modulusPtr := ptr } = v1b16d7 p := by
  simp only [v1b16d7, v1b161f_withPtr, v1b16d1_withPtr]

private theorem v1b16da_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16da { p with modulusPtr := ptr } = v1b16da p := by
  simp only [v1b16da, v1b161f_withPtr, v1b16d1_withPtr]

private theorem v1b16e0_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16e0 { p with modulusPtr := ptr } = v1b16e0 p := by
  simp only [v1b16e0, v1b16ce_withPtr, v1b16da_withPtr]

private theorem v1b16e3_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16e3 { p with modulusPtr := ptr } = v1b16e3 p := by
  simp only [v1b16e3, v1b16d7_withPtr, v1b16e0_withPtr]

private theorem v1b16e6_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16e6 { p with modulusPtr := ptr } = v1b16e6 p := by
  simp only [v1b16e6, v1b16e3_withPtr]

private theorem v1b16f1_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16f1 { p with modulusPtr := ptr } = v1b16f1 p := by
  simp only [v1b16f1, v1b16e6_withPtr]

private theorem v1b16f9_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16f9 { p with modulusPtr := ptr } = v1b16f9 p := by
  simp only [v1b16f9, v1b1622_withPtr]

private theorem v1b16fc_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b16fc { p with modulusPtr := ptr } = v1b16fc p := by
  simp only [v1b16fc]

private theorem v1b1702_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1702 { p with modulusPtr := ptr } = v1b1702 p := by
  simp only [v1b1702, v1b1622_withPtr, v1b16fc_withPtr]

private theorem v1b1705_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1705 { p with modulusPtr := ptr } = v1b1705 p := by
  simp only [v1b1705, v1b1622_withPtr, v1b16fc_withPtr]

private theorem v1b1708_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1708 { p with modulusPtr := ptr } = v1b1708 p := by
  simp only [v1b1708, v1b16f1_withPtr]

private theorem v1b170c_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b170c { p with modulusPtr := ptr } = v1b170c p := by
  simp only [v1b170c, v1b16f9_withPtr, v1b1708_withPtr]

private theorem v1b170f_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b170f { p with modulusPtr := ptr } = v1b170f p := by
  simp only [v1b170f, v1b1705_withPtr, v1b170c_withPtr]

private theorem v1b1712_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1712 { p with modulusPtr := ptr } = v1b1712 p := by
  simp only [v1b1712, v1b1702_withPtr, v1b170f_withPtr]

private theorem v1b1715_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1715 { p with modulusPtr := ptr } = v1b1715 p := by
  simp only [v1b1715, v1b1712_withPtr]

private theorem v1b172b_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b172b { p with modulusPtr := ptr } = v1b172b p := by
  simp only [v1b172b, v1b1629_withPtr]

private theorem v1b1734_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1734 { p with modulusPtr := ptr } = v1b1734 p := by
  simp only [v1b1734, v1b1629_withPtr, v1b166e_withPtr]

private theorem v1b173c_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b173c { p with modulusPtr := ptr } = v1b173c p := by
  simp only [v1b173c, v1b169e_withPtr, v1b1734_withPtr]

private theorem v1b173f_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b173f { p with modulusPtr := ptr } = v1b173f p := by
  simp only [v1b173f, v1b16ce_withPtr, v1b173c_withPtr]

private theorem v1b17b1_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17b1 { p with modulusPtr := ptr } = v1b17b1 p := by
  simp only [v1b17b1, v1b16ce_withPtr, v1b173f_withPtr]

private theorem v1b17b4_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17b4 { p with modulusPtr := ptr } = v1b17b4 p := by
  simp only [v1b17b4, v1b1715_withPtr]

private theorem v1b17b7_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17b7 { p with modulusPtr := ptr } = v1b17b7 p := by
  simp only [v1b17b7, v1b17b1_withPtr, v1b17b4_withPtr]

private theorem v1b17ba_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17ba { p with modulusPtr := ptr } = v1b17ba p := by
  simp only [v1b17ba, v1b16ce_withPtr, v1b17b7_withPtr]

private theorem v1b17bd_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17bd { p with modulusPtr := ptr } = v1b17bd p := by
  simp only [v1b17bd, v1b169e_withPtr, v1b173c_withPtr]

private theorem v1b17c0_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17c0 { p with modulusPtr := ptr } = v1b17c0 p := by
  simp only [v1b17c0, v1b1715_withPtr]

private theorem v1b17c3_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17c3 { p with modulusPtr := ptr } = v1b17c3 p := by
  simp only [v1b17c3, v1b17bd_withPtr, v1b17c0_withPtr]

private theorem v1b17c6_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17c6 { p with modulusPtr := ptr } = v1b17c6 p := by
  simp only [v1b17c6, v1b169e_withPtr, v1b17c3_withPtr]

private theorem v1b17c9_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17c9 { p with modulusPtr := ptr } = v1b17c9 p := by
  simp only [v1b17c9, v1b166e_withPtr, v1b1734_withPtr]

private theorem v1b17cc_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17cc { p with modulusPtr := ptr } = v1b17cc p := by
  simp only [v1b17cc, v1b1715_withPtr]

private theorem v1b17cf_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17cf { p with modulusPtr := ptr } = v1b17cf p := by
  simp only [v1b17cf, v1b17c9_withPtr, v1b17cc_withPtr]

private theorem v1b17d2_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17d2 { p with modulusPtr := ptr } = v1b17d2 p := by
  simp only [v1b17d2, v1b166e_withPtr, v1b17cf_withPtr]

private theorem v1b17d5_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17d5 { p with modulusPtr := ptr } = v1b17d5 p := by
  simp only [v1b17d5, v1b173f_withPtr]

private theorem v1b17db_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17db { p with modulusPtr := ptr } = v1b17db p := by
  simp only [v1b17db, v1b170c_withPtr]

private theorem v1b17de_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17de { p with modulusPtr := ptr } = v1b17de p := by
  simp only [v1b17de, v1b17d5_withPtr, v1b17db_withPtr]

private theorem v1b17e1_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17e1 { p with modulusPtr := ptr } = v1b17e1 p := by
  simp only [v1b17e1, v1b170c_withPtr, v1b17de_withPtr]

private theorem v1b17ea_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17ea { p with modulusPtr := ptr } = v1b17ea p := by
  simp only [v1b17ea, v1b1715_withPtr]

private theorem v1b17ed_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17ed { p with modulusPtr := ptr } = v1b17ed p := by
  simp only [v1b17ed, v1b17e1_withPtr, v1b17ea_withPtr]

private theorem v1b17f0_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17f0 { p with modulusPtr := ptr } = v1b17f0 p := by
  simp only [v1b17f0, v1b170c_withPtr, v1b17ed_withPtr]

private theorem v1b17fa_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b17fa { p with modulusPtr := ptr } = v1b17fa p := by
  simp only [v1b17fa, v1b17f0_withPtr]

private theorem v1b1802_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1802 { p with modulusPtr := ptr } = v1b1802 p := by
  simp only [v1b1802, v1b1629_withPtr, v1b172b_withPtr]

private theorem v1b1805_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1805 { p with modulusPtr := ptr } = v1b1805 p := by
  simp only [v1b1805, v1b1715_withPtr]

private theorem v1b1811_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1811 { p with modulusPtr := ptr } = v1b1811 p := by
  simp only [v1b1811, v1b17ba_withPtr]

private theorem v1b1816_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1816 { p with modulusPtr := ptr } = v1b1816 p := by
  simp only [v1b1816, v1b17ba_withPtr]

private theorem v1b181e_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b181e { p with modulusPtr := ptr } = v1b181e p := by
  simp only [v1b181e, v1b17c6_withPtr]

private theorem v1b1821_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1821 { p with modulusPtr := ptr } = v1b1821 p := by
  simp only [v1b1821, v1b1802_withPtr, v1b1805_withPtr]

private theorem v1b1824_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1824 { p with modulusPtr := ptr } = v1b1824 p := by
  simp only [v1b1824, v1b1629_withPtr, v1b1821_withPtr]

private theorem v1b1827_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1827 { p with modulusPtr := ptr } = v1b1827 p := by
  simp only [v1b1827, v1b1816_withPtr, v1b181e_withPtr]

private theorem v1b182c_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b182c { p with modulusPtr := ptr } = v1b182c p := by
  simp only [v1b182c, v1b17c6_withPtr]

private theorem v1b1834_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1834 { p with modulusPtr := ptr } = v1b1834 p := by
  simp only [v1b1834, v1b17d2_withPtr]

private theorem v1b1839_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1839 { p with modulusPtr := ptr } = v1b1839 p := by
  simp only [v1b1839, v1b17d2_withPtr]

private theorem v1b183e_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b183e { p with modulusPtr := ptr } = v1b183e p := by
  simp only [v1b183e, v1b1824_withPtr]

private theorem v1b1841_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1841 { p with modulusPtr := ptr } = v1b1841 p := by
  simp only [v1b1841, v1b182c_withPtr, v1b1834_withPtr]

private theorem v1b1844_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1844 { p with modulusPtr := ptr } = v1b1844 p := by
  simp only [v1b1844, v1b1839_withPtr, v1b183e_withPtr]

private theorem v1b184f_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b184f { p with modulusPtr := ptr } = v1b184f p := by
  simp only [v1b184f, v1b1844_withPtr]

private theorem v1b1855_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1855 { p with modulusPtr := ptr } = v1b1855 p := by
  simp only [v1b1855, v1b1844_withPtr]

private theorem v1b185b_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b185b { p with modulusPtr := ptr } = v1b185b p := by
  simp only [v1b185b, v1b1855_withPtr]

private theorem v1b185e_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b185e { p with modulusPtr := ptr } = v1b185e p := by
  simp only [v1b185e, v1b1855_withPtr]

private theorem v1b1861_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1861 { p with modulusPtr := ptr } = v1b1861 p := by
  simp only [v1b1861, v1b184f_withPtr, v1b185e_withPtr]

private theorem v1b1864_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1864 { p with modulusPtr := ptr } = v1b1864 p := by
  simp only [v1b1864, v1b185b_withPtr, v1b1861_withPtr]

private theorem v1b1867_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1867 { p with modulusPtr := ptr } = v1b1867 p := by
  simp only [v1b1867, v1b1864_withPtr]

private theorem v1b1878_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1878 { p with modulusPtr := ptr } = v1b1878 p := by
  simp only [v1b1878, v1b1867_withPtr]

private theorem v1b1885_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1885 { p with modulusPtr := ptr } = v1b1885 p := by
  simp only [v1b1885, v1b1841_withPtr]

private theorem v1b1888_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1888 { p with modulusPtr := ptr } = v1b1888 p := by
  simp only [v1b1888, v1b1878_withPtr]

private theorem v1b188c_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b188c { p with modulusPtr := ptr } = v1b188c p := by
  simp only [v1b188c, v1b1885_withPtr, v1b1888_withPtr]

private theorem v1b1892_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1892 { p with modulusPtr := ptr } = v1b1892 p := by
  simp only [v1b1892, v1b1841_withPtr]

private theorem v1b1898_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1898 { p with modulusPtr := ptr } = v1b1898 p := by
  simp only [v1b1898, v1b1892_withPtr]

private theorem v1b189b_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b189b { p with modulusPtr := ptr } = v1b189b p := by
  simp only [v1b189b, v1b1892_withPtr]

private theorem v1b189e_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b189e { p with modulusPtr := ptr } = v1b189e p := by
  simp only [v1b189e, v1b188c_withPtr, v1b189b_withPtr]

private theorem v1b18a1_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18a1 { p with modulusPtr := ptr } = v1b18a1 p := by
  simp only [v1b18a1, v1b1898_withPtr, v1b189e_withPtr]

private theorem v1b18a4_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18a4 { p with modulusPtr := ptr } = v1b18a4 p := by
  simp only [v1b18a4, v1b18a1_withPtr]

private theorem v1b18af_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18af { p with modulusPtr := ptr } = v1b18af p := by
  simp only [v1b18af, v1b18a4_withPtr]

private theorem v1b18bc_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18bc { p with modulusPtr := ptr } = v1b18bc p := by
  simp only [v1b18bc, v1b1827_withPtr]

private theorem v1b18bf_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18bf { p with modulusPtr := ptr } = v1b18bf p := by
  simp only [v1b18bf, v1b18af_withPtr]

private theorem v1b18c3_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18c3 { p with modulusPtr := ptr } = v1b18c3 p := by
  simp only [v1b18c3, v1b18bc_withPtr, v1b18bf_withPtr]

private theorem v1b18c9_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18c9 { p with modulusPtr := ptr } = v1b18c9 p := by
  simp only [v1b18c9, v1b1827_withPtr]

private theorem v1b18cf_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18cf { p with modulusPtr := ptr } = v1b18cf p := by
  simp only [v1b18cf, v1b18c9_withPtr]

private theorem v1b18d2_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18d2 { p with modulusPtr := ptr } = v1b18d2 p := by
  simp only [v1b18d2, v1b18c9_withPtr]

private theorem v1b18d5_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18d5 { p with modulusPtr := ptr } = v1b18d5 p := by
  simp only [v1b18d5, v1b18c3_withPtr, v1b18d2_withPtr]

private theorem v1b18d8_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18d8 { p with modulusPtr := ptr } = v1b18d8 p := by
  simp only [v1b18d8, v1b18cf_withPtr, v1b18d5_withPtr]

private theorem v1b18db_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18db { p with modulusPtr := ptr } = v1b18db p := by
  simp only [v1b18db, v1b18d8_withPtr]

private theorem v1b18e6_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18e6 { p with modulusPtr := ptr } = v1b18e6 p := by
  simp only [v1b18e6, v1b18db_withPtr]

private theorem v1b18eb_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18eb { p with modulusPtr := ptr } = v1b18eb p := by
  simp only [v1b18eb, v1b17fa_withPtr, v1b1811_withPtr]

private theorem v1b18f6_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18f6 { p with modulusPtr := ptr } = v1b18f6 p := by
  simp only [v1b18f6, v1b18eb_withPtr]

private theorem v1b18f9_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18f9 { p with modulusPtr := ptr } = v1b18f9 p := by
  simp only [v1b18f9, v1b18e6_withPtr]

private theorem v1b18fd_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b18fd { p with modulusPtr := ptr } = v1b18fd p := by
  simp only [v1b18fd, v1b18f6_withPtr, v1b18f9_withPtr]

private theorem v1b1903_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1903 { p with modulusPtr := ptr } = v1b1903 p := by
  simp only [v1b1903, v1b18eb_withPtr]

private theorem v1b1909_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1909 { p with modulusPtr := ptr } = v1b1909 p := by
  simp only [v1b1909, v1b1903_withPtr]

private theorem v1b190c_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b190c { p with modulusPtr := ptr } = v1b190c p := by
  simp only [v1b190c, v1b1903_withPtr]

private theorem v1b190f_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b190f { p with modulusPtr := ptr } = v1b190f p := by
  simp only [v1b190f, v1b18fd_withPtr, v1b190c_withPtr]

private theorem v1b1912_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1912 { p with modulusPtr := ptr } = v1b1912 p := by
  simp only [v1b1912, v1b1909_withPtr, v1b190f_withPtr]

private theorem v1b1915_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1915 { p with modulusPtr := ptr } = v1b1915 p := by
  simp only [v1b1915, v1b1912_withPtr]

private theorem v1b1923_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1923 { p with modulusPtr := ptr } = v1b1923 p := by
  simp only [v1b1923, v1b17f0_withPtr]

private theorem v1b1926_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1926 { p with modulusPtr := ptr } = v1b1926 p := by
  simp only [v1b1926, v1b1915_withPtr]

private theorem v1b1930_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1930 { p with modulusPtr := ptr } = v1b1930 p := by
  simp only [v1b1930, v1b1715_withPtr]

private theorem v1b193b_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b193b { p with modulusPtr := ptr } = v1b193b p := by
  simp only [v1b193b, v1b1923_withPtr, v1b1926_withPtr]

private theorem v1b1977_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1977 { p with modulusPtr := ptr } = v1b1977 p := by
  simp only [v1b1977, v1b1844_withPtr, v1b184f_withPtr]

private theorem v1b197a_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b197a { p with modulusPtr := ptr } = v1b197a p := by
  simp only [v1b197a, v1b1923_withPtr, v1b193b_withPtr]

private theorem v1b197d_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b197d { p with modulusPtr := ptr } = v1b197d p := by
  simp only [v1b197d, v1b1977_withPtr, v1b197a_withPtr]

private theorem v1b1980_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1980 { p with modulusPtr := ptr } = v1b1980 p := by
  simp only [v1b1980, v1b184f_withPtr, v1b197d_withPtr]

private theorem v1b198c_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b198c { p with modulusPtr := ptr } = v1b198c p := by
  simp only [v1b198c, v1b1841_withPtr, v1b188c_withPtr]

private theorem v1b198f_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b198f { p with modulusPtr := ptr } = v1b198f p := by
  simp only [v1b198f, v1b1923_withPtr, v1b193b_withPtr]

private theorem v1b1992_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1992 { p with modulusPtr := ptr } = v1b1992 p := by
  simp only [v1b1992, v1b198c_withPtr, v1b198f_withPtr]

private theorem v1b1995_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b1995 { p with modulusPtr := ptr } = v1b1995 p := by
  simp only [v1b1995, v1b188c_withPtr, v1b1992_withPtr]

private theorem v1b19a1_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b19a1 { p with modulusPtr := ptr } = v1b19a1 p := by
  simp only [v1b19a1, v1b1827_withPtr, v1b18c3_withPtr]

private theorem v1b19a4_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b19a4 { p with modulusPtr := ptr } = v1b19a4 p := by
  simp only [v1b19a4, v1b1923_withPtr, v1b193b_withPtr]

private theorem v1b19a7_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b19a7 { p with modulusPtr := ptr } = v1b19a7 p := by
  simp only [v1b19a7, v1b19a1_withPtr, v1b19a4_withPtr]

private theorem v1b19aa_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b19aa { p with modulusPtr := ptr } = v1b19aa p := by
  simp only [v1b19aa, v1b18c3_withPtr, v1b19a7_withPtr]

private theorem v1b19b6_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b19b6 { p with modulusPtr := ptr } = v1b19b6 p := by
  simp only [v1b19b6, v1b18eb_withPtr, v1b18fd_withPtr]

private theorem v1b19b9_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b19b9 { p with modulusPtr := ptr } = v1b19b9 p := by
  simp only [v1b19b9, v1b1923_withPtr, v1b193b_withPtr]

private theorem v1b19bc_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b19bc { p with modulusPtr := ptr } = v1b19bc p := by
  simp only [v1b19bc, v1b19b6_withPtr, v1b19b9_withPtr]

private theorem v1b19bf_withPtr (p : Inputs) (ptr : BitVec 64) :
    v1b19bf { p with modulusPtr := ptr } = v1b19bf p := by
  simp only [v1b19bf, v1b18fd_withPtr, v1b19bc_withPtr]

theorem resultWords_withPtr (p : Inputs) (ptr : BitVec 64) :
    resultWords { p with modulusPtr := ptr } = resultWords p := by
  simp only [resultWords, v1b1980_withPtr, v1b1995_withPtr, v1b19aa_withPtr, v1b19bf_withPtr]

theorem resultSign_withPtr (p : Inputs) (ptr : BitVec 64) :
    resultSign { p with modulusPtr := ptr } = resultSign p := by
  simp only [resultSign, v1b1930_withPtr]

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift
