import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment70 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_70 b_l110d64_71 := by
  replay_segment using code_l110d64_70 from 3025 to 3070
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2932 => ⟨64, v1556 p yy zz sp⟩, 2943 => ⟨64, v1560 p yy zz sp⟩, 2947 => ⟨64,
      w407 p yy zz sp⟩, 2961 => ⟨64, w349 p yy zz sp⟩, 2965 => ⟨64, w400 p yy zz sp⟩, 2979 => ⟨64, v1564 p
      yy zz sp⟩, 2983 => ⟨64, w398 p yy zz sp⟩, 2995 => ⟨64, v1829 p yy zz sp⟩, 2997 => ⟨64, v1566 p yy zz
      sp⟩, 3001 => ⟨64, w415 p yy zz sp⟩, 3019 => ⟨64, v1834 p yy zz sp⟩, 3021 => ⟨64, v1836 p yy zz sp⟩,
      3022 => Value.ofBool (addSpec (v1835 p yy zz sp) (v1826 p yy zz sp)).2.CF]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1307, w1332, w1333, v1580, v1813, v1815, v1816, v1820, v1825, v1826, v1831, v1833, v1835,
      v1837, v1838, v1839, v1840, v1841, v1842, v1843, v1844, v1845, v1846, v1847, v1848]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment71 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (_rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_71 b_l110d64_72 := by
  replay_segment using code_l110d64_71 from 3070 to 3117
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [2983 => ⟨64, w398 p yy zz sp⟩, 3008 => ⟨64, v1832 p yy zz sp⟩, 3027 => ⟨64, v1840 p yy zz
      sp⟩, 3034 => ⟨64, v1841 p yy zz sp⟩, 3036 => ⟨64, v1842 p yy zz sp⟩, 3043 => ⟨64, v1843 p yy zz sp⟩,
      3045 => ⟨64, v1844 p yy zz sp⟩, 3052 => ⟨64, w1332 p yy zz sp⟩, 3054 => ⟨64, w1333 p yy zz sp⟩, 3061
      => ⟨64, v1845 p yy zz sp⟩, 3063 => ⟨64, v1846 p yy zz sp⟩, 3067 => ⟨64, v1848 p yy zz sp⟩, 3068 =>
      ⟨64, v1847 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, v1580, v1849, v1850, v1851, v1852, v1853, v1854, v1855, v1856, v1857, v1858, v1859, v1860,
      v1861, v1862, v1863, v1864, v1865, v1866, v1867, v1868, v1869, v1870, v1871, v1872, v1873, v1874,
      v1875]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment72 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_72 b_l110d64_73 := by
  replay_segment using code_l110d64_72 from 3117 to 3159
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 3070 => ⟨64, w398 p yy zz sp⟩, 3115 => ⟨64, v1871 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1369, w1370, v1580, v1876, v1877, v1878, v1879, v1880, v1881, v1882, v1883,
      BitVec.mul_one]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment73 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_73 b_l110d64_74 := by
  replay_segment using code_l110d64_73 from 3159 to 3205
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 3113 => ⟨64, v1875 p yy zz sp⟩, 3137 => ⟨64, v1880 p yy zz sp⟩, 3139 => ⟨64,
      v1879 p yy zz sp⟩, 3141 => ⟨64, v1881 p yy zz sp⟩, 3148 => ⟨64, w1369 p yy zz sp⟩, 3150 => ⟨64, w1370
      p yy zz sp⟩, 3154 => ⟨64, v1883 p yy zz sp⟩, 3157 => ⟨64, v1882 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, v1580, v1884, v1885, v1886, v1887, v1888, v1889, v1890, v1891, v1892, v1893, v1894, v1895,
      v1896, v1897, v1898, v1899, v1900, v1901, v1902, v1903, v1904, v1905, v1906, v1907]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment74 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_74 b_l110d64_75 := by
  replay_segment using code_l110d64_74 from 3205 to 3247
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 3119 => ⟨64, v1556 p yy zz sp⟩, 3128 => ⟨64, v1560 p yy zz sp⟩, 3132 => ⟨64,
      w415 p yy zz sp⟩, 3163 => ⟨64, w400 p yy zz sp⟩, 3200 => ⟨64, v1907 p yy zz sp⟩, 3203 => ⟨64, v1906 p
      yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1408, w1409, v1580, v1908, v1909, v1910, v1911, v1912, v1913, v1914, v1915, v1916, v1917,
      BitVec.mul_one]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
