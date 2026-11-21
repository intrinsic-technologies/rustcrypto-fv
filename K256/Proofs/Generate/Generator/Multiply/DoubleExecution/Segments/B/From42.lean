import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Sec1.Affine.Uncompressed
open Common.Point Common.Field Common.Point.DoubleWords.Replay

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment42 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_42 b_l11d880_43 := by
  replay_segment using code_l11d880_42 from 1823 to 1868
    registers [4 => ⟨64, sp⟩, 1771 => ⟨64, w796 p yy zz sp⟩, 1773 => ⟨64, w797 p yy zz sp⟩, 1780 => ⟨64,
      w799 p yy zz sp⟩, 1782 => ⟨64, w798 p yy zz sp⟩, 1784 => ⟨64, w800 p yy zz sp⟩, 1812 => ⟨64, w810 p yy
      zz sp⟩, 1815 => ⟨64, w813 p yy zz sp⟩, 1821 => ⟨64, w814 p yy zz sp⟩] slots 38
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w815, w816, w817, w818, w819, w820, w821, w822, w823, w824, w825, w826,
      w827, w828, w829, w830, w831, w832, w833, w834, w835, w836, w837, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment43 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_43 b_l11d880_44 := by
  replay_segment using code_l11d880_43 from 1868 to 1909
    registers [4 => ⟨64, sp⟩, 1850 => ⟨64, w834 p yy zz sp⟩, 1861 => ⟨64, w837 p yy zz sp⟩, 1864 => ⟨64,
      w836 p yy zz sp⟩, 1866 => ⟨64, w59 p yy zz sp⟩] slots 37
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w838, w839, w840, w841, w842, w843, w844, w845, w846, w847, w848, w849,
      w850, w851, w852, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment44 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_44 b_l11d880_45 := by
  replay_segment using code_l11d880_44 from 1909 to 1948
    registers [4 => ⟨64, sp⟩, 1877 => ⟨64, w843 p yy zz sp⟩, 1880 => ⟨64, w846 p yy zz sp⟩, 1906 => ⟨64,
      w852 p yy zz sp⟩, 1907 => ⟨64, w851 p yy zz sp⟩] slots 40
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w853, w854, w855, w856, w857, w858, w859, w861, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment45 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_45 b_l11d880_46 := by
  replay_segment using code_l11d880_45 from 1948 to 1991
    registers [4 => ⟨64, sp⟩, 1877 => ⟨64, w843 p yy zz sp⟩, 1884 => ⟨64, w17 p yy zz sp⟩, 1916 => ⟨64, w854
      p yy zz sp⟩, 1918 => ⟨64, w853 p yy zz sp⟩, 1926 => ⟨64, w11 p yy zz sp⟩, 1935 => ⟨64, w857 p yy zz
      sp⟩, 1937 => ⟨64, w856 p yy zz sp⟩, 1946 => ⟨64, w861 p yy zz sp⟩] slots 42
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w862, w863, w864, w865, w866, w867, w868, w869, w870, w871, w872, w873,
      w874, w875, w876, w877, w878, w879, w880, w881, w882, w883, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment46 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_46 b_l11d880_47 := by
  replay_segment using code_l11d880_46 from 1991 to 2033
    registers [4 => ⟨64, sp⟩, 1891 => ⟨64, w9 p yy zz sp⟩, 1895 => ⟨64, w18 p yy zz sp⟩, 1902 => ⟨64, w8 p
      yy zz sp⟩, 1930 => ⟨64, w21 p yy zz sp⟩, 1978 => ⟨64, w877 p yy zz sp⟩, 1981 => ⟨64, w880 p yy zz sp⟩,
      1987 => ⟨64, w883 p yy zz sp⟩] slots 39
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w884, w885, w886, w887, w888, w889, w890, w891, w892, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment47 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_47 b_l11d880_48 := by
  replay_segment using code_l11d880_47 from 2033 to 2079
    registers [4 => ⟨64, sp⟩, 1884 => ⟨64, w17 p yy zz sp⟩, 1983 => ⟨64, w881 p yy zz sp⟩, 1998 => ⟨64, w885
      p yy zz sp⟩, 2007 => ⟨64, w887 p yy zz sp⟩, 2009 => ⟨64, w886 p yy zz sp⟩, 2011 => ⟨64, w888 p yy zz
      sp⟩, 2018 => ⟨64, w890 p yy zz sp⟩, 2020 => ⟨64, w889 p yy zz sp⟩, 2022 => ⟨64, w7 p yy zz sp⟩, 2029
      => ⟨64, w891 p yy zz sp⟩, 2031 => ⟨64, w892 p yy zz sp⟩] slots 41
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w893, w894, w895, w896, w897, w898, w899, w900, w901, w902, w903, w904,
      w905, w906, w907, w908, w909, w910, w911, w912, w913, w914, w915, w916, w917, w918, w919, w920, w1266,
      w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment48 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_48 b_l11d880_49 := by
  replay_segment using code_l11d880_48 from 2079 to 2122
    registers [4 => ⟨64, sp⟩, 2002 => ⟨64, w19 p yy zz sp⟩, 2068 => ⟨64, w915 p yy zz sp⟩, 2071 => ⟨64, w918
      p yy zz sp⟩, 2076 => ⟨64, w919 p yy zz sp⟩] slots 40
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w921, w922, w923, w924, w925, w926, w927, w928, w929, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment49 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_49 b_l11d880_50 := by
  replay_segment using code_l11d880_49 from 2122 to 2169
    registers [4 => ⟨64, sp⟩, 2088 => ⟨64, w922 p yy zz sp⟩, 2090 => ⟨64, w921 p yy zz sp⟩, 2103 => ⟨64,
      w925 p yy zz sp⟩, 2105 => ⟨64, w924 p yy zz sp⟩, 2107 => ⟨64, w926 p yy zz sp⟩, 2109 => ⟨64, w927 p yy
      zz sp⟩, 2118 => ⟨64, w929 p yy zz sp⟩, 2120 => ⟨64, w928 p yy zz sp⟩] slots 40
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w930, w931, w932, w933, w934, w935, w936, w937, w938, w939, w940, w941,
      w942, w943, w944, w945, w946, w947, w948, w949, w950, w951, w952, w953, w954, w955, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment50 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_50 b_l11d880_51 := by
  replay_segment using code_l11d880_50 from 2169 to 2210
    registers [4 => ⟨64, sp⟩, 2079 => ⟨64, w919 p yy zz sp⟩, 2081 => ⟨64, w11 p yy zz sp⟩, 2096 => ⟨64, w10
      p yy zz sp⟩, 2113 => ⟨64, w20 p yy zz sp⟩, 2122 => ⟨64, w8 p yy zz sp⟩, 2162 => ⟨64, w952 p yy zz sp⟩,
      2164 => ⟨64, w954 p yy zz sp⟩, 2165 => Value.ofBool (addSpec (w953 p yy zz sp) (w920 p yy zz
      sp)).2.CF, 2167 => ⟨64, w954 p yy zz sp⟩] slots 39
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w847, w848, w849, w850, w851, w852, w853, w854, w856, w857, w861, w862,
      w863, w865, w866, w867, w868, w869, w870, w871, w872, w873, w874, w875, w876, w878, w879, w880, w881,
      w882, w883, w884, w885, w886, w887, w888, w889, w890, w891, w892, w893, w894, w895, w896, w897, w898,
      w899, w900, w901, w902, w903, w904, w905, w906, w907, w908, w909, w910, w911, w912, w913, w914, w916,
      w917, w918, w920, w922, w923, w925, w926, w927, w929, w931, w932, w936, w940, w944, w949, w950, w951,
      w953, w955, w956, w957, w958, w959, w960, w961, w962, w963, w964, w965, w966, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment51 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_51 b_l11d880_52 := by
  replay_segment using code_l11d880_51 from 2210 to 2257
    registers [4 => ⟨64, sp⟩, 2149 => ⟨64, w948 p yy zz sp⟩, 2188 => ⟨64, w960 p yy zz sp⟩, 2190 => ⟨64,
      w961 p yy zz sp⟩, 2199 => ⟨64, w963 p yy zz sp⟩, 2201 => ⟨64, w962 p yy zz sp⟩, 2207 => ⟨64, w966 p yy
      zz sp⟩, 2208 => ⟨64, w965 p yy zz sp⟩] slots 39
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w967, w968, w969, w970, w971, w972, w973, w974, w975, w976, w977, w978,
      w979, w980, w981, w982, w983, w984, w985, w986, w987, w988, w989, w990, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment52 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_52 b_l11d880_53 := by
  replay_segment using code_l11d880_52 from 2257 to 2301
    registers [4 => ⟨64, sp⟩, 2174 => ⟨64, w17 p yy zz sp⟩, 2183 => ⟨64, w18 p yy zz sp⟩, 2194 => ⟨64, w19 p
      yy zz sp⟩, 2203 => ⟨64, w964 p yy zz sp⟩, 2214 => ⟨64, w9 p yy zz sp⟩, 2247 => ⟨64, w983 p yy zz sp⟩,
      2252 => ⟨64, w988 p yy zz sp⟩, 2254 => ⟨64, w989 p yy zz sp⟩, 2255 => Value.ofBool (addSpec (w984 p yy
      zz sp) (w985 p yy zz sp)).2.CF] slots 35
    normalize [w1, w21, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334,
      w336, w364, w373, w607, w615, w666, w847, w848, w849, w850, w851, w852, w853, w854, w856, w857, w861,
      w862, w863, w865, w866, w867, w868, w869, w870, w871, w872, w873, w874, w875, w876, w878, w879, w880,
      w881, w882, w883, w884, w885, w886, w887, w888, w889, w890, w891, w892, w893, w894, w895, w896, w897,
      w898, w899, w900, w901, w902, w903, w904, w905, w906, w907, w908, w909, w910, w911, w912, w913, w914,
      w916, w917, w918, w921, w922, w924, w925, w926, w928, w929, w930, w931, w932, w933, w934, w935, w936,
      w937, w938, w939, w940, w941, w942, w943, w944, w945, w946, w947, w948, w959, w961, w963, w966, w968,
      w969, w973, w977, w982, w984, w985, w990, w991, w992, w993, w994, w995, w996, w997, w998, w999, w1000,
      w1001, w1002, w1003, w1004, w1005, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment53 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_53 b_l11d880_54 := by
  replay_segment using code_l11d880_53 from 2301 to 2348
    registers [4 => ⟨64, sp⟩, 2218 => ⟨64, w21 p yy zz sp⟩, 2238 => ⟨64, w981 p yy zz sp⟩, 2272 => ⟨64, w998
      p yy zz sp⟩, 2279 => ⟨64, w999 p yy zz sp⟩, 2281 => ⟨64, w1000 p yy zz sp⟩, 2288 => ⟨64, w1002 p yy zz
      sp⟩, 2290 => ⟨64, w1001 p yy zz sp⟩, 2297 => ⟨64, w1004 p yy zz sp⟩, 2299 => ⟨64, w1005 p yy zz sp⟩]
      slots 32
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1006, w1007, w1008, w1009, w1010, w1011, w1012, w1013, w1014, w1015,
      w1016, w1017, w1018, w1019, w1020, w1021, w1022, w1023, w1024, w1025, w1026, w1027, w1028, w1029,
      w1030, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment54 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_54 b_l11d880_55 := by
  replay_segment using code_l11d880_54 from 2348 to 2387
    registers [4 => ⟨64, sp⟩, 2292 => ⟨64, w1003 p yy zz sp⟩, 2315 => ⟨64, w1012 p yy zz sp⟩, 2318 => ⟨64,
      w1015 p yy zz sp⟩, 2343 => ⟨64, w1027 p yy zz sp⟩, 2346 => ⟨64, w1030 p yy zz sp⟩] slots 30
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1031, w1032, w1033, w1034, w1035, w1036, w1037, w1038, w1039, w1040,
      w1041, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment55 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_55 b_l11d880_56 := by
  replay_segment using code_l11d880_55 from 2387 to 2425
    registers [4 => ⟨64, sp⟩, 2262 => ⟨64, w993 p yy zz sp⟩, 2351 => ⟨64, w1031 p yy zz sp⟩, 2367 => ⟨64,
      w1036 p yy zz sp⟩, 2374 => ⟨64, w1037 p yy zz sp⟩, 2384 => ⟨64, w1040 p yy zz sp⟩, 2385 =>
      Value.ofBool (addSpec (w1038 p yy zz sp) (w1039 p yy zz sp)).2.CF] slots 29
    normalize [w1, w7, w8, w9, w10, w11, w17, w18, w19, w20, w21, w27, w28, w59, w80, w121, w128, w133,
      w157, w160, w257, w284, w312, w322, w334, w336, w364, w373, w607, w615, w666, w847, w848, w849, w850,
      w851, w852, w853, w854, w856, w857, w861, w862, w863, w865, w866, w867, w868, w869, w870, w871, w872,
      w873, w874, w875, w876, w877, w878, w879, w880, w881, w882, w883, w884, w885, w886, w887, w888, w889,
      w890, w891, w892, w893, w894, w895, w896, w897, w898, w899, w900, w901, w902, w903, w904, w905, w906,
      w907, w908, w909, w910, w911, w912, w913, w914, w916, w917, w918, w921, w922, w924, w925, w926, w928,
      w929, w930, w931, w932, w933, w934, w935, w936, w937, w938, w939, w940, w941, w942, w943, w944, w945,
      w946, w947, w948, w962, w963, w965, w966, w967, w968, w969, w970, w971, w972, w973, w974, w975, w976,
      w977, w978, w979, w980, w981, w1004, w1005, w1006, w1007, w1008, w1009, w1010, w1011, w1012, w1013,
      w1014, w1015, w1035, w1038, w1039, w1041, w1042, w1043, w1044, w1045, w1046, w1047, w1048, w1049,
      w1050, w1052, w1053, w1054, w1055, w1266, w1270]

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
