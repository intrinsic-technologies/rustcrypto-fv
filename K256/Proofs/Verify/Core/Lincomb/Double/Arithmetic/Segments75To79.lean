import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment75 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_75 b_l110d64_76 := by
  replay_segment using code_l110d64_75 from 3247 to 3294
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 3188 => ⟨64, v1902 p yy zz sp⟩, 3226 => ⟨64, v1915 p yy zz sp⟩, 3228 => ⟨64,
      v1916 p yy zz sp⟩, 3237 => ⟨64, w1409 p yy zz sp⟩, 3239 => ⟨64, w1408 p yy zz sp⟩, 3245 => ⟨64, v1564
      p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, v1580, v1918, v1919, v1920, v1921, v1922, v1923, v1924, v1925, v1926, v1927, v1928, v1929,
      v1930, v1931, v1932, v1933, v1934, v1935, v1936, v1937, v1938, v1939, v1940, v1941]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment76 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_76 b_l110d64_77 := by
  replay_segment using code_l110d64_76 from 3294 to 3336
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 3212 => ⟨64, v1912 p yy zz sp⟩, 3230 => ⟨64, w349 p yy zz sp⟩, 3258 => ⟨64,
      w407 p yy zz sp⟩, 3280 => ⟨64, w59 p yy zz sp⟩, 3286 => ⟨64, v1937 p yy zz sp⟩, 3287 => ⟨64, v1936 p
      yy zz sp⟩, 3289 => ⟨64, v1938 p yy zz sp⟩, 3292 => ⟨64, v1941 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1448, w1449, v1580, v1942, v1943, v1944, v1945, v1946, v1947, v1948, v1949, v1950, v1951,
      v1952, v1953, v1954, v1955]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment77 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_77 b_l110d64_78 := by
  replay_segment using code_l110d64_77 from 3336 to 3381
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 3245 => ⟨64, v1564 p yy zz sp⟩, 3278 => ⟨64, v1934 p yy zz sp⟩, 3280 => ⟨64,
      w59 p yy zz sp⟩, 3323 => ⟨64, v1954 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, v1580, v1956, v1957, v1958, v1959, v1960, v1961, v1962, v1963, v1964, v1965, v1966, v1967,
      v1968, v1969, v1970, v1971, v1972]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment78 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_78 b_l110d64_79 := by
  replay_segment using code_l110d64_78 from 3381 to 3424
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 3307 => ⟨64, v1950 p yy zz sp⟩, 3321 => ⟨64, v1953 p yy zz sp⟩, 3330 => ⟨64,
      w1449 p yy zz sp⟩, 3332 => ⟨64, w1448 p yy zz sp⟩, 3359 => ⟨64, v1964 p yy zz sp⟩, 3362 => ⟨64, v1967
      p yy zz sp⟩, 3368 => ⟨64, w59 p yy zz sp⟩, 3370 => ⟨64, w1 p yy zz sp⟩, 3372 => ⟨64, v1970 p yy zz
      sp⟩, 3373 => ⟨64, v1969 p yy zz sp⟩, 3378 => ⟨64, v1971 p yy zz sp⟩, 3379 => Value.ofBool (addSpec
      (v1954 p yy zz sp) (v1952 p yy zz sp)).2.CF]
    normalize [w1, w17, w18, w19, w22, w23, w24, w25, w26, w28, w59, w80, w121, w128, w133, w157, w160,
      w257, w264, w265, w266, w267, w270, w271, w272, w273, w274, w275, w276, w280, w281, w282, w283, w284,
      w285, w286, w290, w291, w292, w293, w294, w295, w298, w299, w300, w301, w303, w304, w306, w307, w308,
      w310, w312, w313, w314, w315, w316, w317, w318, w319, w321, w322, w327, w328, w329, w330, w331, w333,
      w334, w336, w340, w364, w373, w400, w407, w615, w666, v1555, v1556, v1558, v1559, v1560, v1580, v1952,
      v1954, v1972, v1973, v1974, v1975, v1976, v1977, v1978, v1979, v1980, v1981, v1982, v1983, v1984,
      v1985, v1986, v1987, v1988, v1989, v1990, v1991, v1992, v1993, v1994, v1995, v1996]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment79 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_79 b_l110d64_80 := by
  replay_segment using code_l110d64_79 from 3424 to 3464
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 3108 => ⟨64, v1871 p yy zz sp⟩, 3243 => ⟨64, v1917 p yy zz sp⟩, 3334 => ⟨64,
      v1955 p yy zz sp⟩, 3368 => ⟨64, w59 p yy zz sp⟩, 3403 => ⟨64, v1988 p yy zz sp⟩, 3413 => ⟨64, v1991 p
      yy zz sp⟩, 3419 => ⟨64, v1993 p yy zz sp⟩, 3422 => ⟨64, v1996 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, v1580, v1997, v1998, v1999, v2000, v2001, v2002, v2003, v2005, v2006, v2007, v2008, v2009,
      v2010, v2011, v2012, v2013, v2014, v2015, v2016]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
