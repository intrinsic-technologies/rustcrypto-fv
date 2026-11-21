import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment45 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_45 b_l110d64_46 := by
  replay_segment using code_l110d64_45 from 1951 to 1992
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1857 => ⟨64, w9 p yy zz sp⟩, 1872 => ⟨64, w8 p yy zz sp⟩, 1876 => ⟨64, w19 p
      yy zz sp⟩, 1883 => ⟨64, w7 p yy zz sp⟩, 1887 => ⟨64, w20 p yy zz sp⟩, 1941 => ⟨64, w881 p yy zz sp⟩,
      1947 => ⟨64, w883 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w884, w885, w886, w887, w889, w890, w891, w892, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment46 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_46 b_l110d64_47 := by
  replay_segment using code_l110d64_46 from 1992 to 2038
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1883 => ⟨64, w7 p yy zz sp⟩, 1943 => ⟨64, w888 p yy zz sp⟩, 1966 => ⟨64, w886
      p yy zz sp⟩, 1968 => ⟨64, w887 p yy zz sp⟩, 1975 => ⟨64, w889 p yy zz sp⟩, 1977 => ⟨64, w890 p yy zz
      sp⟩, 1986 => ⟨64, w891 p yy zz sp⟩, 1988 => ⟨64, w892 p yy zz sp⟩, 1990 => ⟨64, w881 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w893, w894, w895, w896, w897, w898, w899, w900, w901, w902, w903, w904, w905, w906, w907,
      w908, w909, w910, w911, w912, w913, w914, w915, w916, w917, w918, w923, w926, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment47 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_47 b_l110d64_48 := by
  replay_segment using code_l110d64_47 from 2038 to 2080
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1954 => ⟨64, w18 p yy zz sp⟩, 2032 => ⟨64, w923 p yy zz sp⟩, 2034 => ⟨64, w7 p
      yy zz sp⟩, 2036 => ⟨64, w17 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w919, w920, w921, w922, w924, w925, w927, w928, w929, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment48 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_48 b_l110d64_49 := by
  replay_segment using code_l110d64_48 from 2080 to 2126
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 1981 => ⟨64, w21 p yy zz sp⟩, 2030 => ⟨64, w926 p yy zz sp⟩, 2050 => ⟨64, w921
      p yy zz sp⟩, 2052 => ⟨64, w922 p yy zz sp⟩, 2061 => ⟨64, w925 p yy zz sp⟩, 2063 => ⟨64, w924 p yy zz
      sp⟩, 2065 => ⟨64, w927 p yy zz sp⟩, 2072 => ⟨64, w928 p yy zz sp⟩, 2074 => ⟨64, w929 p yy zz sp⟩, 2078
      => ⟨64, w8 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w930, w931, w932, w933, w934, w935, w936, w937, w938, w939, w940, w941, w942, w943, w944,
      w945, w946, w947, w948, w949, w950, w951, w952, w953, w954, w955, w956, w957, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment49 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_49 b_l110d64_50 := by
  replay_segment using code_l110d64_49 from 2126 to 2167
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2036 => ⟨64, w17 p yy zz sp⟩, 2043 => ⟨64, w11 p yy zz sp⟩, 2054 => ⟨64, w10 p
      yy zz sp⟩, 2076 => ⟨64, w8 p yy zz sp⟩, 2118 => ⟨64, w954 p yy zz sp⟩, 2124 => ⟨64, w957 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w958, w959, w960, w961, w962, w963, w964, w965, w966, v1580]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
