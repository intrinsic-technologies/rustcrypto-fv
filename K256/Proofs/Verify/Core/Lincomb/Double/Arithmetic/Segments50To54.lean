import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment50 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_50 b_l110d64_51 := by
  replay_segment using code_l110d64_50 from 2167 to 2213
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2103 => ⟨64, w948 p yy zz sp⟩, 2145 => ⟨64, w960 p yy zz sp⟩, 2147 => ⟨64,
      w961 p yy zz sp⟩, 2156 => ⟨64, w962 p yy zz sp⟩, 2158 => ⟨64, w963 p yy zz sp⟩, 2164 => ⟨64, w966 p yy
      zz sp⟩, 2165 => ⟨64, w965 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w967, w968, w969, w970, w971, w972, w973, w974, w975, w976, w977, w978, w979, w980, w981,
      w982, w983, w984, w985, w986, w987, w988, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment51 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_51 b_l110d64_52 := by
  replay_segment using code_l110d64_51 from 2213 to 2253
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2136 => ⟨64, w7 p yy zz sp⟩, 2140 => ⟨64, w18 p yy zz sp⟩, 2151 => ⟨64, w19 p
      yy zz sp⟩, 2171 => ⟨64, w9 p yy zz sp⟩, 2204 => ⟨64, w983 p yy zz sp⟩, 2206 => ⟨64, w984 p yy zz sp⟩,
      2208 => ⟨64, w985 p yy zz sp⟩, 2211 => ⟨64, w988 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w989, w990, w991, w992, w993, w994, w995, w996, w997, w998, w999, w1000, w1001, w1002,
      w1003, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment52 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_52 b_l110d64_53 := by
  replay_segment using code_l110d64_52 from 2253 to 2298
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2162 => ⟨64, w20 p yy zz sp⟩, 2175 => ⟨64, w21 p yy zz sp⟩, 2195 => ⟨64, w981
      p yy zz sp⟩, 2242 => ⟨64, w1000 p yy zz sp⟩, 2249 => ⟨64, w1002 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1004, w1005, w1006, w1007, w1008, w1009, w1010, w1011, w1012, w1013, w1014, w1015, w1016,
      w1017, w1018, w1019, w1020, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment53 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_53 b_l110d64_54 := by
  replay_segment using code_l110d64_53 from 2298 to 2342
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2227 => ⟨64, w1003 p yy zz sp⟩, 2251 => ⟨64, w1001 p yy zz sp⟩, 2277 => ⟨64,
      w1012 p yy zz sp⟩, 2280 => ⟨64, w1015 p yy zz sp⟩, 2284 => ⟨64, w59 p yy zz sp⟩, 2288 => ⟨64, w1 p yy
      zz sp⟩, 2291 => ⟨64, w1017 p yy zz sp⟩, 2293 => ⟨64, w1018 p yy zz sp⟩, 2295 => ⟨64, w1019 p yy zz
      sp⟩, 2296 => Value.ofBool (addSpec (w1002 p yy zz sp) (w1000 p yy zz sp)).2.CF]
    normalize [w1, w7, w8, w18, w19, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334,
      w336, w364, w373, w615, w666, w1000, w1002, w1020, w1021, w1022, w1023, w1024, w1025, w1026, w1027,
      w1028, w1029, w1030, w1031, w1032, w1033, w1034, w1035, w1036, w1037, w1038, w1039, w1040, w1041,
      w1042, w1043, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment54 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_54 b_l110d64_55 := by
  replay_segment using code_l110d64_54 from 2342 to 2380
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2310 => ⟨64, w1031 p yy zz sp⟩, 2320 => ⟨64, w1036 p yy zz sp⟩, 2329 => ⟨64,
      w59 p yy zz sp⟩, 2335 => ⟨64, w1040 p yy zz sp⟩, 2338 => ⟨64, w1043 p yy zz sp⟩, 2340 => ⟨64, v1788 p
      yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1044, w1045, w1046, w1047, w1048, w1049, w1050, w1052, w1053, w1054, v1580,
      BitVec.mul_one]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
