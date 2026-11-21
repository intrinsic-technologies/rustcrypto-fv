import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment55 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_55 b_l110d64_56 := by
  replay_segment using code_l110d64_55 from 2380 to 2419
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2343 => ⟨64, w1044 p yy zz sp⟩, 2365 => ⟨64, w1052 p yy zz sp⟩, 2369 => ⟨64,
      w1053 p yy zz sp⟩, 2371 => ⟨64, w1054 p yy zz sp⟩, 2373 => ⟨64, w59 p yy zz sp⟩, 2375 => ⟨64, w15 p yy
      zz sp⟩, 2378 => ⟨64, w1052 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1055, w1057, w1058, w1060, w1061, w1062, w1063, w1064, w1065, w1067, w1068, v1580,
      BitVec.mul_one]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment56 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_56 b_l110d64_57 := by
  replay_segment using code_l110d64_56 from 2419 to 2460
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2361 => ⟨64, w1050 p yy zz sp⟩, 2388 => ⟨64, w1055 p yy zz sp⟩, 2405 => ⟨64,
      w1062 p yy zz sp⟩, 2408 => ⟨64, w1065 p yy zz sp⟩, 2415 => ⟨64, w1068 p yy zz sp⟩, 2416 => ⟨64, w1067
      p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1069, w1070, w1071, w1072, w1074, w1075, w1076, w1077, w1078, w1079, w1081, w1082, v1580,
      BitVec.mul_one]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment57 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_57 b_l110d64_58 := by
  replay_segment using code_l110d64_57 from 2460 to 2500
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2365 => ⟨64, w1052 p yy zz sp⟩, 2369 => ⟨64, w1053 p yy zz sp⟩, 2371 => ⟨64,
      w1054 p yy zz sp⟩, 2390 => ⟨64, w59 p yy zz sp⟩, 2441 => ⟨64, w1076 p yy zz sp⟩, 2444 => ⟨64, w1079 p
      yy zz sp⟩, 2446 => ⟨64, w16 p yy zz sp⟩, 2453 => ⟨64, w1082 p yy zz sp⟩, 2458 => ⟨64, w1081 p yy zz
      sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1083, w1084, w1085, w1086, w1087, w1088, w1089, w1090, w1091, w1092, w1093, w1094, w1101,
      v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment58 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_58 b_l110d64_59 := by
  replay_segment using code_l110d64_58 from 2500 to 2544
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2388 => ⟨64, w1055 p yy zz sp⟩, 2410 => ⟨64, w13 p yy zz sp⟩, 2448 => ⟨64,
      w1050 p yy zz sp⟩, 2456 => ⟨64, w1081 p yy zz sp⟩, 2460 => ⟨64, w1083 p yy zz sp⟩, 2492 => ⟨64, w1093
      p yy zz sp⟩, 2494 => ⟨64, w1094 p yy zz sp⟩, 2496 => ⟨64, w1054 p yy zz sp⟩, 2498 => ⟨64, w14 p yy zz
      sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1095, w1096, w1097, w1098, w1099, w1100, w1102, w1103, w1104, w1105, w1106, w1108, w1109,
      w1110, w1111, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment59 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_59 b_l110d64_60 := by
  replay_segment using code_l110d64_59 from 2544 to 2588
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2477 => ⟨64, w1101 p yy zz sp⟩, 2504 => ⟨64, w1096 p yy zz sp⟩, 2511 => ⟨64,
      w1097 p yy zz sp⟩, 2513 => ⟨64, w1098 p yy zz sp⟩, 2517 => ⟨64, w12 p yy zz sp⟩, 2522 => ⟨64, w1100 p
      yy zz sp⟩, 2524 => ⟨64, w1099 p yy zz sp⟩, 2534 => ⟨64, w1105 p yy zz sp⟩, 2537 => ⟨64, w1106 p yy zz
      sp⟩, 2539 => ⟨64, w1108 p yy zz sp⟩, 2542 => ⟨64, w1111 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1112, w1113, w1114, w1115, w1116, w1117, w1118, w1119, w1120, w1121, w1122, w1123, w1124,
      w1125, w1126, w1127, w1128, w1129, w1130, w1131, w1132, w1133, w1140, w1144, v1580]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
