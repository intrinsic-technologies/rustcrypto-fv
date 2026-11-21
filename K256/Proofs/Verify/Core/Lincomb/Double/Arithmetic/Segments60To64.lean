import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment60 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_60 b_l110d64_61 := by
  replay_segment using code_l110d64_60 from 2588 to 2634
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2446 => ⟨64, w16 p yy zz sp⟩, 2498 => ⟨64, w14 p yy zz sp⟩, 2573 => ⟨64, w1140
      p yy zz sp⟩, 2586 => ⟨64, w1053 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1134, w1135, w1136, w1137, w1138, w1139, w1141, w1142, w1143, w1145, w1146, w1147, w1148,
      w1149, w1150, w1151, w1152, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment61 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_61 b_l110d64_62 := by
  replay_segment using code_l110d64_61 from 2634 to 2677
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2569 => ⟨64, w1144 p yy zz sp⟩, 2575 => ⟨64, w1052 p yy zz sp⟩, 2595 => ⟨64,
      w1141 p yy zz sp⟩, 2619 => ⟨64, w13 p yy zz sp⟩, 2621 => ⟨64, w1143 p yy zz sp⟩, 2622 => ⟨64, w1142 p
      yy zz sp⟩, 2629 => ⟨64, w1149 p yy zz sp⟩, 2632 => ⟨64, w1152 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1153, w1154, w1155, w1156, w1157, w1158, w1159, w1160, w1161, w1162, w1163, w1164, w1165,
      w1166, w1167, w1168, w1169, w1170, w1171, w1172, w1177, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment62 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_62 b_l110d64_63 := by
  replay_segment using code_l110d64_62 from 2677 to 2723
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2584 => ⟨64, w1053 p yy zz sp⟩, 2597 => ⟨64, w1054 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1173, w1174, w1175, w1176, w1178, w1179, w1180, w1181, w1182, w1183, w1184, w1185, w1186,
      w1187, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment63 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_63 b_l110d64_64 := by
  replay_segment using code_l110d64_63 from 2723 to 2767
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2644 => ⟨64, w1161 p yy zz sp⟩, 2668 => ⟨64, w1177 p yy zz sp⟩, 2682 => ⟨64,
      w1173 p yy zz sp⟩, 2684 => ⟨64, w1174 p yy zz sp⟩, 2710 => ⟨64, w14 p yy zz sp⟩, 2713 => ⟨64, w1180 p
      yy zz sp⟩, 2718 => ⟨64, w1185 p yy zz sp⟩, 2720 => ⟨64, w1186 p yy zz sp⟩, 2721 => Value.ofBool
      (addSpec (w1181 p yy zz sp) (w1182 p yy zz sp)).2.CF]
    normalize [w1, w7, w8, w9, w10, w11, w17, w18, w19, w20, w21, w28, w59, w80, w121, w128, w133, w157,
      w160, w257, w284, w322, w334, w336, w364, w373, w615, w666, w847, w848, w849, w850, w851, w852, w853,
      w854, w856, w857, w861, w862, w863, w865, w866, w867, w868, w869, w870, w871, w872, w873, w874, w875,
      w876, w877, w878, w879, w880, w881, w882, w883, w884, w885, w886, w887, w888, w889, w890, w891, w892,
      w893, w894, w895, w896, w897, w898, w899, w900, w901, w902, w903, w904, w905, w906, w907, w908, w909,
      w910, w911, w912, w913, w914, w915, w916, w917, w918, w919, w920, w921, w922, w923, w924, w925, w926,
      w927, w928, w929, w930, w931, w932, w933, w934, w935, w936, w937, w938, w939, w940, w941, w942, w943,
      w944, w945, w946, w947, w948, w949, w950, w951, w952, w953, w954, w955, w956, w957, w958, w959, w960,
      w961, w962, w963, w964, w965, w966, w967, w968, w969, w970, w971, w972, w973, w974, w975, w976, w977,
      w978, w979, w980, w981, w982, w983, w984, w985, w986, w987, w988, w989, w990, w991, w992, w993, w994,
      w995, w996, w997, w998, w999, w1000, w1001, w1002, w1003, w1004, w1005, w1006, w1007, w1008, w1009,
      w1010, w1011, w1012, w1013, w1014, w1015, w1016, w1017, w1018, w1019, w1020, w1021, w1022, w1023,
      w1024, w1025, w1026, w1027, w1028, w1029, w1030, w1031, w1032, w1033, w1034, w1035, w1036, w1037,
      w1038, w1039, w1040, w1041, w1042, w1043, w1044, w1045, w1046, w1047, w1048, w1049, w1050, w1055,
      w1176, w1179, w1181, w1182, w1187, w1188, w1189, w1190, w1191, w1192, w1193, w1194, w1195, w1196,
      w1197, w1198, w1199, w1200, w1201, w1202, w1203, w1204, w1205, w1206, w1207, w1208, w1209, w1210,
      w1211, w1216, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment64 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_64 b_l110d64_65 := by
  replay_segment using code_l110d64_64 from 2767 to 2813
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2695 => ⟨64, w1055 p yy zz sp⟩, 2706 => ⟨64, w1050 p yy zz sp⟩, 2730 => ⟨64,
      w1194 p yy zz sp⟩, 2765 => ⟨64, w1053 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1212, w1213, w1214, w1215, w1217, w1218, w1219, w1220, w1221, w1222, w1223, w1224, w1225,
      w1226, w1227, w1228, v1580]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
