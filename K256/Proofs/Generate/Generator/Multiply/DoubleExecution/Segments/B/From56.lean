import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Sec1.Affine.Uncompressed
open Common.Point Common.Field Common.Point.DoubleWords.Replay

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment56 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_56 b_l11d880_57 := by
  replay_segment using code_l11d880_56 from 2425 to 2465
    registers [4 => ⟨64, sp⟩, 2411 => ⟨64, w1052 p yy zz sp⟩, 2413 => ⟨64, w1053 p yy zz sp⟩, 2417 => ⟨64,
      w1054 p yy zz sp⟩, 2422 => ⟨64, w15 p yy zz sp⟩] slots 28
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1057, w1058, w1060, w1061, w1062, w1063, w1064, w1065, w1067, w1068,
      w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment57 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_57 b_l11d880_58 := by
  replay_segment using code_l11d880_57 from 2465 to 2505
    registers [4 => ⟨64, sp⟩, 2405 => ⟨64, w1050 p yy zz sp⟩, 2419 => ⟨64, w1055 p yy zz sp⟩, 2452 => ⟨64,
      w1062 p yy zz sp⟩, 2455 => ⟨64, w1065 p yy zz sp⟩, 2457 => ⟨64, w13 p yy zz sp⟩, 2462 => ⟨64, w1068 p
      yy zz sp⟩, 2463 => ⟨64, w1067 p yy zz sp⟩] slots 30
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1069, w1070, w1071, w1072, w1074, w1075, w1076, w1077, w1078, w1079,
      w1081, w1082, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment58 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_58 b_l11d880_59 := by
  replay_segment using code_l11d880_58 from 2505 to 2545
    registers [4 => ⟨64, sp⟩, 2411 => ⟨64, w1052 p yy zz sp⟩, 2417 => ⟨64, w1054 p yy zz sp⟩, 2439 => ⟨64,
      w1053 p yy zz sp⟩, 2487 => ⟨64, w1076 p yy zz sp⟩, 2490 => ⟨64, w1079 p yy zz sp⟩, 2492 => ⟨64, w16 p
      yy zz sp⟩, 2499 => ⟨64, w1082 p yy zz sp⟩, 2500 => ⟨64, w1081 p yy zz sp⟩] slots 32
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1083, w1084, w1085, w1086, w1087, w1088, w1089, w1090, w1091, w1092,
      w1093, w1094, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment59 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_59 b_l11d880_60 := by
  replay_segment using code_l11d880_59 from 2545 to 2588
    registers [4 => ⟨64, sp⟩, 2445 => ⟨64, w14 p yy zz sp⟩, 2457 => ⟨64, w13 p yy zz sp⟩, 2496 => ⟨64, w1050
      p yy zz sp⟩, 2503 => ⟨64, w1081 p yy zz sp⟩, 2507 => ⟨64, w1083 p yy zz sp⟩, 2523 => ⟨64, w1087 p yy
      zz sp⟩, 2526 => ⟨64, w1090 p yy zz sp⟩, 2543 => ⟨64, w1054 p yy zz sp⟩] slots 36
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1095, w1096, w1097, w1098, w1099, w1100, w1101, w1102, w1103, w1104,
      w1105, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment60 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_60 b_l11d880_61 := by
  replay_segment using code_l11d880_60 from 2588 to 2633
    registers [4 => ⟨64, sp⟩, 2541 => ⟨64, w1093 p yy zz sp⟩, 2549 => ⟨64, w1096 p yy zz sp⟩, 2558 => ⟨64,
      w1097 p yy zz sp⟩, 2560 => ⟨64, w1098 p yy zz sp⟩, 2564 => ⟨64, w12 p yy zz sp⟩, 2569 => ⟨64, w1100 p
      yy zz sp⟩, 2571 => ⟨64, w1099 p yy zz sp⟩, 2573 => ⟨64, w1101 p yy zz sp⟩, 2579 => ⟨64, w1103 p yy zz
      sp⟩, 2585 => ⟨64, w1105 p yy zz sp⟩, 2586 => ⟨64, w1104 p yy zz sp⟩] slots 37
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1106, w1108, w1109, w1110, w1111, w1112, w1113, w1114, w1115, w1116,
      w1117, w1118, w1119, w1120, w1121, w1122, w1123, w1124, w1125, w1126, w1127, w1128, w1129, w1130,
      w1131, w1132, w1133, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment61 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_61 b_l11d880_62 := by
  replay_segment using code_l11d880_61 from 2633 to 2676
    registers [4 => ⟨64, sp⟩, 2551 => ⟨64, w1055 p yy zz sp⟩, 2617 => ⟨64, w1128 p yy zz sp⟩, 2631 => ⟨64,
      w1053 p yy zz sp⟩] slots 35
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1134, w1135, w1136, w1137, w1138, w1139, w1140, w1141, w1142, w1143,
      w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment62 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_62 b_l11d880_63 := by
  replay_segment using code_l11d880_62 from 2676 to 2722
    registers [4 => ⟨64, sp⟩, 2617 => ⟨64, w1128 p yy zz sp⟩, 2620 => ⟨64, w1131 p yy zz sp⟩, 2638 => ⟨64,
      w1134 p yy zz sp⟩, 2640 => ⟨64, w1135 p yy zz sp⟩, 2647 => ⟨64, w1136 p yy zz sp⟩, 2649 => ⟨64, w1137
      p yy zz sp⟩, 2656 => ⟨64, w1139 p yy zz sp⟩, 2658 => ⟨64, w1138 p yy zz sp⟩, 2665 => ⟨64, w1141 p yy
      zz sp⟩, 2673 => ⟨64, w1143 p yy zz sp⟩, 2674 => ⟨64, w1142 p yy zz sp⟩] slots 36
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1144, w1145, w1146, w1147, w1148, w1149, w1150, w1151, w1152, w1153,
      w1154, w1155, w1156, w1157, w1158, w1159, w1160, w1161, w1162, w1163, w1164, w1165, w1166, w1167,
      w1168, w1169, w1170, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment63 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_63 b_l11d880_64 := by
  replay_segment using code_l11d880_63 from 2722 to 2764
    registers [4 => ⟨64, sp⟩, 2622 => ⟨64, w1052 p yy zz sp⟩, 2631 => ⟨64, w1053 p yy zz sp⟩, 2667 => ⟨64,
      w1050 p yy zz sp⟩, 2671 => ⟨64, w13 p yy zz sp⟩, 2717 => ⟨64, w1167 p yy zz sp⟩, 2720 => ⟨64, w1170 p
      yy zz sp⟩] slots 34
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1171, w1172, w1173, w1174, w1175, w1176, w1177, w1178, w1179, w1266,
      w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment64 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_64 b_l11d880_65 := by
  replay_segment using code_l11d880_64 from 2764 to 2812
    registers [4 => ⟨64, sp⟩, 2698 => ⟨64, w1161 p yy zz sp⟩, 2734 => ⟨64, w1173 p yy zz sp⟩, 2736 => ⟨64,
      w1174 p yy zz sp⟩, 2745 => ⟨64, w1176 p yy zz sp⟩, 2747 => ⟨64, w1175 p yy zz sp⟩, 2749 => ⟨64, w1177
      p yy zz sp⟩, 2758 => ⟨64, w1179 p yy zz sp⟩, 2760 => ⟨64, w1178 p yy zz sp⟩, 2762 => ⟨64, w1050 p yy
      zz sp⟩] slots 34
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1180, w1181, w1182, w1183, w1184, w1185, w1186, w1187, w1188, w1189,
      w1190, w1191, w1192, w1193, w1194, w1195, w1196, w1197, w1198, w1199, w1200, w1201, w1202, w1203,
      w1204, w1205, w1206, w1207, w1208, w1209, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment65 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_65 b_l11d880_66 := by
  replay_segment using code_l11d880_65 from 2812 to 2856
    registers [4 => ⟨64, sp⟩, 2738 => ⟨64, w1054 p yy zz sp⟩, 2751 => ⟨64, w1055 p yy zz sp⟩, 2764 => ⟨64,
      w14 p yy zz sp⟩, 2805 => ⟨64, w1206 p yy zz sp⟩, 2808 => ⟨64, w1209 p yy zz sp⟩, 2810 => ⟨64, w1052 p
      yy zz sp⟩] slots 30
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1210, w1211, w1212, w1213, w1214, w1215, w1216, w1217, w1218, w1219,
      w1220, w1221, w1222, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment66 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_66 b_l11d880_67 := by
  replay_segment using code_l11d880_66 from 2856 to 2903
    registers [4 => ⟨64, sp⟩, 2784 => ⟨64, w1194 p yy zz sp⟩, 2822 => ⟨64, w1212 p yy zz sp⟩, 2824 => ⟨64,
      w1213 p yy zz sp⟩, 2831 => ⟨64, w1215 p yy zz sp⟩, 2833 => ⟨64, w1214 p yy zz sp⟩, 2835 => ⟨64, w1216
      p yy zz sp⟩, 2844 => ⟨64, w1217 p yy zz sp⟩, 2849 => ⟨64, w1219 p yy zz sp⟩, 2853 => ⟨64, w1221 p yy
      zz sp⟩, 2854 => Value.ofBool (addSpec (w1220 p yy zz sp) (w1218 p yy zz sp)).2.CF] slots 26
    normalize [w1, w7, w8, w9, w10, w11, w15, w16, w17, w18, w19, w20, w21, w27, w28, w59, w80, w121, w128,
      w133, w157, w160, w257, w284, w312, w322, w334, w336, w364, w373, w607, w615, w666, w847, w848, w849,
      w850, w851, w852, w853, w854, w856, w857, w861, w862, w863, w865, w866, w867, w868, w869, w870, w871,
      w872, w873, w874, w875, w876, w877, w878, w879, w880, w881, w882, w883, w884, w885, w886, w887, w888,
      w889, w890, w891, w892, w893, w894, w895, w896, w897, w898, w899, w900, w901, w902, w903, w904, w905,
      w906, w907, w908, w909, w910, w911, w912, w913, w914, w915, w916, w917, w918, w919, w920, w921, w922,
      w923, w924, w925, w926, w927, w928, w929, w930, w931, w932, w933, w934, w935, w936, w937, w938, w939,
      w940, w941, w942, w943, w944, w945, w946, w947, w948, w949, w950, w951, w952, w953, w954, w955, w956,
      w957, w958, w959, w960, w961, w962, w963, w964, w965, w966, w967, w968, w969, w970, w971, w972, w973,
      w974, w975, w976, w977, w978, w979, w980, w981, w982, w983, w984, w985, w986, w987, w988, w989, w990,
      w991, w992, w993, w994, w995, w996, w997, w998, w999, w1000, w1001, w1002, w1003, w1004, w1005, w1006,
      w1007, w1008, w1009, w1010, w1011, w1012, w1013, w1014, w1015, w1016, w1017, w1018, w1019, w1020,
      w1021, w1022, w1023, w1024, w1025, w1026, w1027, w1028, w1029, w1030, w1031, w1032, w1033, w1034,
      w1035, w1036, w1037, w1038, w1039, w1040, w1041, w1042, w1043, w1044, w1045, w1046, w1047, w1048,
      w1049, w1050, w1055, w1218, w1220, w1222, w1223, w1224, w1225, w1226, w1227, w1228, w1229, w1230,
      w1231, w1232, w1233, w1234, w1235, w1236, w1237, w1238, w1239, w1240, w1241, w1242, w1243, w1244,
      w1245, w1246, w1247, w1248, w1249, w1250, w1251, w1266, w1270]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment67 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_67 b_l11d880_68 := by
  replay_segment using code_l11d880_67 from 2903 to 2945
    registers [4 => ⟨64, sp⟩, 2717 => ⟨64, w1167 p yy zz sp⟩, 2898 => ⟨64, w1250 p yy zz sp⟩, 2899 => ⟨64,
      w1249 p yy zz sp⟩, 2901 => ⟨64, w1251 p yy zz sp⟩] slots 24
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1252, w1253, w1254, w1255, w1256, w1257, w1258, w1259, w1260, w1261,
      w1262, w1263, w1265, w1266, w1267, w1268, w1269, w1270, w1271, w1272, w1273]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment68 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_68 b_l11d880_69 := by
  replay_segment using code_l11d880_68 from 2945 to 2985
    registers [4 => ⟨64, sp⟩, 2805 => ⟨64, w1206 p yy zz sp⟩, 2889 => ⟨64, w1244 p yy zz sp⟩, 2914 => ⟨64,
      w1257 p yy zz sp⟩, 2931 => ⟨64, w1266 p yy zz sp⟩, 2935 => ⟨64, w1269 p yy zz sp⟩, 2943 => ⟨64, w1273
      p yy zz sp⟩] slots 22
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1266, w1270, w1275, w1276, w1277, w1278, w1280, w1281, w1282, w1283,
      w1285, w1286, w1287, w1288, w1290, w1291, w1292]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment69 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_69 b_l11d880_70 := by
  replay_segment using code_l11d880_69 from 2985 to 3022
    registers [4 => ⟨64, sp⟩, 2943 => ⟨64, w1273 p yy zz sp⟩, 2961 => ⟨64, w1278 p yy zz sp⟩, 2965 => ⟨64,
      w1283 p yy zz sp⟩, 2975 => ⟨64, w1288 p yy zz sp⟩, 2983 => ⟨64, w1292 p yy zz sp⟩] slots 21
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1266, w1270, w1294, w1295, w1296, w1297, w1298, w1299, w1300, w1301]

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
