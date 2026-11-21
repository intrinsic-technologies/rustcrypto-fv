import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Tactic.Replay Common.Point Common.Field
  Common.Point.DoubleWords.Replay Sec1.Affine.Uncompressed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment65 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_65 b_l110d64_66 := by
  replay_segment using code_l110d64_65 from 2813 to 2861
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2756 => ⟨64, w1216 p yy zz sp⟩, 2770 => ⟨64, w1212 p yy zz sp⟩, 2772 => ⟨64,
      w1213 p yy zz sp⟩, 2779 => ⟨64, w1214 p yy zz sp⟩, 2781 => ⟨64, w1215 p yy zz sp⟩, 2804 => ⟨64, w1225
      p yy zz sp⟩, 2807 => ⟨64, w1228 p yy zz sp⟩, 2809 => ⟨64, w1225 p yy zz sp⟩, 2811 => ⟨64, w59 p yy zz
      sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1229, w1230, w1231, w1232, w1233, w1234, w1235, w1236, w1237, w1238, w1239, w1240, w1241,
      w1242, w1243, w1244, w1245, w1246, w1247, w1248, w1249, w1250, w1251, w1252, w1253, w1254, w1255,
      w1256, w1257, w1258, v1580]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment66 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_66 b_l110d64_67 := by
  replay_segment using code_l110d64_66 from 2861 to 2901
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2564 => ⟨64, w1128 p yy zz sp⟩, 2663 => ⟨64, w1167 p yy zz sp⟩, 2751 => ⟨64,
      w1206 p yy zz sp⟩, 2811 => ⟨64, w59 p yy zz sp⟩, 2835 => ⟨64, w1244 p yy zz sp⟩, 2856 => ⟨64, w1256 p
      yy zz sp⟩, 2858 => ⟨64, w1257 p yy zz sp⟩, 2859 => Value.ofBool (addSpec (w1253 p yy zz sp) (w1251 p
      yy zz sp)).2.CF]
    normalize [w1, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w28, w59, w80,
      w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373, w615, w666, w847, w848, w849,
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
      w1049, w1050, w1052, w1053, w1054, w1055, w1057, w1058, w1060, w1061, w1062, w1063, w1064, w1065,
      w1067, w1068, w1069, w1070, w1071, w1072, w1074, w1075, w1076, w1077, w1078, w1079, w1081, w1082,
      w1083, w1084, w1085, w1086, w1087, w1088, w1089, w1090, w1091, w1092, w1093, w1094, w1095, w1096,
      w1097, w1098, w1099, w1100, w1101, w1102, w1103, w1104, w1105, w1106, w1108, w1109, w1110, w1111,
      w1112, w1113, w1114, w1115, w1116, w1117, w1118, w1119, w1120, w1121, w1122, w1123, w1124, w1125,
      w1126, w1127, w1129, w1130, w1131, w1132, w1133, w1134, w1135, w1136, w1137, w1138, w1139, w1140,
      w1141, w1142, w1143, w1144, w1145, w1146, w1147, w1148, w1149, w1150, w1151, w1152, w1153, w1154,
      w1155, w1156, w1157, w1158, w1159, w1160, w1161, w1162, w1163, w1164, w1165, w1166, w1168, w1169,
      w1170, w1171, w1172, w1173, w1174, w1175, w1176, w1177, w1178, w1179, w1180, w1181, w1182, w1183,
      w1184, w1185, w1186, w1187, w1188, w1189, w1190, w1191, w1192, w1193, w1194, w1195, w1196, w1197,
      w1198, w1199, w1200, w1201, w1202, w1203, w1204, w1205, w1207, w1208, w1209, w1210, w1211, w1212,
      w1213, w1214, w1215, w1216, w1217, w1218, w1219, w1220, w1221, w1222, w1223, w1224, w1225, w1226,
      w1227, w1228, w1229, w1230, w1231, w1232, w1233, w1234, w1235, w1236, w1237, w1238, w1239, w1240,
      w1241, w1242, w1243, w1245, w1246, w1247, w1248, w1250, w1251, w1252, w1253, w1258, w1259, w1260,
      w1261, w1262, w1263, w1268, w1269, w1270, w1271, w1272, v1580, v1789, v1790, v1791, v1792, v1793,
      v1794, v1795, v1796, v1797]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment67 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_67 b_l110d64_68 := by
  replay_segment using code_l110d64_67 from 2901 to 2936
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2811 => ⟨64, w59 p yy zz sp⟩, 2858 => ⟨64, w1257 p yy zz sp⟩, 2873 => ⟨64,
      v1789 p yy zz sp⟩, 2889 => ⟨64, v1792 p yy zz sp⟩, 2895 => ⟨64, v1797 p yy zz sp⟩, 2897 => ⟨64, v1796
      p yy zz sp⟩, 2899 => ⟨64, v1796 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, v1580, v1798, v1799, v1800, v1801, v1802, v1803, v1804, v1805, v1806, v1808, v1809, v1810,
      v1811]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment68 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_68 b_l110d64_69 := by
  replay_segment using code_l110d64_68 from 2936 to 2981
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2934 => ⟨64, v1556 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, w1306, w1307, v1580, v1812, v1813, v1814, v1815, v1816, v1817, v1818, v1819, v1820, v1821,
      v1822, v1823]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem segment69 {a : Registers} {p : PointWords} {yy zz : Limbs} {sp : Word}
    (rsp : a[4] = ⟨64, sp⟩) :
    Segment a p yy zz sp b_l110d64_69 b_l110d64_70 := by
  replay_segment using code_l110d64_69 from 2981 to 3025
    atoms (memoryAtoms p yy zz sp) unfold memoryAtoms framed_by writes
    registers [4 => ⟨64, sp⟩, 2974 => ⟨64, v1820 p yy zz sp⟩, 2977 => ⟨64, v1823 p yy zz sp⟩, 2979 => ⟨64,
      v1564 p yy zz sp⟩]
    normalize [w1, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w322, w334, w336, w364, w373,
      w615, w666, v1580, v1824, v1825, v1826, v1827, v1828, v1829, v1830, v1831, v1832, v1833, v1834, v1835,
      v1836, v1837]

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
