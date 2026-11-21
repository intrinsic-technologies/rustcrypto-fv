import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Sec1.Affine.Uncompressed
open Common.Point Common.Field Common.Point.DoubleWords.Replay

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment70 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_70 b_l11d880_71 := by
  replay_segment using code_l11d880_70 from 3022 to 3067
    registers [4 => ⟨64, sp⟩, 3007 => ⟨64, w1299 p yy zz sp⟩, 3009 => ⟨64, w1298 p yy zz sp⟩, 3018 => ⟨64,
      w1300 p yy zz sp⟩, 3020 => ⟨64, w1301 p yy zz sp⟩] slots 26
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1266, w1270, w1302, w1303, w1304, w1305, w1306, w1307, w1308, w1309,
      w1310, w1311, w1312, w1313, w1314, w1315, w1316, w1317]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment71 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_71 b_l11d880_72 := by
  replay_segment using code_l11d880_71 from 3067 to 3110
    registers [4 => ⟨64, sp⟩, 3000 => ⟨64, w326 p yy zz sp⟩, 3011 => ⟨64, w339 p yy zz sp⟩, 3058 => ⟨64,
      w1314 p yy zz sp⟩, 3061 => ⟨64, w1317 p yy zz sp⟩, 3065 => ⟨64, w368 p yy zz sp⟩] slots 25
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1266, w1270, w1318, w1319, w1320, w1321, w1322, w1323, w1324, w1325,
      w1326, w1327, w1328, w1329, w1330, w1331]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment72 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_72 b_l11d880_73 := by
  replay_segment using code_l11d880_72 from 3110 to 3155
    registers [4 => ⟨64, sp⟩, 3027 => ⟨64, w349 p yy zz sp⟩, 3031 => ⟨64, w400 p yy zz sp⟩, 3045 => ⟨64,
      w363 p yy zz sp⟩, 3049 => ⟨64, w398 p yy zz sp⟩, 3063 => ⟨64, w368 p yy zz sp⟩, 3074 => ⟨64, w1320 p
      yy zz sp⟩, 3090 => ⟨64, w1324 p yy zz sp⟩, 3093 => ⟨64, w1327 p yy zz sp⟩, 3101 => ⟨64, w1329 p yy zz
      sp⟩, 3105 => ⟨64, w1331 p yy zz sp⟩, 3108 => ⟨64, w1330 p yy zz sp⟩] slots 27
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1266, w1270, w1332, w1333, w1334, w1335, w1336, w1337, w1338, w1339,
      w1340, w1341, w1342, w1343, w1344]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment73 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_73 b_l11d880_74 := by
  replay_segment using code_l11d880_73 from 3155 to 3199
    registers [4 => ⟨64, sp⟩, 3117 => ⟨64, w1333 p yy zz sp⟩, 3119 => ⟨64, w1332 p yy zz sp⟩, 3121 => ⟨64,
      w1334 p yy zz sp⟩, 3128 => ⟨64, w1336 p yy zz sp⟩, 3130 => ⟨64, w1335 p yy zz sp⟩, 3137 => ⟨64, w398 p
      yy zz sp⟩, 3139 => ⟨64, w1337 p yy zz sp⟩, 3141 => ⟨64, w1338 p yy zz sp⟩, 3147 => ⟨64, w1340 p yy zz
      sp⟩, 3148 => ⟨64, w1339 p yy zz sp⟩, 3150 => ⟨64, w1341 p yy zz sp⟩, 3153 => ⟨64, w1344 p yy zz sp⟩]
      slots 26
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1266, w1270, w1345, w1346, w1347, w1348, w1349, w1350, w1351, w1352,
      w1353, w1354, w1355, w1356, w1357, w1358, w1359, w1360, w1361, w1362, w1363, w1364, w1365, w1366,
      w1367, w1368]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment74 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_74 b_l11d880_75 := by
  replay_segment using code_l11d880_74 from 3199 to 3244
    registers [4 => ⟨64, sp⟩, 3175 => ⟨64, w1361 p yy zz sp⟩, 3178 => ⟨64, w1364 p yy zz sp⟩, 3196 => ⟨64,
      w1368 p yy zz sp⟩, 3197 => ⟨64, w1367 p yy zz sp⟩] slots 29
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1266, w1270, w1369, w1370, w1371, w1372, w1373, w1374, w1375, w1376,
      w1377, w1378, w1379, w1380, w1381, w1382, w1383]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment75 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_75 b_l11d880_76 := by
  replay_segment using code_l11d880_75 from 3244 to 3287
    registers [4 => ⟨64, sp⟩, 3180 => ⟨64, w326 p yy zz sp⟩, 3219 => ⟨64, w1371 p yy zz sp⟩, 3225 => ⟨64,
      w1374 p yy zz sp⟩, 3229 => ⟨64, w400 p yy zz sp⟩, 3231 => ⟨64, w1376 p yy zz sp⟩, 3232 => ⟨64, w1375 p
      yy zz sp⟩, 3234 => ⟨64, w1377 p yy zz sp⟩, 3239 => ⟨64, w1381 p yy zz sp⟩, 3241 => ⟨64, w1382 p yy zz
      sp⟩, 3242 => Value.ofBool (addSpec (w1378 p yy zz sp) (w1372 p yy zz sp)).2.CF] slots 29
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1266, w1270, w1368, w1370, w1372, w1378, w1383, w1384, w1385, w1386,
      w1387, w1388, w1389, w1390, w1391, w1392, w1393, w1394, w1395, w1396, w1397, w1398, w1399, w1400,
      w1401, w1402, w1403, w1404, w1405]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment76 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_76 b_l11d880_77 := by
  replay_segment using code_l11d880_76 from 3287 to 3332
    registers [4 => ⟨64, sp⟩, 3187 => ⟨64, w398 p yy zz sp⟩, 3192 => ⟨64, w339 p yy zz sp⟩, 3275 => ⟨64,
      w1400 p yy zz sp⟩, 3278 => ⟨64, w1403 p yy zz sp⟩] slots 29
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1266, w1270, w1406, w1407, w1408, w1409, w1410, w1411, w1412, w1413,
      w1414, w1415, w1416, w1417]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment77 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_77 b_l11d880_78 := by
  replay_segment using code_l11d880_77 from 3332 to 3378
    registers [4 => ⟨64, sp⟩, 3256 => ⟨64, w1394 p yy zz sp⟩, 3292 => ⟨64, w1406 p yy zz sp⟩, 3294 => ⟨64,
      w1407 p yy zz sp⟩, 3305 => ⟨64, w1408 p yy zz sp⟩, 3307 => ⟨64, w1410 p yy zz sp⟩, 3320 => ⟨64, w1412
      p yy zz sp⟩, 3324 => ⟨64, w407 p yy zz sp⟩, 3326 => ⟨64, w1415 p yy zz sp⟩, 3327 => ⟨64, w1414 p yy zz
      sp⟩, 3329 => ⟨64, w1416 p yy zz sp⟩, 3330 => Value.ofBool (addSpec (w1413 p yy zz sp) (w1409 p yy zz
      sp)).2.CF] slots 27
    normalize [w1, w19, w22, w23, w24, w25, w26, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257,
      w264, w265, w266, w267, w270, w271, w272, w273, w274, w275, w276, w280, w281, w282, w283, w284, w285,
      w286, w290, w291, w292, w293, w294, w295, w298, w299, w300, w301, w303, w304, w306, w307, w308, w310,
      w312, w313, w314, w315, w316, w317, w318, w319, w322, w327, w328, w329, w330, w331, w334, w336, w337,
      w340, w341, w342, w343, w344, w346, w348, w349, w364, w373, w607, w615, w666, w1266, w1270, w1409,
      w1413, w1417, w1418, w1419, w1420, w1421, w1422, w1423, w1424, w1425, w1426, w1427, w1428, w1429,
      w1430, w1431, w1432, w1433, w1434, w1435, w1436, w1437, w1438, w1439, w1440, w1441, w1442, w1443,
      w1444, w1445]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment78 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_78 b_l11d880_79 := by
  replay_segment using code_l11d880_78 from 3378 to 3422
    registers [4 => ⟨64, sp⟩, 3296 => ⟨64, w349 p yy zz sp⟩, 3365 => ⟨64, w1440 p yy zz sp⟩, 3368 => ⟨64,
      w1443 p yy zz sp⟩] slots 25
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1266, w1270, w1446, w1447, w1448, w1449, w1450, w1451, w1452, w1453,
      w1454, w1455, w1456, w1457]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment79 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_79 b_l11d880_80 := by
  replay_segment using code_l11d880_79 from 3422 to 3464
    registers [4 => ⟨64, sp⟩, 3344 => ⟨64, w1428 p yy zz sp⟩, 3375 => ⟨64, w1444 p yy zz sp⟩, 3383 => ⟨64,
      w1446 p yy zz sp⟩, 3385 => ⟨64, w1447 p yy zz sp⟩, 3392 => ⟨64, w1449 p yy zz sp⟩, 3408 => ⟨64, w1452
      p yy zz sp⟩, 3413 => ⟨64, w1454 p yy zz sp⟩, 3417 => ⟨64, w1456 p yy zz sp⟩, 3418 => Value.ofBool
      (addSpec (w1455 p yy zz sp) (w1453 p yy zz sp)).2.CF, 3420 => ⟨64, w1 p yy zz sp⟩] slots 19
    normalize [w1, w20, w21, w22, w23, w24, w25, w26, w27, w28, w59, w80, w121, w128, w133, w157, w160,
      w257, w262, w264, w265, w266, w267, w270, w271, w272, w273, w274, w275, w276, w280, w281, w282, w283,
      w284, w285, w286, w290, w291, w292, w293, w294, w295, w298, w299, w300, w301, w303, w304, w306, w307,
      w308, w310, w312, w313, w314, w315, w316, w317, w318, w319, w322, w327, w328, w329, w330, w331, w334,
      w336, w337, w340, w341, w342, w343, w344, w350, w351, w352, w353, w354, w356, w357, w358, w360, w362,
      w363, w364, w366, w368, w373, w411, w415, w607, w615, w666, w1266, w1270, w1453, w1455, w1457, w1458,
      w1459, w1460, w1461, w1462, w1463, w1464, w1465, w1466, w1467, w1468, w1469, w1470, w1471, w1472,
      w1474, w1475, w1476, w1477, w1478, w1479]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment80 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_80 b_l11d880_81 := by
  replay_segment using code_l11d880_80 from 3464 to 3506
    registers [4 => ⟨64, sp⟩, 3395 => ⟨64, w1450 p yy zz sp⟩, 3420 => ⟨64, w1 p yy zz sp⟩, 3424 => ⟨64,
      w1460 p yy zz sp⟩, 3427 => ⟨64, w1463 p yy zz sp⟩, 3456 => ⟨64, w1476 p yy zz sp⟩, 3459 => ⟨64, w1479
      p yy zz sp⟩] slots 17
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1266, w1270, w1480, w1481, w1482, w1483, w1484, w1485, w1486, w1487,
      w1488, w1489, w1490, w1491, w1492, w1493, w1494, w1495, w1496, w1497, w1498]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment81 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_81 b_l11d880_82 := by
  replay_segment using code_l11d880_81 from 3506 to 3546
    registers [4 => ⟨64, sp⟩, 3175 => ⟨64, w1361 p yy zz sp⟩, 3311 => ⟨64, w1411 p yy zz sp⟩, 3399 => ⟨64,
      w1451 p yy zz sp⟩, 3483 => ⟨64, w1488 p yy zz sp⟩, 3502 => ⟨64, w1498 p yy zz sp⟩, 3504 => ⟨64, w257 p
      yy zz sp⟩] slots 16
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1266, w1270, w1499, w1500, w1502, w1503, w1504, w1505, w1506, w1507,
      w1508, w1509, w1510, w1511, w1512, w1513, w1514, w1515, w1516]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem segment82 {a : Values Value Reg.count} {p : PointWords} {yy zz : Limbs}
    {sp : Word} {count : BitVec 32} (rsp : a[4] = ⟨64, sp⟩)
    (_rbp : a[5] = ⟨64, 0x1000003d10⟩) :
    Segment a p yy zz sp count b_l11d880_82 b_l11d880_83 := by
  replay_segment using code_l11d880_82 from 3546 to 3583
    registers [4 => ⟨64, sp⟩, 3474 => ⟨64, w59 p yy zz sp⟩, 3494 => ⟨64, w1494 p yy zz sp⟩, 3504 => ⟨64,
      w257 p yy zz sp⟩, 3520 => ⟨64, w1507 p yy zz sp⟩, 3526 => ⟨64, w1510 p yy zz sp⟩, 3532 => ⟨64, w1513 p
      yy zz sp⟩, 3542 => ⟨64, w1516 p yy zz sp⟩, 3544 => ⟨64, w1516 p yy zz sp⟩] slots 12
    normalize [w1, w27, w28, w59, w80, w121, w128, w133, w157, w160, w257, w284, w312, w322, w334, w336,
      w364, w373, w607, w615, w666, w1266, w1270, w1518, w1519, w1521, w1522, w1523, w1524, w1525, w1526,
      w1528, w1529, w1531, w1532, w1533, w1534]

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
