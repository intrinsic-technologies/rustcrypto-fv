import K256.Proofs.Sec1.LIR.Labels
import K256.Proofs.Common.CFG.EvalAttr
import K256.Proofs.Common.Lift.Generated.Footprints.Part1
import K256.Proofs.Common.Lift.Generated.Footprints.Part2
import K256.Proofs.Common.Lift.Generated.Footprints.Part3
import K256.Proofs.Common.Lift.Generated.Footprints.Part4
import K256.Proofs.Common.Lift.Generated.Footprints.Part5
import K256.Proofs.Sec1.LIR.Generated.Footprints

namespace K256.Proofs.Sec1.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

def b_l11f8f6_31 : Block Op Label signature Reg.count 1397 :=
  .letOp (n := 1397) (.out 0x120253 (xorR64R64Effect 0x120253 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[1381, 1367]
    (.letOp (n := 1398) (.exec 0x120253 (fun s => s.RIP = 0x120253) (xorR64R64Effect 0x120253 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[1381, 1367]
    (.letOp (n := 1399) (.out 0x120256 (andR64R64Effect 0x120256 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[1397, 1393]
    (.letOp (n := 1400) (.exec 0x120256 (fun s => s.RIP = 0x120256) (andR64R64Effect 0x120256 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[1397, 1393]
    (.letOp (n := 1401) (.out 0x120259 (shrR64Effect 0x120259 4 14 52) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[1393]
    (.letOp (n := 1402) (.exec 0x120259 (fun s => s.RIP = 0x120259) (shrR64Effect 0x120259 4 14 52) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1393]
    (.letOp (n := 1403) (.out 0x12025d (addR64R64Effect 0x12025d 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[1395, 1389]
    (.letOp (n := 1404) (.exec 0x12025d (fun s => s.RIP = 0x12025d) (addR64R64Effect 0x12025d 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[1395, 1389]
    (.letOp (n := 1405) (.out 0x120260 (addR64R64Effect 0x120260 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[1403, 1401]
    (.letOp (n := 1406) (.exec 0x120260 (fun s => s.RIP = 0x120260) (addR64R64Effect 0x120260 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[1403, 1401]
    (.letOp (n := 1407) (.out 0x120263 (addR64R64Effect 0x120263 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[1347, 1389]
    (.letOp (n := 1408) (.exec 0x120263 (fun s => s.RIP = 0x120263) (addR64R64Effect 0x120263 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[1347, 1389]
    (.letOp (n := 1409) (.out 0x120266 (andR64R64Effect 0x120266 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[1399, 1405]
    (.letOp (n := 1410) (.exec 0x120266 (fun s => s.RIP = 0x120266) (andR64R64Effect 0x120266 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[1399, 1405]
    (.letOp (n := 1411) (.out 0x120269 (shrR64Effect 0x120269 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[1405]
    (.letOp (n := 1412) (.exec 0x120269 (fun s => s.RIP = 0x120269) (shrR64Effect 0x120269 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1405]
    (.letOp (n := 1413) (.out 0x12026d (addR64R64Effect 0x12026d 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[1407, 1411]
    (.letOp (n := 1414) (.exec 0x12026d (fun s => s.RIP = 0x12026d) (addR64R64Effect 0x12026d 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[1407, 1411]
    (.letOp (n := 1415) (.out 0x120270 (andR64R64Effect 0x120270 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[1409, 1413]
    (.letOp (n := 1416) (.exec 0x120270 (fun s => s.RIP = 0x120270) (andR64R64Effect 0x120270 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[1409, 1413]
    (.letOp (n := 1417) (.out 0x120273 (shrR64Effect 0x120273 4 10 52) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[1413]
    (.letOp (n := 1418) (.exec 0x120273 (fun s => s.RIP = 0x120273) (shrR64Effect 0x120273 4 10 52) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1413]
    (.letOp (n := 1419) (.out 0x120277 (addR64R64Effect 0x120277 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[1417, 1365]
    (.letOp (n := 1420) (.exec 0x120277 (fun s => s.RIP = 0x120277) (addR64R64Effect 0x120277 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[1417, 1365]
    (.letOp (n := 1421) (.out 0x12027a (movR64Imm64Effect 0x12027a 0 0xf000000000000) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1422) (.exec 0x12027a (fun s => s.RIP = 0x12027a) (movR64Imm64Effect 0x12027a 0 0xf000000000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 1423) (.out 0x120284 (xorR64R64Effect 0x120284 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[1421, 1419]
    (.letOp (n := 1424) (.exec 0x120284 (fun s => s.RIP = 0x120284) (xorR64R64Effect 0x120284 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[1421, 1419]
    (.letOp (n := 1425) (.out 0x120287 (andR64R64Effect 0x120287 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1415, 1423]
    (.letOp (n := 1426) (.exec 0x120287 (fun s => s.RIP = 0x120287) (andR64R64Effect 0x120287 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1415, 1423]
    (.letOp (n := 1427) (.out 0x12028a (xorR32R32Effect 0x12028a 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[1385, 1385]
    (.letOp (n := 1428) (.exec 0x12028a (fun s => s.RIP = 0x12028a) (xorR32R32Effect 0x12028a 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[1385, 1385]
    (.letOp (n := 1429) (.out 0x12028c (cmpR64R64Effect 0x12028c 1 3) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 3] []) (.flag .ZF)) #v[1425, 1283]
    (.letOp (n := 1430) (.exec 0x12028c (fun s => s.RIP = 0x12028c) (cmpR64R64Effect 0x12028c 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1425, 1283]
    (.letOp (n := 1431) (.out 0x12028f (atFlags (condHolds 4) (setccR8Effect 0x12028f 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[1427, 1429]
    (.letOp (n := 1432) (.exec 0x12028f (fun s => s.RIP = 0x12028f) (atFlags (condHolds 4) (setccR8Effect 0x12028f 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[1427, 1429]
    (.letOp (n := 1433) (.out 0x120293 (callEffect (fun _ => 0x127d50) 0x120298) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 1434) (.exec 0x120293 (PushPre 0x120293 5) (callEffect (fun _ => 0x127d50) 0x120298) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1435) (.const ⟨64, 0x120298⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 1423), (1, 1425), (2, 1367), (3, 1283), (4, 1433), (5, 1224), (6, 1389), (7, 1431), (8, 1411), (9, 1312), (10, 1419), (11, 1318), (12, 1218), (13, 1226), (14, 1401), (15, 1287), (19, 1429), (22, 22), (39, 39), (50, 50), (51, 51)] 1436⟩ { target := .l120298, kept := #v[], arity := rfl, guard := some (Fin.last 1435) }))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_31 : List UInt8 :=
  [0x48, 0x31, 0xD1, 0x4C, 0x21, 0xF1, 0x49, 0xC1, 0xEE, 0x34, 0x49, 0x01, 0xF0, 0x4D, 0x01, 0xF0,
    0x49, 0x01, 0xF2, 0x4C, 0x21, 0xC1, 0x49, 0xC1, 0xE8, 0x34, 0x4D, 0x01, 0xC2, 0x4C, 0x21, 0xD1,
    0x49, 0xC1, 0xEA, 0x34, 0x49, 0x01, 0xC2, 0x48, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0F,
    0x00, 0x4C, 0x31, 0xD0, 0x48, 0x21, 0xC1, 0x31, 0xFF, 0x48, 0x39, 0xD9, 0x40, 0x0F, 0x94, 0xC7,
    0xE8, 0xB8, 0x7A, 0x00, 0x00]

theorem code_l11f8f6_31 : ∀ x ∈ codeRange 0x120253 bytes_l11f8f6_31, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x20253 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l11f8f6_30 : Block Op Label signature Reg.count 1357 :=
  .letOp (n := 1357) (.out 0x1201e6 (movR64Imm64Effect 0x1201e6 0 0x3fffffffffffc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1358) (.exec 0x1201e6 (fun s => s.RIP = 0x1201e6) (movR64Imm64Effect 0x1201e6 0 0x3fffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 1359) (.out 0x1201f0 (addR64R64Effect 0x1201f0 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[1357, 1355]
    (.letOp (n := 1360) (.exec 0x1201f0 (fun s => s.RIP = 0x1201f0) (addR64R64Effect 0x1201f0 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[1357, 1355]
    (.letOp (n := 1361) (.out 0x1201f3 (movR64R64Effect 0x1201f3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1359]
    (.letOp (n := 1362) (.exec 0x1201f3 (fun s => s.RIP = 0x1201f3) (movR64R64Effect 0x1201f3 1 0) (Reg.operands [.gpr 0] [])) #v[1359]
    (.letOp (n := 1363) (.out 0x1201f6 (shrR64Effect 0x1201f6 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1361]
    (.letOp (n := 1364) (.exec 0x1201f6 (fun s => s.RIP = 0x1201f6) (shrR64Effect 0x1201f6 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1361]
    (.letOp (n := 1365) (.out 0x1201fa (andR64R64Effect 0x1201fa 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1359, 1349]
    (.letOp (n := 1366) (.exec 0x1201fa (fun s => s.RIP = 0x1201fa) (andR64R64Effect 0x1201fa 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1359, 1349]
    (.letOp (n := 1367) (.out 0x1201fd (movR64Imm64Effect 0x1201fd 2 0x1000003d0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1368) (.exec 0x1201fd (fun s => s.RIP = 0x1201fd) (movR64Imm64Effect 0x1201fd 2 0x1000003d0) (Reg.operands [] [])) #v[]
    (.letOp (n := 1369) (.out 0x120207 (leaR64Effect 0x120207 6 (.base 2 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1367]
    (.letOp (n := 1370) (.exec 0x120207 (fun s => s.RIP = 0x120207) (leaR64Effect 0x120207 6 (.base 2 (.d8 0x1))) (Reg.operands [.gpr 2] [])) #v[1367]
    (.letOp (n := 1371) (.out 0x12020b (imulR64R64Effect 0x12020b 4 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[1369, 1363]
    (.letOp (n := 1372) (.exec 0x12020b (fun s => s.RIP = 0x12020b) (imulR64R64Effect 0x12020b 4 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[1369, 1363]
    (.letOp (n := 1373) (.out 0x12020f (movR64M64Effect 0x12020f 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 1374) (.exec 0x12020f (LoadPre 0x12020f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x12020f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12020f 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1375) (.out 0x120214 (subR64M64Effect 0x120214 7 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[1373, 4]
    (.letOp (n := 1376) (.exec 0x120214 (LoadPre 0x120214 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x120214 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x120214 7 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1373, 4]
    (.letOp (n := 1377) (.out 0x12021c (movR64Imm64Effect 0x12021c 1 0x3ffffbfffff0c3) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1378) (.exec 0x12021c (fun s => s.RIP = 0x12021c) (movR64Imm64Effect 0x12021c 1 0x3ffffbfffff0c3) (Reg.operands [] [])) #v[]
    (.letOp (n := 1379) (.out 0x120226 (addR64R64Effect 0x120226 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[1377, 1375]
    (.letOp (n := 1380) (.exec 0x120226 (fun s => s.RIP = 0x120226) (addR64R64Effect 0x120226 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[1377, 1375]
    (.letOp (n := 1381) (.out 0x120229 (addR64R64Effect 0x120229 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[1379, 1371]
    (.letOp (n := 1382) (.exec 0x120229 (fun s => s.RIP = 0x120229) (addR64R64Effect 0x120229 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1379, 1371]
    (.letOp (n := 1383) (.out 0x12022c (movR64R64Effect 0x12022c 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[1381]
    (.letOp (n := 1384) (.exec 0x12022c (fun s => s.RIP = 0x12022c) (movR64R64Effect 0x12022c 7 1) (Reg.operands [.gpr 1] [])) #v[1381]
    (.letOp (n := 1385) (.out 0x12022f (shrR64Effect 0x12022f 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1383]
    (.letOp (n := 1386) (.exec 0x12022f (fun s => s.RIP = 0x12022f) (shrR64Effect 0x12022f 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1383]
    (.letOp (n := 1387) (.out 0x120233 (subR64M64Effect 0x120233 14 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[1251, 4]
    (.letOp (n := 1388) (.exec 0x120233 (LoadPre 0x120233 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x120233 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x120233 14 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[1251, 4]
    (.letOp (n := 1389) (.out 0x12023b (movR64Imm64Effect 0x12023b 6 0x3ffffffffffffc) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 1390) (.exec 0x12023b (fun s => s.RIP = 0x12023b) (movR64Imm64Effect 0x12023b 6 0x3ffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 1391) (.out 0x120245 (addR64R64Effect 0x120245 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[1387, 1389]
    (.letOp (n := 1392) (.exec 0x120245 (fun s => s.RIP = 0x120245) (addR64R64Effect 0x120245 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[1387, 1389]
    (.letOp (n := 1393) (.out 0x120248 (addR64R64Effect 0x120248 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[1391, 1385]
    (.letOp (n := 1394) (.exec 0x120248 (fun s => s.RIP = 0x120248) (addR64R64Effect 0x120248 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[1391, 1385]
    (.letOp (n := 1395) (.out 0x12024b (subR64M64Effect 0x12024b 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[1322, 4]
    (.letOp (n := 1396) (.exec 0x12024b (LoadPre 0x12024b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x12024b + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x12024b 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[1322, 4]
    (b_l11f8f6_31))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_30 : List UInt8 :=
  [0x48, 0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x00, 0x48, 0x01, 0xF8, 0x48, 0x89, 0xC1,
    0x48, 0xC1, 0xE9, 0x30, 0x48, 0x21, 0xF0, 0x48, 0xBA, 0xD0, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00,
    0x00, 0x48, 0x8D, 0x72, 0x01, 0x48, 0x0F, 0xAF, 0xF1, 0x48, 0x8B, 0x7C, 0x24, 0x40, 0x48, 0x2B,
    0xBC, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0xB9, 0xC3, 0xF0, 0xFF, 0xFF, 0xFB, 0xFF, 0x3F, 0x00,
    0x48, 0x01, 0xF9, 0x48, 0x01, 0xF1, 0x48, 0x89, 0xCF, 0x48, 0xC1, 0xEF, 0x34, 0x4C, 0x2B, 0xB4,
    0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0xBE, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00, 0x49,
    0x01, 0xF6, 0x49, 0x01, 0xFE, 0x4C, 0x2B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] ++ bytes_l11f8f6_31

theorem code_l11f8f6_30 : ∀ x ∈ codeRange 0x1201e6 bytes_l11f8f6_30, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x201e6 109 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_31

def b_l11f8f6_29 : Block Op Label signature Reg.count 1314 :=
  .letOp (n := 1314) (.out 0x120198 (shrR64Effect 0x120198 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1279]
    (.letOp (n := 1315) (.exec 0x120198 (fun s => s.RIP = 0x120198) (shrR64Effect 0x120198 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1279]
    (.letOp (n := 1316) (.out 0x12019c (movR64R64Effect 0x12019c 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 11] []) (.reg (.gpr 6))) #v[1310]
    (.letOp (n := 1317) (.exec 0x12019c (fun s => s.RIP = 0x12019c) (movR64R64Effect 0x12019c 6 11) (Reg.operands [.gpr 11] [])) #v[1310]
    (.letOp (n := 1318) (.out 0x12019f (shldR64R64Effect 0x12019f 5 11 8 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[1310, 1307]
    (.letOp (n := 1319) (.exec 0x12019f (fun s => s.RIP = 0x12019f) (shldR64R64Effect 0x12019f 5 11 8 12) (Reg.operands [.gpr 11, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1310, 1307]
    (.letOp (n := 1320) (.out 0x1201a4 (shrR64Effect 0x1201a4 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1316]
    (.letOp (n := 1321) (.exec 0x1201a4 (fun s => s.RIP = 0x1201a4) (shrR64Effect 0x1201a4 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1316]
    (.letOp (n := 1322) (.out 0x1201a8 (andR64R64Effect 0x1201a8 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[1307, 1283]
    (.letOp (n := 1323) (.exec 0x1201a8 (fun s => s.RIP = 0x1201a8) (andR64R64Effect 0x1201a8 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[1307, 1283]
    (.letOp (n := 1324) (.out 0x1201ab (imulR64R64Effect 0x1201ab 4 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[1314, 1287]
    (.letOp (n := 1325) (.exec 0x1201ab (fun s => s.RIP = 0x1201ab) (imulR64R64Effect 0x1201ab 4 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[1314, 1287]
    (.letOp (n := 1326) (.out 0x1201af (movR64R64Effect 0x1201af 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[1312]
    (.letOp (n := 1327) (.exec 0x1201af (fun s => s.RIP = 0x1201af) (movR64R64Effect 0x1201af 0 9) (Reg.operands [.gpr 9] [])) #v[1312]
    (.letOp (n := 1328) (.out 0x1201b2 (mulR64Effect 0x1201b2 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[1287, 1326]
    (.letOp (n := 1329) (.out 0x1201b2 (mulR64Effect 0x1201b2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[1287, 1326]
    (.letOp (n := 1330) (.exec 0x1201b2 (fun s => s.RIP = 0x1201b2) (mulR64Effect 0x1201b2 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[1287, 1326]
    (.letOp (n := 1331) (.out 0x1201b5 (andR64R64Effect 0x1201b5 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[927, 1283]
    (.letOp (n := 1332) (.exec 0x1201b5 (fun s => s.RIP = 0x1201b5) (andR64R64Effect 0x1201b5 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[927, 1283]
    (.letOp (n := 1333) (.out 0x1201b8 (addR64R64Effect 0x1201b8 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[1331, 1328]
    (.letOp (n := 1334) (.out 0x1201b8 (addR64R64Effect 0x1201b8 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[1331, 1328]
    (.letOp (n := 1335) (.exec 0x1201b8 (fun s => s.RIP = 0x1201b8) (addR64R64Effect 0x1201b8 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[1331, 1328]
    (.letOp (n := 1336) (.out 0x1201bb (atFlags StatusFlags.CF (adcR64R64Effect 0x1201bb 2 1)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[1329, 1324, 1334]
    (.letOp (n := 1337) (.exec 0x1201bb (fun s => s.RIP = 0x1201bb) (atFlags StatusFlags.CF (adcR64R64Effect 0x1201bb 2 1)) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1329, 1324, 1334]
    (.letOp (n := 1338) (.out 0x1201be (addR64R64Effect 0x1201be 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[1333, 1318]
    (.letOp (n := 1339) (.out 0x1201be (addR64R64Effect 0x1201be 10 11) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 11] []) (.flag .CF)) #v[1333, 1318]
    (.letOp (n := 1340) (.exec 0x1201be (fun s => s.RIP = 0x1201be) (addR64R64Effect 0x1201be 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[1333, 1318]
    (.letOp (n := 1341) (.out 0x1201c1 (atFlags StatusFlags.CF (adcR64R64Effect 0x1201c1 2 6)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[1336, 1320, 1339]
    (.letOp (n := 1342) (.exec 0x1201c1 (fun s => s.RIP = 0x1201c1) (atFlags StatusFlags.CF (adcR64R64Effect 0x1201c1 2 6)) (Reg.operands [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1336, 1320, 1339]
    (.letOp (n := 1343) (.out 0x1201c4 (shldR64R64Effect 0x1201c4 5 2 10 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1341, 1338]
    (.letOp (n := 1344) (.exec 0x1201c4 (fun s => s.RIP = 0x1201c4) (shldR64R64Effect 0x1201c4 5 2 10 12) (Reg.operands [.gpr 2, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1341, 1338]
    (.letOp (n := 1345) (.out 0x1201c9 (andR64R64Effect 0x1201c9 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[1338, 1283]
    (.letOp (n := 1346) (.exec 0x1201c9 (fun s => s.RIP = 0x1201c9) (andR64R64Effect 0x1201c9 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[1338, 1283]
    (.letOp (n := 1347) (.out 0x1201cc (subR64M64Effect 0x1201cc 10 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[1345, 4]
    (.letOp (n := 1348) (.exec 0x1201cc (LoadPre 0x1201cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1201cc + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1201cc 10 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[1345, 4]
    (.letOp (n := 1349) (.out 0x1201d1 (movR64Imm64Effect 0x1201d1 6 0xffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 1350) (.exec 0x1201d1 (fun s => s.RIP = 0x1201d1) (movR64Imm64Effect 0x1201d1 6 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1351) (.out 0x1201db (andR64R64Effect 0x1201db 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[1017, 1349]
    (.letOp (n := 1352) (.exec 0x1201db (fun s => s.RIP = 0x1201db) (andR64R64Effect 0x1201db 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[1017, 1349]
    (.letOp (n := 1353) (.out 0x1201de (addR64R64Effect 0x1201de 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[1351, 1343]
    (.letOp (n := 1354) (.exec 0x1201de (fun s => s.RIP = 0x1201de) (addR64R64Effect 0x1201de 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[1351, 1343]
    (.letOp (n := 1355) (.out 0x1201e1 (subR64M64Effect 0x1201e1 7 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[1353, 4]
    (.letOp (n := 1356) (.exec 0x1201e1 (LoadPre 0x1201e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1201e1 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1201e1 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1353, 4]
    (b_l11f8f6_30)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_29 : List UInt8 :=
  [0x48, 0xC1, 0xE9, 0x34, 0x4C, 0x89, 0xDE, 0x4D, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xC1, 0xEE, 0x34,
    0x49, 0x21, 0xD8, 0x49, 0x0F, 0xAF, 0xCF, 0x4C, 0x89, 0xC8, 0x49, 0xF7, 0xE7, 0x49, 0x21, 0xDA,
    0x49, 0x01, 0xC2, 0x48, 0x11, 0xCA, 0x4D, 0x01, 0xDA, 0x48, 0x11, 0xF2, 0x4C, 0x0F, 0xA4, 0xD2,
    0x0C, 0x49, 0x21, 0xDA, 0x4C, 0x2B, 0x54, 0x24, 0x68, 0x48, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x00, 0x00, 0x48, 0x21, 0xF7, 0x48, 0x01, 0xD7, 0x48, 0x2B, 0x7C, 0x24, 0x70] ++ bytes_l11f8f6_30

theorem code_l11f8f6_29 : ∀ x ∈ codeRange 0x120198 bytes_l11f8f6_29, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20198 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_30

def b_l11f8f6_28 : Block Op Label signature Reg.count 1267 :=
  .letOp (n := 1267) (.out 0x120144 (movR64R64Effect 0x120144 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1265]
    (.letOp (n := 1268) (.exec 0x120144 (fun s => s.RIP = 0x120144) (movR64R64Effect 0x120144 1 2) (Reg.operands [.gpr 2] [])) #v[1265]
    (.letOp (n := 1269) (.out 0x120147 (movR64R64Effect 0x120147 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[1264]
    (.letOp (n := 1270) (.exec 0x120147 (fun s => s.RIP = 0x120147) (movR64R64Effect 0x120147 9 0) (Reg.operands [.gpr 0] [])) #v[1264]
    (.letOp (n := 1271) (.out 0x12014a (addR64R64Effect 0x12014a 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15] []) (.reg (.gpr 9))) #v[1269, 1260]
    (.letOp (n := 1272) (.out 0x12014a (addR64R64Effect 0x12014a 9 15) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 15] []) (.flag .CF)) #v[1269, 1260]
    (.letOp (n := 1273) (.exec 0x12014a (fun s => s.RIP = 0x12014a) (addR64R64Effect 0x12014a 9 15) (Reg.operands [.gpr 9, .gpr 15] [])) #v[1269, 1260]
    (.letOp (n := 1274) (.out 0x12014d (atFlags StatusFlags.CF (adcR64R64Effect 0x12014d 1 3)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1267, 1258, 1272]
    (.letOp (n := 1275) (.exec 0x12014d (fun s => s.RIP = 0x12014d) (atFlags StatusFlags.CF (adcR64R64Effect 0x12014d 1 3)) (Reg.operands [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1267, 1258, 1272]
    (.letOp (n := 1276) (.out 0x120150 (addR64R64Effect 0x120150 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12] []) (.reg (.gpr 9))) #v[1271, 1218]
    (.letOp (n := 1277) (.out 0x120150 (addR64R64Effect 0x120150 9 12) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 12] []) (.flag .CF)) #v[1271, 1218]
    (.letOp (n := 1278) (.exec 0x120150 (fun s => s.RIP = 0x120150) (addR64R64Effect 0x120150 9 12) (Reg.operands [.gpr 9, .gpr 12] [])) #v[1271, 1218]
    (.letOp (n := 1279) (.out 0x120153 (atFlags StatusFlags.CF (adcR64R64Effect 0x120153 1 6)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1274, 1220, 1277]
    (.letOp (n := 1280) (.exec 0x120153 (fun s => s.RIP = 0x120153) (atFlags StatusFlags.CF (adcR64R64Effect 0x120153 1 6)) (Reg.operands [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1274, 1220, 1277]
    (.letOp (n := 1281) (.out 0x120156 (movR64R64Effect 0x120156 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[1276]
    (.letOp (n := 1282) (.exec 0x120156 (fun s => s.RIP = 0x120156) (movR64R64Effect 0x120156 0 9) (Reg.operands [.gpr 9] [])) #v[1276]
    (.letOp (n := 1283) (.out 0x120159 (movR64Imm64Effect 0x120159 3 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 1284) (.exec 0x120159 (fun s => s.RIP = 0x120159) (movR64Imm64Effect 0x120159 3 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1285) (.out 0x120163 (andR64R64Effect 0x120163 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[1281, 1283]
    (.letOp (n := 1286) (.exec 0x120163 (fun s => s.RIP = 0x120163) (andR64R64Effect 0x120163 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[1281, 1283]
    (.letOp (n := 1287) (.out 0x120166 (movR64Imm64Effect 0x120166 15 0x1000003d10) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 1288) (.exec 0x120166 (fun s => s.RIP = 0x120166) (movR64Imm64Effect 0x120166 15 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1289) (.out 0x120170 (mulR64Effect 0x120170 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[1287, 1285]
    (.letOp (n := 1290) (.out 0x120170 (mulR64Effect 0x120170 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[1287, 1285]
    (.letOp (n := 1291) (.exec 0x120170 (fun s => s.RIP = 0x120170) (mulR64Effect 0x120170 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[1287, 1285]
    (.letOp (n := 1292) (.out 0x120173 (addR64M64Effect 0x120173 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[1242, 4]
    (.letOp (n := 1293) (.out 0x120173 (addR64M64Effect 0x120173 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[1242, 4]
    (.letOp (n := 1294) (.exec 0x120173 (LoadPre 0x120173 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120173 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x120173 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[1242, 4]
    (.letOp (n := 1295) (.out 0x120178 (atFlags StatusFlags.CF (adcR64M64Effect 0x120178 11 (.sib 4 none 0 (.d8 0x18)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[1240, 4, 1293]
    (.letOp (n := 1296) (.exec 0x120178 (LoadPre 0x120178 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120178 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x120178 11 (.sib 4 none 0 (.d8 0x18)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1240, 4, 1293]
    (.letOp (n := 1297) (.out 0x12017d (addR64M64Effect 0x12017d 8 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[1292, 4]
    (.letOp (n := 1298) (.out 0x12017d (addR64M64Effect 0x12017d 8 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[1292, 4]
    (.letOp (n := 1299) (.exec 0x12017d (LoadPre 0x12017d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x12017d + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x12017d 8 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[1292, 4]
    (.letOp (n := 1300) (.out 0x120182 (atFlags StatusFlags.CF (adcR64M64Effect 0x120182 11 (.sib 4 none 0 (.d8 0x10)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[1295, 4, 1298]
    (.letOp (n := 1301) (.exec 0x120182 (LoadPre 0x120182 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120182 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x120182 11 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1295, 4, 1298]
    (.letOp (n := 1302) (.out 0x120187 (addR64R64Effect 0x120187 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[1297, 1289]
    (.letOp (n := 1303) (.out 0x120187 (addR64R64Effect 0x120187 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[1297, 1289]
    (.letOp (n := 1304) (.exec 0x120187 (fun s => s.RIP = 0x120187) (addR64R64Effect 0x120187 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1297, 1289]
    (.letOp (n := 1305) (.out 0x12018a (atFlags StatusFlags.CF (adcR64R64Effect 0x12018a 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[1300, 1290, 1303]
    (.letOp (n := 1306) (.exec 0x12018a (fun s => s.RIP = 0x12018a) (atFlags StatusFlags.CF (adcR64R64Effect 0x12018a 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1300, 1290, 1303]
    (.letOp (n := 1307) (.out 0x12018d (addR64R64Effect 0x12018d 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[1302, 1226]
    (.letOp (n := 1308) (.out 0x12018d (addR64R64Effect 0x12018d 8 13) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 13] []) (.flag .CF)) #v[1302, 1226]
    (.letOp (n := 1309) (.exec 0x12018d (fun s => s.RIP = 0x12018d) (addR64R64Effect 0x12018d 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[1302, 1226]
    (.letOp (n := 1310) (.out 0x120190 (atFlags StatusFlags.CF (adcR64R64Effect 0x120190 11 5)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[1305, 1224, 1308]
    (.letOp (n := 1311) (.exec 0x120190 (fun s => s.RIP = 0x120190) (atFlags StatusFlags.CF (adcR64R64Effect 0x120190 11 5)) (Reg.operands [.gpr 11, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1305, 1224, 1308]
    (.letOp (n := 1312) (.out 0x120193 (shrdR64R64Effect 0x120193 5 9 1 52) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[1276, 1279]
    (.letOp (n := 1313) (.exec 0x120193 (fun s => s.RIP = 0x120193) (shrdR64R64Effect 0x120193 5 9 1 52) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1276, 1279]
    (b_l11f8f6_29)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_28 : List UInt8 :=
  [0x48, 0x89, 0xD1, 0x49, 0x89, 0xC1, 0x4D, 0x01, 0xF9, 0x48, 0x11, 0xD9, 0x4D, 0x01, 0xE1, 0x48,
    0x11, 0xF1, 0x4C, 0x89, 0xC8, 0x48, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48,
    0x21, 0xD8, 0x49, 0xBF, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE7, 0x4C,
    0x03, 0x44, 0x24, 0x08, 0x4C, 0x13, 0x5C, 0x24, 0x18, 0x4C, 0x03, 0x44, 0x24, 0x48, 0x4C, 0x13,
    0x5C, 0x24, 0x10, 0x49, 0x01, 0xC0, 0x49, 0x11, 0xD3, 0x4D, 0x01, 0xE8, 0x49, 0x11, 0xEB, 0x49,
    0x0F, 0xAC, 0xC9, 0x34] ++ bytes_l11f8f6_29

theorem code_l11f8f6_28 : ∀ x ∈ codeRange 0x120144 bytes_l11f8f6_28, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20144 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_29

def b_l11f8f6_27 : Block Op Label signature Reg.count 1226 :=
  .letOp (n := 1226) (.out 0x1200ed (shldR64R64Effect 0x1200ed 5 13 14 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1214, 1211]
    (.letOp (n := 1227) (.exec 0x1200ed (fun s => s.RIP = 0x1200ed) (shldR64R64Effect 0x1200ed 5 13 14 12) (Reg.operands [.gpr 13, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1214, 1211]
    (.letOp (n := 1228) (.out 0x1200f2 (movR64M64Effect 0x1200f2 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1229) (.exec 0x1200f2 (LoadPre 0x1200f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1200f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1200f2 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1230) (.out 0x1200f7 (mulR64Effect 0x1200f7 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1168, 1228]
    (.letOp (n := 1231) (.out 0x1200f7 (mulR64Effect 0x1200f7 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1168, 1228]
    (.letOp (n := 1232) (.exec 0x1200f7 (fun s => s.RIP = 0x1200f7) (mulR64Effect 0x1200f7 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1168, 1228]
    (.letOp (n := 1233) (.exec 0x1200fa (StorePre 0x1200fa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1200fa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1200fa 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1231, 4]
    (.letOp (n := 1234) (.exec 0x1200ff (StorePre 0x1200ff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1200ff + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1200ff 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1230, 4]
    (.letOp (n := 1235) (.out 0x120104 (movR64M64Effect 0x120104 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1236) (.exec 0x120104 (LoadPre 0x120104 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120104 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120104 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1237) (.out 0x120109 (mulM64Effect 0x120109 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1235, 4]
    (.letOp (n := 1238) (.out 0x120109 (mulM64Effect 0x120109 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1235, 4]
    (.letOp (n := 1239) (.exec 0x120109 (LoadPre 0x120109 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x120109 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120109 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1235, 4]
    (.letOp (n := 1240) (.out 0x12010e (movR64R64Effect 0x12010e 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[1238]
    (.letOp (n := 1241) (.exec 0x12010e (fun s => s.RIP = 0x12010e) (movR64R64Effect 0x12010e 11 2) (Reg.operands [.gpr 2] [])) #v[1238]
    (.letOp (n := 1242) (.out 0x120111 (movR64R64Effect 0x120111 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[1237]
    (.letOp (n := 1243) (.exec 0x120111 (fun s => s.RIP = 0x120111) (movR64R64Effect 0x120111 8 0) (Reg.operands [.gpr 0] [])) #v[1237]
    (.letOp (n := 1244) (.out 0x120114 (movR64M64Effect 0x120114 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1245) (.exec 0x120114 (LoadPre 0x120114 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x120114 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120114 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1246) (.out 0x120119 (mulM64Effect 0x120119 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1244, 4]
    (.letOp (n := 1247) (.out 0x120119 (mulM64Effect 0x120119 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1244, 4]
    (.letOp (n := 1248) (.exec 0x120119 (LoadPre 0x120119 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x120119 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120119 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1244, 4]
    (.letOp (n := 1249) (.exec 0x12011e (StorePre 0x12011e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x12011e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12011e 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1246, 4]
    (.letOp (n := 1250) (.exec 0x120123 (StorePre 0x120123 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120123 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120123 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1247, 4]
    (.letOp (n := 1251) (.out 0x120128 (andR64R64Effect 0x120128 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[1211, 1192]
    (.letOp (n := 1252) (.exec 0x120128 (fun s => s.RIP = 0x120128) (andR64R64Effect 0x120128 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[1211, 1192]
    (.letOp (n := 1253) (.out 0x12012b (movR64M64Effect 0x12012b 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1254) (.exec 0x12012b (LoadPre 0x12012b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x12012b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12012b 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1255) (.out 0x120130 (mulM64Effect 0x120130 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1253, 4]
    (.letOp (n := 1256) (.out 0x120130 (mulM64Effect 0x120130 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1253, 4]
    (.letOp (n := 1257) (.exec 0x120130 (LoadPre 0x120130 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x120130 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120130 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1253, 4]
    (.letOp (n := 1258) (.out 0x120135 (movR64R64Effect 0x120135 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[1256]
    (.letOp (n := 1259) (.exec 0x120135 (fun s => s.RIP = 0x120135) (movR64R64Effect 0x120135 3 2) (Reg.operands [.gpr 2] [])) #v[1256]
    (.letOp (n := 1260) (.out 0x120138 (movR64R64Effect 0x120138 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[1255]
    (.letOp (n := 1261) (.exec 0x120138 (fun s => s.RIP = 0x120138) (movR64R64Effect 0x120138 15 0) (Reg.operands [.gpr 0] [])) #v[1255]
    (.letOp (n := 1262) (.out 0x12013b (movR64M64Effect 0x12013b 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1263) (.exec 0x12013b (LoadPre 0x12013b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12013b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12013b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1264) (.out 0x12013f (mulM64Effect 0x12013f 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1262, 4]
    (.letOp (n := 1265) (.out 0x12013f (mulM64Effect 0x12013f 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1262, 4]
    (.letOp (n := 1266) (.exec 0x12013f (LoadPre 0x12013f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x12013f + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x12013f 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1262, 4]
    (b_l11f8f6_28)))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_27 : List UInt8 :=
  [0x4D, 0x0F, 0xA4, 0xF5, 0x0C, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0x54,
    0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0xF7, 0x64, 0x24,
    0x30, 0x49, 0x89, 0xD3, 0x49, 0x89, 0xC0, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0xF7, 0x64, 0x24,
    0x50, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48, 0x89, 0x54, 0x24, 0x10, 0x4D, 0x21, 0xCE, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0xF7, 0x64, 0x24, 0x20, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC7, 0x48, 0x8B,
    0x04, 0x24, 0x48, 0xF7, 0x64, 0x24, 0x38] ++ bytes_l11f8f6_28

theorem code_l11f8f6_27 : ∀ x ∈ codeRange 0x1200ed bytes_l11f8f6_27, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x200ed 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_28

def b_l11f8f6_26 : Block Op Label signature Reg.count 1180 :=
  .letOp (n := 1180) (.out 0x12009a (addR64R64Effect 0x12009a 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[1173, 1175]
    (.letOp (n := 1181) (.out 0x12009a (addR64R64Effect 0x12009a 11 3) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 3] []) (.flag .CF)) #v[1173, 1175]
    (.letOp (n := 1182) (.exec 0x12009a (fun s => s.RIP = 0x12009a) (addR64R64Effect 0x12009a 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[1173, 1175]
    (.letOp (n := 1183) (.out 0x12009d (atFlags StatusFlags.CF (adcR64R64Effect 0x12009d 12 2)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[1178, 1171, 1181]
    (.letOp (n := 1184) (.exec 0x12009d (fun s => s.RIP = 0x12009d) (atFlags StatusFlags.CF (adcR64R64Effect 0x12009d 12 2)) (Reg.operands [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1178, 1171, 1181]
    (.letOp (n := 1185) (.out 0x1200a0 (addR64R64Effect 0x1200a0 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[1180, 1099]
    (.letOp (n := 1186) (.out 0x1200a0 (addR64R64Effect 0x1200a0 11 15) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 15] []) (.flag .CF)) #v[1180, 1099]
    (.letOp (n := 1187) (.exec 0x1200a0 (fun s => s.RIP = 0x1200a0) (addR64R64Effect 0x1200a0 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[1180, 1099]
    (.letOp (n := 1188) (.out 0x1200a3 (atFlags StatusFlags.CF (adcR64R64Effect 0x1200a3 12 9)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[1183, 1116, 1186]
    (.letOp (n := 1189) (.exec 0x1200a3 (fun s => s.RIP = 0x1200a3) (atFlags StatusFlags.CF (adcR64R64Effect 0x1200a3 12 9)) (Reg.operands [.gpr 12, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1183, 1116, 1186]
    (.letOp (n := 1190) (.out 0x1200a6 (movR64R64Effect 0x1200a6 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[1185]
    (.letOp (n := 1191) (.exec 0x1200a6 (fun s => s.RIP = 0x1200a6) (movR64R64Effect 0x1200a6 0 11) (Reg.operands [.gpr 11] [])) #v[1185]
    (.letOp (n := 1192) (.out 0x1200a9 (movR64Imm64Effect 0x1200a9 9 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 1193) (.exec 0x1200a9 (fun s => s.RIP = 0x1200a9) (movR64Imm64Effect 0x1200a9 9 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1194) (.out 0x1200b3 (andR64R64Effect 0x1200b3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[1190, 1192]
    (.letOp (n := 1195) (.exec 0x1200b3 (fun s => s.RIP = 0x1200b3) (andR64R64Effect 0x1200b3 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[1190, 1192]
    (.letOp (n := 1196) (.out 0x1200b6 (movR64Imm64Effect 0x1200b6 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1197) (.exec 0x1200b6 (fun s => s.RIP = 0x1200b6) (movR64Imm64Effect 0x1200b6 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1198) (.out 0x1200c0 (mulR64Effect 0x1200c0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1196, 1194]
    (.letOp (n := 1199) (.out 0x1200c0 (mulR64Effect 0x1200c0 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1196, 1194]
    (.letOp (n := 1200) (.exec 0x1200c0 (fun s => s.RIP = 0x1200c0) (mulR64Effect 0x1200c0 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1196, 1194]
    (.letOp (n := 1201) (.out 0x1200c3 (addR64M64Effect 0x1200c3 14 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[1139, 4]
    (.letOp (n := 1202) (.out 0x1200c3 (addR64M64Effect 0x1200c3 14 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 4] []) (.flag .CF)) #v[1139, 4]
    (.letOp (n := 1203) (.exec 0x1200c3 (LoadPre 0x1200c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1200c3 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1200c3 14 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[1139, 4]
    (.letOp (n := 1204) (.out 0x1200c8 (atFlags StatusFlags.CF (adcR64M64Effect 0x1200c8 13 (.sib 4 none 0 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 13))) #v[1141, 4, 1202]
    (.letOp (n := 1205) (.exec 0x1200c8 (LoadPre 0x1200c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1200c8 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1200c8 13 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1141, 4, 1202]
    (.letOp (n := 1206) (.out 0x1200cd (addR64R64Effect 0x1200cd 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[1201, 1198]
    (.letOp (n := 1207) (.out 0x1200cd (addR64R64Effect 0x1200cd 14 0) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 0] []) (.flag .CF)) #v[1201, 1198]
    (.letOp (n := 1208) (.exec 0x1200cd (fun s => s.RIP = 0x1200cd) (addR64R64Effect 0x1200cd 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[1201, 1198]
    (.letOp (n := 1209) (.out 0x1200d0 (atFlags StatusFlags.CF (adcR64R64Effect 0x1200d0 13 2)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[1204, 1199, 1207]
    (.letOp (n := 1210) (.exec 0x1200d0 (fun s => s.RIP = 0x1200d0) (atFlags StatusFlags.CF (adcR64R64Effect 0x1200d0 13 2)) (Reg.operands [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1204, 1199, 1207]
    (.letOp (n := 1211) (.out 0x1200d3 (addR64R64Effect 0x1200d3 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[1206, 1123]
    (.letOp (n := 1212) (.out 0x1200d3 (addR64R64Effect 0x1200d3 14 5) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 5] []) (.flag .CF)) #v[1206, 1123]
    (.letOp (n := 1213) (.exec 0x1200d3 (fun s => s.RIP = 0x1200d3) (addR64R64Effect 0x1200d3 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[1206, 1123]
    (.letOp (n := 1214) (.out 0x1200d6 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1200d6 13 0x0)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[1209, 1212]
    (.letOp (n := 1215) (.exec 0x1200d6 (fun s => s.RIP = 0x1200d6) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1200d6 13 0x0)) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1209, 1212]
    (.letOp (n := 1216) (.out 0x1200da (movR64R64Effect 0x1200da 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[1188]
    (.letOp (n := 1217) (.exec 0x1200da (fun s => s.RIP = 0x1200da) (movR64R64Effect 0x1200da 6 12) (Reg.operands [.gpr 12] [])) #v[1188]
    (.letOp (n := 1218) (.out 0x1200dd (shldR64R64Effect 0x1200dd 5 12 11 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1188, 1185]
    (.letOp (n := 1219) (.exec 0x1200dd (fun s => s.RIP = 0x1200dd) (shldR64R64Effect 0x1200dd 5 12 11 12) (Reg.operands [.gpr 12, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1188, 1185]
    (.letOp (n := 1220) (.out 0x1200e2 (shrR64Effect 0x1200e2 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1216]
    (.letOp (n := 1221) (.exec 0x1200e2 (fun s => s.RIP = 0x1200e2) (shrR64Effect 0x1200e2 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1216]
    (.letOp (n := 1222) (.out 0x1200e6 (movR64R64Effect 0x1200e6 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 13] []) (.reg (.gpr 5))) #v[1214]
    (.letOp (n := 1223) (.exec 0x1200e6 (fun s => s.RIP = 0x1200e6) (movR64R64Effect 0x1200e6 5 13) (Reg.operands [.gpr 13] [])) #v[1214]
    (.letOp (n := 1224) (.out 0x1200e9 (shrR64Effect 0x1200e9 4 5 52) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[1222]
    (.letOp (n := 1225) (.exec 0x1200e9 (fun s => s.RIP = 0x1200e9) (shrR64Effect 0x1200e9 4 5 52) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1222]
    (b_l11f8f6_27))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_26 : List UInt8 :=
  [0x49, 0x01, 0xDB, 0x49, 0x11, 0xD4, 0x4D, 0x01, 0xFB, 0x4D, 0x11, 0xCC, 0x4C, 0x89, 0xD8, 0x49,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xC8, 0x48, 0xBA, 0x10, 0x3D,
    0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x03, 0x74, 0x24, 0x60, 0x4C, 0x13,
    0x6C, 0x24, 0x08, 0x49, 0x01, 0xC6, 0x49, 0x11, 0xD5, 0x49, 0x01, 0xEE, 0x49, 0x83, 0xD5, 0x00,
    0x4C, 0x89, 0xE6, 0x4D, 0x0F, 0xA4, 0xDC, 0x0C, 0x48, 0xC1, 0xEE, 0x34, 0x4C, 0x89, 0xED, 0x48,
    0xC1, 0xED, 0x34] ++ bytes_l11f8f6_27

theorem code_l11f8f6_26 : ∀ x ∈ codeRange 0x12009a bytes_l11f8f6_26, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2009a 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_27

def b_l11f8f6_25 : Block Op Label signature Reg.count 1136 :=
  .letOp (n := 1136) (.out 0x12004a (mulM64Effect 0x12004a 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1134, 4]
    (.letOp (n := 1137) (.out 0x12004a (mulM64Effect 0x12004a 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1134, 4]
    (.letOp (n := 1138) (.exec 0x12004a (LoadPre 0x12004a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x12004a + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x12004a 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1134, 4]
    (.letOp (n := 1139) (.out 0x12004f (movR64R64Effect 0x12004f 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[1136]
    (.letOp (n := 1140) (.exec 0x12004f (fun s => s.RIP = 0x12004f) (movR64R64Effect 0x12004f 14 0) (Reg.operands [.gpr 0] [])) #v[1136]
    (.letOp (n := 1141) (.out 0x120052 (movR64R64Effect 0x120052 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[1137]
    (.letOp (n := 1142) (.exec 0x120052 (fun s => s.RIP = 0x120052) (movR64R64Effect 0x120052 13 2) (Reg.operands [.gpr 2] [])) #v[1137]
    (.letOp (n := 1143) (.out 0x120055 (movR64Imm64Effect 0x120055 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1144) (.exec 0x120055 (fun s => s.RIP = 0x120055) (movR64Imm64Effect 0x120055 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1145) (.out 0x12005f (andR64R64Effect 0x12005f 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1125, 1143]
    (.letOp (n := 1146) (.exec 0x12005f (fun s => s.RIP = 0x12005f) (andR64R64Effect 0x12005f 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1125, 1143]
    (.letOp (n := 1147) (.exec 0x120062 (StorePre 0x120062 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x120062 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120062 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1145, 4]
    (.letOp (n := 1148) (.out 0x120067 (movR64R64Effect 0x120067 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[1048]
    (.letOp (n := 1149) (.exec 0x120067 (fun s => s.RIP = 0x120067) (movR64R64Effect 0x120067 0 12) (Reg.operands [.gpr 12] [])) #v[1048]
    (.letOp (n := 1150) (.out 0x12006a (mulM64Effect 0x12006a 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1148, 4]
    (.letOp (n := 1151) (.out 0x12006a (mulM64Effect 0x12006a 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1148, 4]
    (.letOp (n := 1152) (.exec 0x12006a (LoadPre 0x12006a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x12006a + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x12006a 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1148, 4]
    (.letOp (n := 1153) (.out 0x12006f (movR64R64Effect 0x12006f 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1151]
    (.letOp (n := 1154) (.exec 0x12006f (fun s => s.RIP = 0x12006f) (movR64R64Effect 0x12006f 6 2) (Reg.operands [.gpr 2] [])) #v[1151]
    (.letOp (n := 1155) (.out 0x120072 (movR64R64Effect 0x120072 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[1150]
    (.letOp (n := 1156) (.exec 0x120072 (fun s => s.RIP = 0x120072) (movR64R64Effect 0x120072 8 0) (Reg.operands [.gpr 0] [])) #v[1150]
    (.letOp (n := 1157) (.out 0x120075 (movR64M64Effect 0x120075 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1158) (.exec 0x120075 (LoadPre 0x120075 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x120075 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120075 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1159) (.out 0x12007a (mulM64Effect 0x12007a 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1157, 4]
    (.letOp (n := 1160) (.out 0x12007a (mulM64Effect 0x12007a 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1157, 4]
    (.letOp (n := 1161) (.exec 0x12007a (LoadPre 0x12007a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x12007a + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x12007a 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1157, 4]
    (.letOp (n := 1162) (.out 0x12007f (movR64R64Effect 0x12007f 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[1160]
    (.letOp (n := 1163) (.exec 0x12007f (fun s => s.RIP = 0x12007f) (movR64R64Effect 0x12007f 12 2) (Reg.operands [.gpr 2] [])) #v[1160]
    (.letOp (n := 1164) (.out 0x120082 (movR64R64Effect 0x120082 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[1159]
    (.letOp (n := 1165) (.exec 0x120082 (fun s => s.RIP = 0x120082) (movR64R64Effect 0x120082 3 0) (Reg.operands [.gpr 0] [])) #v[1159]
    (.letOp (n := 1166) (.out 0x120085 (movR64M64Effect 0x120085 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1167) (.exec 0x120085 (LoadPre 0x120085 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x120085 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120085 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1168) (.out 0x120089 (movR64M64Effect 0x120089 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 1169) (.exec 0x120089 (LoadPre 0x120089 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x120089 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120089 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1170) (.out 0x12008e (mulR64Effect 0x12008e 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1168, 1166]
    (.letOp (n := 1171) (.out 0x12008e (mulR64Effect 0x12008e 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1168, 1166]
    (.letOp (n := 1172) (.exec 0x12008e (fun s => s.RIP = 0x12008e) (mulR64Effect 0x12008e 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1168, 1166]
    (.letOp (n := 1173) (.out 0x120091 (movR64R64Effect 0x120091 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[1170]
    (.letOp (n := 1174) (.exec 0x120091 (fun s => s.RIP = 0x120091) (movR64R64Effect 0x120091 11 0) (Reg.operands [.gpr 0] [])) #v[1170]
    (.letOp (n := 1175) (.out 0x120094 (addR64R64Effect 0x120094 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[1164, 1155]
    (.letOp (n := 1176) (.out 0x120094 (addR64R64Effect 0x120094 3 8) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 8] []) (.flag .CF)) #v[1164, 1155]
    (.letOp (n := 1177) (.exec 0x120094 (fun s => s.RIP = 0x120094) (addR64R64Effect 0x120094 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[1164, 1155]
    (.letOp (n := 1178) (.out 0x120097 (atFlags StatusFlags.CF (adcR64R64Effect 0x120097 12 6)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[1162, 1153, 1176]
    (.letOp (n := 1179) (.exec 0x120097 (fun s => s.RIP = 0x120097) (atFlags StatusFlags.CF (adcR64R64Effect 0x120097 12 6)) (Reg.operands [.gpr 12, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1162, 1153, 1176]
    (b_l11f8f6_26))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_25 : List UInt8 :=
  [0x48, 0xF7, 0x64, 0x24, 0x50, 0x49, 0x89, 0xC6, 0x49, 0x89, 0xD5, 0x48, 0xB8, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC1, 0x48, 0x89, 0x4C, 0x24, 0x40, 0x4C, 0x89, 0xE0,
    0x48, 0xF7, 0x64, 0x24, 0x20, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC0, 0x48, 0x8B, 0x44, 0x24, 0x28,
    0x48, 0xF7, 0x64, 0x24, 0x38, 0x49, 0x89, 0xD4, 0x48, 0x89, 0xC3, 0x48, 0x8B, 0x04, 0x24, 0x48,
    0x8B, 0x4C, 0x24, 0x58, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xC3, 0x4C, 0x01, 0xC3, 0x49, 0x11, 0xF4] ++ bytes_l11f8f6_26

theorem code_l11f8f6_25 : ∀ x ∈ codeRange 0x12004a bytes_l11f8f6_25, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2004a 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_26

def b_l11f8f6_24 : Block Op Label signature Reg.count 1095 :=
  .letOp (n := 1095) (.out 0x11ffee (atFlags StatusFlags.CF (adcR64R64Effect 0x11ffee 15 9)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[1090, 1024, 1093]
    (.letOp (n := 1096) (.exec 0x11ffee (fun s => s.RIP = 0x11ffee) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ffee 15 9)) (Reg.operands [.gpr 15, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1090, 1024, 1093]
    (.letOp (n := 1097) (.out 0x11fff1 (movR64R64Effect 0x11fff1 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 15] []) (.reg (.gpr 9))) #v[1095]
    (.letOp (n := 1098) (.exec 0x11fff1 (fun s => s.RIP = 0x11fff1) (movR64R64Effect 0x11fff1 9 15) (Reg.operands [.gpr 15] [])) #v[1095]
    (.letOp (n := 1099) (.out 0x11fff4 (shldR64R64Effect 0x11fff4 5 15 0 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[1095, 1092]
    (.letOp (n := 1100) (.exec 0x11fff4 (fun s => s.RIP = 0x11fff4) (shldR64R64Effect 0x11fff4 5 15 0 12) (Reg.operands [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1095, 1092]
    (.letOp (n := 1101) (.out 0x11fff9 (shlR64Effect 0x11fff9 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1092]
    (.letOp (n := 1102) (.exec 0x11fff9 (fun s => s.RIP = 0x11fff9) (shlR64Effect 0x11fff9 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1092]
    (.letOp (n := 1103) (.out 0x11fffd (movR64Imm64Effect 0x11fffd 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1104) (.exec 0x11fffd (fun s => s.RIP = 0x11fffd) (movR64Imm64Effect 0x11fffd 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 1105) (.out 0x120007 (andR64R64Effect 0x120007 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1101, 1103]
    (.letOp (n := 1106) (.exec 0x120007 (fun s => s.RIP = 0x120007) (andR64R64Effect 0x120007 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1101, 1103]
    (.letOp (n := 1107) (.out 0x12000a (orR64R64Effect 0x12000a 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1105, 1075]
    (.letOp (n := 1108) (.exec 0x12000a (fun s => s.RIP = 0x12000a) (orR64R64Effect 0x12000a 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1105, 1075]
    (.letOp (n := 1109) (.out 0x12000d (movR64Imm64Effect 0x12000d 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1110) (.exec 0x12000d (fun s => s.RIP = 0x12000d) (movR64Imm64Effect 0x12000d 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 1111) (.out 0x120017 (mulR64Effect 0x120017 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1109, 1107]
    (.letOp (n := 1112) (.out 0x120017 (mulR64Effect 0x120017 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1109, 1107]
    (.letOp (n := 1113) (.exec 0x120017 (fun s => s.RIP = 0x120017) (mulR64Effect 0x120017 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1109, 1107]
    (.letOp (n := 1114) (.out 0x12001a (movR64R64Effect 0x12001a 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[1112]
    (.letOp (n := 1115) (.exec 0x12001a (fun s => s.RIP = 0x12001a) (movR64R64Effect 0x12001a 5 2) (Reg.operands [.gpr 2] [])) #v[1112]
    (.letOp (n := 1116) (.out 0x12001d (shrR64Effect 0x12001d 4 9 52) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[1097]
    (.letOp (n := 1117) (.exec 0x12001d (fun s => s.RIP = 0x12001d) (shrR64Effect 0x12001d 4 9 52) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1097]
    (.letOp (n := 1118) (.out 0x120021 (addR64M64Effect 0x120021 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1111, 4]
    (.letOp (n := 1119) (.out 0x120021 (addR64M64Effect 0x120021 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[1111, 4]
    (.letOp (n := 1120) (.exec 0x120021 (LoadPre 0x120021 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120021 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x120021 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1111, 4]
    (.letOp (n := 1121) (.out 0x120026 (atFlags StatusFlags.CF (adcR64M64Effect 0x120026 5 (.sib 4 none 0 (.d8 0x40)))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 5))) #v[1114, 4, 1119]
    (.letOp (n := 1122) (.exec 0x120026 (LoadPre 0x120026 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x120026 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x120026 5 (.sib 4 none 0 (.d8 0x40)))) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1114, 4, 1119]
    (.letOp (n := 1123) (.out 0x12002b (shldR64R64Effect 0x12002b 5 5 0 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[1121, 1118]
    (.letOp (n := 1124) (.exec 0x12002b (fun s => s.RIP = 0x12002b) (shldR64R64Effect 0x12002b 5 5 0 12) (Reg.operands [.gpr 5, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1121, 1118]
    (.letOp (n := 1125) (.out 0x120030 (movR64R64Effect 0x120030 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1118]
    (.letOp (n := 1126) (.exec 0x120030 (fun s => s.RIP = 0x120030) (movR64R64Effect 0x120030 1 0) (Reg.operands [.gpr 0] [])) #v[1118]
    (.letOp (n := 1127) (.out 0x120033 (movR64M64Effect 0x120033 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1128) (.exec 0x120033 (LoadPre 0x120033 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120033 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120033 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1129) (.out 0x120038 (mulR64Effect 0x120038 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[1070, 1127]
    (.letOp (n := 1130) (.out 0x120038 (mulR64Effect 0x120038 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[1070, 1127]
    (.letOp (n := 1131) (.exec 0x120038 (fun s => s.RIP = 0x120038) (mulR64Effect 0x120038 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1070, 1127]
    (.letOp (n := 1132) (.exec 0x12003b (StorePre 0x12003b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12003b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12003b 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1130, 4]
    (.letOp (n := 1133) (.exec 0x120040 (StorePre 0x120040 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x120040 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120040 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1129, 4]
    (.letOp (n := 1134) (.out 0x120045 (movR64M64Effect 0x120045 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1135) (.exec 0x120045 (LoadPre 0x120045 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120045 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120045 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l11f8f6_25)))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_24 : List UInt8 :=
  [0x4D, 0x11, 0xCF, 0x4D, 0x89, 0xF9, 0x49, 0x0F, 0xA4, 0xC7, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48,
    0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x48, 0x09, 0xF0, 0x48,
    0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD5, 0x49,
    0xC1, 0xE9, 0x34, 0x48, 0x03, 0x44, 0x24, 0x08, 0x48, 0x13, 0x6C, 0x24, 0x40, 0x48, 0x0F, 0xA4,
    0xC5, 0x0C, 0x48, 0x89, 0xC1, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0x54,
    0x24, 0x08, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x44, 0x24, 0x10] ++ bytes_l11f8f6_25

theorem code_l11f8f6_24 : ∀ x ∈ codeRange 0x11ffee bytes_l11f8f6_24, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ffee 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_25

def b_l11f8f6_23 : Block Op Label signature Reg.count 1048 :=
  .letOp (n := 1048) (.out 0x11ffa7 (movR64M64Effect 0x11ffa7 12 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 1049) (.exec 0x11ffa7 (LoadPre 0x11ffa7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11ffa7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ffa7 12 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1050) (.out 0x11ffac (movR64R64Effect 0x11ffac 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[1048]
    (.letOp (n := 1051) (.exec 0x11ffac (fun s => s.RIP = 0x11ffac) (movR64R64Effect 0x11ffac 0 12) (Reg.operands [.gpr 12] [])) #v[1048]
    (.letOp (n := 1052) (.out 0x11ffaf (mulM64Effect 0x11ffaf 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1050, 4]
    (.letOp (n := 1053) (.out 0x11ffaf (mulM64Effect 0x11ffaf 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1050, 4]
    (.letOp (n := 1054) (.exec 0x11ffaf (LoadPre 0x11ffaf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11ffaf + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11ffaf 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1050, 4]
    (.letOp (n := 1055) (.out 0x11ffb4 (movR64R64Effect 0x11ffb4 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[1053]
    (.letOp (n := 1056) (.exec 0x11ffb4 (fun s => s.RIP = 0x11ffb4) (movR64R64Effect 0x11ffb4 15 2) (Reg.operands [.gpr 2] [])) #v[1053]
    (.letOp (n := 1057) (.out 0x11ffb7 (movR64R64Effect 0x11ffb7 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[1052]
    (.letOp (n := 1058) (.exec 0x11ffb7 (fun s => s.RIP = 0x11ffb7) (movR64R64Effect 0x11ffb7 11 0) (Reg.operands [.gpr 0] [])) #v[1052]
    (.letOp (n := 1059) (.out 0x11ffba (movR64M64Effect 0x11ffba 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1060) (.exec 0x11ffba (LoadPre 0x11ffba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11ffba + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ffba 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1061) (.out 0x11ffbf (mulM64Effect 0x11ffbf 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1059, 4]
    (.letOp (n := 1062) (.out 0x11ffbf (mulM64Effect 0x11ffbf 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1059, 4]
    (.letOp (n := 1063) (.exec 0x11ffbf (LoadPre 0x11ffbf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11ffbf + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11ffbf 5 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1059, 4]
    (.letOp (n := 1064) (.out 0x11ffc4 (movR64R64Effect 0x11ffc4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[1062]
    (.letOp (n := 1065) (.exec 0x11ffc4 (fun s => s.RIP = 0x11ffc4) (movR64R64Effect 0x11ffc4 13 2) (Reg.operands [.gpr 2] [])) #v[1062]
    (.letOp (n := 1066) (.out 0x11ffc7 (movR64R64Effect 0x11ffc7 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[1061]
    (.letOp (n := 1067) (.exec 0x11ffc7 (fun s => s.RIP = 0x11ffc7) (movR64R64Effect 0x11ffc7 5 0) (Reg.operands [.gpr 0] [])) #v[1061]
    (.letOp (n := 1068) (.out 0x11ffca (movR64M64Effect 0x11ffca 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1069) (.exec 0x11ffca (LoadPre 0x11ffca (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11ffca + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11ffca 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1070) (.out 0x11ffce (movR64M64Effect 0x11ffce 8 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 1071) (.exec 0x11ffce (LoadPre 0x11ffce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11ffce + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ffce 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1072) (.out 0x11ffd3 (mulR64Effect 0x11ffd3 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[1070, 1068]
    (.letOp (n := 1073) (.out 0x11ffd3 (mulR64Effect 0x11ffd3 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[1070, 1068]
    (.letOp (n := 1074) (.exec 0x11ffd3 (fun s => s.RIP = 0x11ffd3) (mulR64Effect 0x11ffd3 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1070, 1068]
    (.letOp (n := 1075) (.out 0x11ffd6 (andR32Imm8Effect 0x11ffd6 3 6 0xf) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[1046]
    (.letOp (n := 1076) (.exec 0x11ffd6 (fun s => s.RIP = 0x11ffd6) (andR32Imm8Effect 0x11ffd6 3 6 0xf) (Reg.operands [.gpr 6] [])) #v[1046]
    (.letOp (n := 1077) (.out 0x11ffd9 (addR64R64Effect 0x11ffd9 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[1057, 1040]
    (.letOp (n := 1078) (.out 0x11ffd9 (addR64R64Effect 0x11ffd9 11 1) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 1] []) (.flag .CF)) #v[1057, 1040]
    (.letOp (n := 1079) (.exec 0x11ffd9 (fun s => s.RIP = 0x11ffd9) (addR64R64Effect 0x11ffd9 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[1057, 1040]
    (.letOp (n := 1080) (.out 0x11ffdc (atFlags StatusFlags.CF (adcR64R64Effect 0x11ffdc 15 14)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[1055, 1042, 1078]
    (.letOp (n := 1081) (.exec 0x11ffdc (fun s => s.RIP = 0x11ffdc) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ffdc 15 14)) (Reg.operands [.gpr 15, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1055, 1042, 1078]
    (.letOp (n := 1082) (.out 0x11ffdf (addR64R64Effect 0x11ffdf 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[1077, 1066]
    (.letOp (n := 1083) (.out 0x11ffdf (addR64R64Effect 0x11ffdf 11 5) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 5] []) (.flag .CF)) #v[1077, 1066]
    (.letOp (n := 1084) (.exec 0x11ffdf (fun s => s.RIP = 0x11ffdf) (addR64R64Effect 0x11ffdf 11 5) (Reg.operands [.gpr 11, .gpr 5] [])) #v[1077, 1066]
    (.letOp (n := 1085) (.out 0x11ffe2 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ffe2 15 13)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[1080, 1064, 1083]
    (.letOp (n := 1086) (.exec 0x11ffe2 (fun s => s.RIP = 0x11ffe2) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ffe2 15 13)) (Reg.operands [.gpr 15, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1080, 1064, 1083]
    (.letOp (n := 1087) (.out 0x11ffe5 (addR64R64Effect 0x11ffe5 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[1072, 1082]
    (.letOp (n := 1088) (.out 0x11ffe5 (addR64R64Effect 0x11ffe5 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[1072, 1082]
    (.letOp (n := 1089) (.exec 0x11ffe5 (fun s => s.RIP = 0x11ffe5) (addR64R64Effect 0x11ffe5 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[1072, 1082]
    (.letOp (n := 1090) (.out 0x11ffe8 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ffe8 15 2)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[1085, 1073, 1088]
    (.letOp (n := 1091) (.exec 0x11ffe8 (fun s => s.RIP = 0x11ffe8) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ffe8 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1085, 1073, 1088]
    (.letOp (n := 1092) (.out 0x11ffeb (addR64R64Effect 0x11ffeb 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[1087, 1026]
    (.letOp (n := 1093) (.out 0x11ffeb (addR64R64Effect 0x11ffeb 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[1087, 1026]
    (.letOp (n := 1094) (.exec 0x11ffeb (fun s => s.RIP = 0x11ffeb) (addR64R64Effect 0x11ffeb 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[1087, 1026]
    (b_l11f8f6_24)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_23 : List UInt8 :=
  [0x4C, 0x8B, 0x64, 0x24, 0x48, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0x64, 0x24, 0x38, 0x49, 0x89, 0xD7,
    0x49, 0x89, 0xC3, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0xF7, 0x64, 0x24, 0x58, 0x49, 0x89, 0xD5,
    0x48, 0x89, 0xC5, 0x48, 0x8B, 0x04, 0x24, 0x4C, 0x8B, 0x44, 0x24, 0x30, 0x49, 0xF7, 0xE0, 0x83,
    0xE6, 0x0F, 0x49, 0x01, 0xCB, 0x4D, 0x11, 0xF7, 0x49, 0x01, 0xEB, 0x4D, 0x11, 0xEF, 0x4C, 0x01,
    0xD8, 0x49, 0x11, 0xD7, 0x48, 0x01, 0xD8] ++ bytes_l11f8f6_24

theorem code_l11f8f6_23 : ∀ x ∈ codeRange 0x11ffa7 bytes_l11f8f6_23, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ffa7 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_24

def b_l11f8f6_22 : Block Op Label signature Reg.count 1005 :=
  .letOp (n := 1005) (.out 0x11ff5f (atFlags StatusFlags.CF (adcR64M64Effect 0x11ff5f 3 (.sib 4 none 0 (.d8 0x78)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[1000, 4, 1003]
    (.letOp (n := 1006) (.exec 0x11ff5f (LoadPre 0x11ff5f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11ff5f + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11ff5f 3 (.sib 4 none 0 (.d8 0x78)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1000, 4, 1003]
    (.letOp (n := 1007) (.out 0x11ff64 (addR64R64Effect 0x11ff64 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[1002, 981]
    (.letOp (n := 1008) (.out 0x11ff64 (addR64R64Effect 0x11ff64 7 1) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 1] []) (.flag .CF)) #v[1002, 981]
    (.letOp (n := 1009) (.exec 0x11ff64 (fun s => s.RIP = 0x11ff64) (addR64R64Effect 0x11ff64 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[1002, 981]
    (.letOp (n := 1010) (.out 0x11ff67 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ff67 3 9)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1005, 979, 1008]
    (.letOp (n := 1011) (.exec 0x11ff67 (fun s => s.RIP = 0x11ff67) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ff67 3 9)) (Reg.operands [.gpr 3, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1005, 979, 1008]
    (.letOp (n := 1012) (.out 0x11ff6a (addR64R64Effect 0x11ff6a 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[1007, 987]
    (.letOp (n := 1013) (.out 0x11ff6a (addR64R64Effect 0x11ff6a 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[1007, 987]
    (.letOp (n := 1014) (.exec 0x11ff6a (fun s => s.RIP = 0x11ff6a) (addR64R64Effect 0x11ff6a 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[1007, 987]
    (.letOp (n := 1015) (.out 0x11ff6d (atFlags StatusFlags.CF (adcR64R64Effect 0x11ff6d 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1010, 988, 1013]
    (.letOp (n := 1016) (.exec 0x11ff6d (fun s => s.RIP = 0x11ff6d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ff6d 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1010, 988, 1013]
    (.letOp (n := 1017) (.out 0x11ff70 (addR64R64Effect 0x11ff70 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[1012, 934]
    (.letOp (n := 1018) (.out 0x11ff70 (addR64R64Effect 0x11ff70 7 14) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 14] []) (.flag .CF)) #v[1012, 934]
    (.letOp (n := 1019) (.exec 0x11ff70 (fun s => s.RIP = 0x11ff70) (addR64R64Effect 0x11ff70 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[1012, 934]
    (.letOp (n := 1020) (.out 0x11ff73 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ff73 3 6)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1015, 990, 1018]
    (.letOp (n := 1021) (.exec 0x11ff73 (fun s => s.RIP = 0x11ff73) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ff73 3 6)) (Reg.operands [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1015, 990, 1018]
    (.letOp (n := 1022) (.out 0x11ff76 (movR64R64Effect 0x11ff76 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[1020]
    (.letOp (n := 1023) (.exec 0x11ff76 (fun s => s.RIP = 0x11ff76) (movR64R64Effect 0x11ff76 9 3) (Reg.operands [.gpr 3] [])) #v[1020]
    (.letOp (n := 1024) (.out 0x11ff79 (shrR64Effect 0x11ff79 4 9 52) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[1022]
    (.letOp (n := 1025) (.exec 0x11ff79 (fun s => s.RIP = 0x11ff79) (shrR64Effect 0x11ff79 4 9 52) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1022]
    (.letOp (n := 1026) (.out 0x11ff7d (shldR64R64Effect 0x11ff7d 5 3 7 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1020, 1017]
    (.letOp (n := 1027) (.exec 0x11ff7d (fun s => s.RIP = 0x11ff7d) (shldR64R64Effect 0x11ff7d 5 3 7 12) (Reg.operands [.gpr 3, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1020, 1017]
    (.letOp (n := 1028) (.out 0x11ff82 (movR64R64Effect 0x11ff82 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[936]
    (.letOp (n := 1029) (.exec 0x11ff82 (fun s => s.RIP = 0x11ff82) (movR64R64Effect 0x11ff82 0 13) (Reg.operands [.gpr 13] [])) #v[936]
    (.letOp (n := 1030) (.out 0x11ff85 (mulR64Effect 0x11ff85 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[977, 1028]
    (.letOp (n := 1031) (.out 0x11ff85 (mulR64Effect 0x11ff85 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[977, 1028]
    (.letOp (n := 1032) (.exec 0x11ff85 (fun s => s.RIP = 0x11ff85) (mulR64Effect 0x11ff85 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[977, 1028]
    (.letOp (n := 1033) (.exec 0x11ff88 (StorePre 0x11ff88 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11ff88 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ff88 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1031, 4]
    (.letOp (n := 1034) (.exec 0x11ff8d (StorePre 0x11ff8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ff8d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ff8d 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1030, 4]
    (.letOp (n := 1035) (.out 0x11ff92 (movR64R64Effect 0x11ff92 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[945]
    (.letOp (n := 1036) (.exec 0x11ff92 (fun s => s.RIP = 0x11ff92) (movR64R64Effect 0x11ff92 0 12) (Reg.operands [.gpr 12] [])) #v[945]
    (.letOp (n := 1037) (.out 0x11ff95 (mulM64Effect 0x11ff95 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1035, 4]
    (.letOp (n := 1038) (.out 0x11ff95 (mulM64Effect 0x11ff95 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1035, 4]
    (.letOp (n := 1039) (.exec 0x11ff95 (LoadPre 0x11ff95 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11ff95 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11ff95 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1035, 4]
    (.letOp (n := 1040) (.out 0x11ff9a (movR64R64Effect 0x11ff9a 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1037]
    (.letOp (n := 1041) (.exec 0x11ff9a (fun s => s.RIP = 0x11ff9a) (movR64R64Effect 0x11ff9a 1 0) (Reg.operands [.gpr 0] [])) #v[1037]
    (.letOp (n := 1042) (.out 0x11ff9d (movR64R64Effect 0x11ff9d 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[1038]
    (.letOp (n := 1043) (.exec 0x11ff9d (fun s => s.RIP = 0x11ff9d) (movR64R64Effect 0x11ff9d 14 2) (Reg.operands [.gpr 2] [])) #v[1038]
    (.letOp (n := 1044) (.out 0x11ffa0 (movR64R64Effect 0x11ffa0 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[1017]
    (.letOp (n := 1045) (.exec 0x11ffa0 (fun s => s.RIP = 0x11ffa0) (movR64R64Effect 0x11ffa0 6 7) (Reg.operands [.gpr 7] [])) #v[1017]
    (.letOp (n := 1046) (.out 0x11ffa3 (shrR64Effect 0x11ffa3 4 6 48) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1044]
    (.letOp (n := 1047) (.exec 0x11ffa3 (fun s => s.RIP = 0x11ffa3) (shrR64Effect 0x11ffa3 4 6 48) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1044]
    (b_l11f8f6_23)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_22 : List UInt8 :=
  [0x48, 0x13, 0x5C, 0x24, 0x78, 0x48, 0x01, 0xCF, 0x4C, 0x11, 0xCB, 0x48, 0x01, 0xC7, 0x48, 0x11,
    0xD3, 0x4C, 0x01, 0xF7, 0x48, 0x11, 0xF3, 0x49, 0x89, 0xD9, 0x49, 0xC1, 0xE9, 0x34, 0x48, 0x0F,
    0xA4, 0xFB, 0x0C, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0x54, 0x24, 0x40, 0x48, 0x89,
    0x44, 0x24, 0x08, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0x64, 0x24, 0x20, 0x48, 0x89, 0xC1, 0x49, 0x89,
    0xD6, 0x48, 0x89, 0xFE, 0x48, 0xC1, 0xEE, 0x30] ++ bytes_l11f8f6_23

theorem code_l11f8f6_22 : ∀ x ∈ codeRange 0x11ff5f bytes_l11f8f6_22, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ff5f 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_23

def b_l11f8f6_21 : Block Op Label signature Reg.count 961 :=
  .letOp (n := 961) (.exec 0x11ff0e (StorePre 0x11ff0e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11ff0e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ff0e 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[959, 4]
    (.letOp (n := 962) (.out 0x11ff13 (movR64R64Effect 0x11ff13 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[958]
    (.letOp (n := 963) (.exec 0x11ff13 (fun s => s.RIP = 0x11ff13) (movR64R64Effect 0x11ff13 5 0) (Reg.operands [.gpr 0] [])) #v[958]
    (.letOp (n := 964) (.out 0x11ff16 (movR64M64Effect 0x11ff16 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 965) (.exec 0x11ff16 (LoadPre 0x11ff16 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11ff16 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ff16 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 966) (.out 0x11ff1b (mulR64Effect 0x11ff1b 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[877, 964]
    (.letOp (n := 967) (.out 0x11ff1b (mulR64Effect 0x11ff1b 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[877, 964]
    (.letOp (n := 968) (.exec 0x11ff1b (fun s => s.RIP = 0x11ff1b) (mulR64Effect 0x11ff1b 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[877, 964]
    (.letOp (n := 969) (.exec 0x11ff1e (StorePre 0x11ff1e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11ff1e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ff1e 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[967, 4]
    (.letOp (n := 970) (.out 0x11ff23 (movR64R64Effect 0x11ff23 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[966]
    (.letOp (n := 971) (.exec 0x11ff23 (fun s => s.RIP = 0x11ff23) (movR64R64Effect 0x11ff23 8 0) (Reg.operands [.gpr 0] [])) #v[966]
    (.letOp (n := 972) (.out 0x11ff26 (movR64M64Effect 0x11ff26 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 973) (.exec 0x11ff26 (LoadPre 0x11ff26 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11ff26 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11ff26 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 974) (.out 0x11ff2a (mulR64Effect 0x11ff2a 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[893, 972]
    (.letOp (n := 975) (.out 0x11ff2a (mulR64Effect 0x11ff2a 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[893, 972]
    (.letOp (n := 976) (.exec 0x11ff2a (fun s => s.RIP = 0x11ff2a) (mulR64Effect 0x11ff2a 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[893, 972]
    (.letOp (n := 977) (.out 0x11ff2d (movR64R64Effect 0x11ff2d 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 1] []) (.reg (.gpr 15))) #v[893]
    (.letOp (n := 978) (.exec 0x11ff2d (fun s => s.RIP = 0x11ff2d) (movR64R64Effect 0x11ff2d 15 1) (Reg.operands [.gpr 1] [])) #v[893]
    (.letOp (n := 979) (.out 0x11ff30 (movR64R64Effect 0x11ff30 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[975]
    (.letOp (n := 980) (.exec 0x11ff30 (fun s => s.RIP = 0x11ff30) (movR64R64Effect 0x11ff30 9 2) (Reg.operands [.gpr 2] [])) #v[975]
    (.letOp (n := 981) (.out 0x11ff33 (movR64R64Effect 0x11ff33 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[974]
    (.letOp (n := 982) (.exec 0x11ff33 (fun s => s.RIP = 0x11ff33) (movR64R64Effect 0x11ff33 1 0) (Reg.operands [.gpr 0] [])) #v[974]
    (.letOp (n := 983) (.out 0x11ff36 (movR64R64Effect 0x11ff36 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[916]
    (.letOp (n := 984) (.exec 0x11ff36 (fun s => s.RIP = 0x11ff36) (movR64R64Effect 0x11ff36 0 11) (Reg.operands [.gpr 11] [])) #v[916]
    (.letOp (n := 985) (.out 0x11ff39 (movR64Imm64Effect 0x11ff39 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 986) (.exec 0x11ff39 (fun s => s.RIP = 0x11ff39) (movR64Imm64Effect 0x11ff39 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 987) (.out 0x11ff43 (mulR64Effect 0x11ff43 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[985, 983]
    (.letOp (n := 988) (.out 0x11ff43 (mulR64Effect 0x11ff43 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[985, 983]
    (.letOp (n := 989) (.exec 0x11ff43 (fun s => s.RIP = 0x11ff43) (mulR64Effect 0x11ff43 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[985, 983]
    (.letOp (n := 990) (.out 0x11ff46 (shrR64Effect 0x11ff46 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[932]
    (.letOp (n := 991) (.exec 0x11ff46 (fun s => s.RIP = 0x11ff46) (shrR64Effect 0x11ff46 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[932]
    (.letOp (n := 992) (.out 0x11ff4a (addR64M64Effect 0x11ff4a 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[954, 4]
    (.letOp (n := 993) (.out 0x11ff4a (addR64M64Effect 0x11ff4a 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 4] []) (.flag .CF)) #v[954, 4]
    (.letOp (n := 994) (.exec 0x11ff4a (LoadPre 0x11ff4a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ff4a + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11ff4a 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[954, 4]
    (.letOp (n := 995) (.out 0x11ff4f (atFlags StatusFlags.CF (adcR64M64Effect 0x11ff4f 3 (.sib 4 none 0 (.d8 0x40)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[952, 4, 993]
    (.letOp (n := 996) (.exec 0x11ff4f (LoadPre 0x11ff4f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11ff4f + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11ff4f 3 (.sib 4 none 0 (.d8 0x40)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[952, 4, 993]
    (.letOp (n := 997) (.out 0x11ff54 (addR64R64Effect 0x11ff54 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[992, 962]
    (.letOp (n := 998) (.out 0x11ff54 (addR64R64Effect 0x11ff54 7 5) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 5] []) (.flag .CF)) #v[992, 962]
    (.letOp (n := 999) (.exec 0x11ff54 (fun s => s.RIP = 0x11ff54) (addR64R64Effect 0x11ff54 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[992, 962]
    (.letOp (n := 1000) (.out 0x11ff57 (atFlags StatusFlags.CF (adcR64M64Effect 0x11ff57 3 (.sib 4 none 0 (.d8 0x60)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[995, 4, 998]
    (.letOp (n := 1001) (.exec 0x11ff57 (LoadPre 0x11ff57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11ff57 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11ff57 3 (.sib 4 none 0 (.d8 0x60)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[995, 4, 998]
    (.letOp (n := 1002) (.out 0x11ff5c (addR64R64Effect 0x11ff5c 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[997, 970]
    (.letOp (n := 1003) (.out 0x11ff5c (addR64R64Effect 0x11ff5c 7 8) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 8] []) (.flag .CF)) #v[997, 970]
    (.letOp (n := 1004) (.exec 0x11ff5c (fun s => s.RIP = 0x11ff5c) (addR64R64Effect 0x11ff5c 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[997, 970]
    (b_l11f8f6_22))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_21 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x60, 0x48, 0x89, 0xC5, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x49, 0xF7, 0xE1,
    0x48, 0x89, 0x54, 0x24, 0x78, 0x49, 0x89, 0xC0, 0x48, 0x8B, 0x04, 0x24, 0x48, 0xF7, 0xE1, 0x49,
    0x89, 0xCF, 0x49, 0x89, 0xD1, 0x48, 0x89, 0xC1, 0x4C, 0x89, 0xD8, 0x48, 0xBA, 0x10, 0x3D, 0x00,
    0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0xC1, 0xEE, 0x34, 0x48, 0x03, 0x7C, 0x24,
    0x08, 0x48, 0x13, 0x5C, 0x24, 0x40, 0x48, 0x01, 0xEF, 0x48, 0x13, 0x5C, 0x24, 0x60, 0x4C, 0x01,
    0xC7] ++ bytes_l11f8f6_22

theorem code_l11f8f6_21 : ∀ x ∈ codeRange 0x11ff0e bytes_l11f8f6_21, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ff0e 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_22

def b_l11f8f6_20 : Block Op Label signature Reg.count 918 :=
  .letOp (n := 918) (.out 0x11fec6 (andR64R64Effect 0x11fec6 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[911, 848]
    (.letOp (n := 919) (.exec 0x11fec6 (fun s => s.RIP = 0x11fec6) (andR64R64Effect 0x11fec6 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[911, 848]
    (.letOp (n := 920) (.out 0x11fec9 (mulR64Effect 0x11fec9 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[807, 918]
    (.letOp (n := 921) (.out 0x11fec9 (mulR64Effect 0x11fec9 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[807, 918]
    (.letOp (n := 922) (.exec 0x11fec9 (fun s => s.RIP = 0x11fec9) (mulR64Effect 0x11fec9 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[807, 918]
    (.letOp (n := 923) (.out 0x11fecc (movR64R64Effect 0x11fecc 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[921]
    (.letOp (n := 924) (.exec 0x11fecc (fun s => s.RIP = 0x11fecc) (movR64R64Effect 0x11fecc 14 2) (Reg.operands [.gpr 2] [])) #v[921]
    (.letOp (n := 925) (.out 0x11fecf (movR64R64Effect 0x11fecf 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[920]
    (.letOp (n := 926) (.exec 0x11fecf (fun s => s.RIP = 0x11fecf) (movR64R64Effect 0x11fecf 10 0) (Reg.operands [.gpr 0] [])) #v[920]
    (.letOp (n := 927) (.out 0x11fed2 (addR64R64Effect 0x11fed2 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15] []) (.reg (.gpr 10))) #v[925, 902]
    (.letOp (n := 928) (.out 0x11fed2 (addR64R64Effect 0x11fed2 10 15) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 15] []) (.flag .CF)) #v[925, 902]
    (.letOp (n := 929) (.exec 0x11fed2 (fun s => s.RIP = 0x11fed2) (addR64R64Effect 0x11fed2 10 15) (Reg.operands [.gpr 10, .gpr 15] [])) #v[925, 902]
    (.letOp (n := 930) (.out 0x11fed5 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fed5 14 3)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[923, 905, 928]
    (.letOp (n := 931) (.exec 0x11fed5 (fun s => s.RIP = 0x11fed5) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fed5 14 3)) (Reg.operands [.gpr 14, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[923, 905, 928]
    (.letOp (n := 932) (.out 0x11fed8 (movR64R64Effect 0x11fed8 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[930]
    (.letOp (n := 933) (.exec 0x11fed8 (fun s => s.RIP = 0x11fed8) (movR64R64Effect 0x11fed8 6 14) (Reg.operands [.gpr 14] [])) #v[930]
    (.letOp (n := 934) (.out 0x11fedb (shldR64R64Effect 0x11fedb 5 14 10 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[930, 927]
    (.letOp (n := 935) (.exec 0x11fedb (fun s => s.RIP = 0x11fedb) (shldR64R64Effect 0x11fedb 5 14 10 12) (Reg.operands [.gpr 14, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[930, 927]
    (.letOp (n := 936) (.out 0x11fee0 (movR64M64Effect 0x11fee0 13 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 937) (.exec 0x11fee0 (LoadPre 0x11fee0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11fee0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fee0 13 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 938) (.out 0x11fee5 (movR64R64Effect 0x11fee5 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[936]
    (.letOp (n := 939) (.exec 0x11fee5 (fun s => s.RIP = 0x11fee5) (movR64R64Effect 0x11fee5 0 13) (Reg.operands [.gpr 13] [])) #v[936]
    (.letOp (n := 940) (.out 0x11fee8 (mulR64Effect 0x11fee8 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[909, 938]
    (.letOp (n := 941) (.out 0x11fee8 (mulR64Effect 0x11fee8 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[909, 938]
    (.letOp (n := 942) (.exec 0x11fee8 (fun s => s.RIP = 0x11fee8) (mulR64Effect 0x11fee8 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[909, 938]
    (.letOp (n := 943) (.exec 0x11feeb (StorePre 0x11feeb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11feeb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11feeb 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[941, 4]
    (.letOp (n := 944) (.exec 0x11fef0 (StorePre 0x11fef0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11fef0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11fef0 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[940, 4]
    (.letOp (n := 945) (.out 0x11fef5 (movR64M64Effect 0x11fef5 12 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 946) (.exec 0x11fef5 (LoadPre 0x11fef5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11fef5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fef5 12 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 947) (.out 0x11fefa (movR64R64Effect 0x11fefa 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[945]
    (.letOp (n := 948) (.exec 0x11fefa (fun s => s.RIP = 0x11fefa) (movR64R64Effect 0x11fefa 0 12) (Reg.operands [.gpr 12] [])) #v[945]
    (.letOp (n := 949) (.out 0x11fefd (mulR64Effect 0x11fefd 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[850, 947]
    (.letOp (n := 950) (.out 0x11fefd (mulR64Effect 0x11fefd 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[850, 947]
    (.letOp (n := 951) (.exec 0x11fefd (fun s => s.RIP = 0x11fefd) (mulR64Effect 0x11fefd 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[850, 947]
    (.letOp (n := 952) (.out 0x11ff00 (movR64R64Effect 0x11ff00 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[950]
    (.letOp (n := 953) (.exec 0x11ff00 (fun s => s.RIP = 0x11ff00) (movR64R64Effect 0x11ff00 3 2) (Reg.operands [.gpr 2] [])) #v[950]
    (.letOp (n := 954) (.out 0x11ff03 (movR64R64Effect 0x11ff03 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[949]
    (.letOp (n := 955) (.exec 0x11ff03 (fun s => s.RIP = 0x11ff03) (movR64R64Effect 0x11ff03 7 0) (Reg.operands [.gpr 0] [])) #v[949]
    (.letOp (n := 956) (.out 0x11ff06 (movR64M64Effect 0x11ff06 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 957) (.exec 0x11ff06 (LoadPre 0x11ff06 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11ff06 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ff06 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 958) (.out 0x11ff0b (mulR64Effect 0x11ff0b 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[864, 956]
    (.letOp (n := 959) (.out 0x11ff0b (mulR64Effect 0x11ff0b 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[864, 956]
    (.letOp (n := 960) (.exec 0x11ff0b (fun s => s.RIP = 0x11ff0b) (mulR64Effect 0x11ff0b 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[864, 956]
    (b_l11f8f6_21)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_20 : List UInt8 :=
  [0x4C, 0x21, 0xD0, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC2, 0x4D, 0x01, 0xFA, 0x49,
    0x11, 0xDE, 0x4C, 0x89, 0xF6, 0x4D, 0x0F, 0xA4, 0xD6, 0x0C, 0x4C, 0x8B, 0x6C, 0x24, 0x18, 0x4C,
    0x89, 0xE8, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0x54, 0x24, 0x40, 0x48, 0x89, 0x44, 0x24, 0x08, 0x4C,
    0x8B, 0x64, 0x24, 0x10, 0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0xD3, 0x48, 0x89, 0xC7,
    0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0xF7, 0xE5] ++ bytes_l11f8f6_21

theorem code_l11f8f6_20 : ∀ x ∈ codeRange 0x11fec6 bytes_l11f8f6_20, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fec6 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_21

def b_l11f8f6_19 : Block Op Label signature Reg.count 873 :=
  .letOp (n := 873) (.out 0x11fe82 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fe82 11 6)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[866, 855, 871]
    (.letOp (n := 874) (.exec 0x11fe82 (fun s => s.RIP = 0x11fe82) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fe82 11 6)) (Reg.operands [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[866, 855, 871]
    (.letOp (n := 875) (.out 0x11fe85 (movR64R64Effect 0x11fe85 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[842]
    (.letOp (n := 876) (.exec 0x11fe85 (fun s => s.RIP = 0x11fe85) (movR64R64Effect 0x11fe85 0 15) (Reg.operands [.gpr 15] [])) #v[842]
    (.letOp (n := 877) (.out 0x11fe88 (movR64M64Effect 0x11fe88 9 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 878) (.exec 0x11fe88 (LoadPre 0x11fe88 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11fe88 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fe88 9 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 879) (.out 0x11fe8d (mulR64Effect 0x11fe8d 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[877, 875]
    (.letOp (n := 880) (.out 0x11fe8d (mulR64Effect 0x11fe8d 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[877, 875]
    (.letOp (n := 881) (.exec 0x11fe8d (fun s => s.RIP = 0x11fe8d) (mulR64Effect 0x11fe8d 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[877, 875]
    (.letOp (n := 882) (.out 0x11fe90 (movR64R64Effect 0x11fe90 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[880]
    (.letOp (n := 883) (.exec 0x11fe90 (fun s => s.RIP = 0x11fe90) (movR64R64Effect 0x11fe90 6 2) (Reg.operands [.gpr 2] [])) #v[880]
    (.letOp (n := 884) (.out 0x11fe93 (movR64R64Effect 0x11fe93 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[879]
    (.letOp (n := 885) (.exec 0x11fe93 (fun s => s.RIP = 0x11fe93) (movR64R64Effect 0x11fe93 7 0) (Reg.operands [.gpr 0] [])) #v[879]
    (.letOp (n := 886) (.out 0x11fe96 (addR64R64Effect 0x11fe96 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[884, 870]
    (.letOp (n := 887) (.out 0x11fe96 (addR64R64Effect 0x11fe96 7 3) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 3] []) (.flag .CF)) #v[884, 870]
    (.letOp (n := 888) (.exec 0x11fe96 (fun s => s.RIP = 0x11fe96) (addR64R64Effect 0x11fe96 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[884, 870]
    (.letOp (n := 889) (.out 0x11fe99 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fe99 6 11)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[882, 873, 887]
    (.letOp (n := 890) (.exec 0x11fe99 (fun s => s.RIP = 0x11fe99) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fe99 6 11)) (Reg.operands [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[882, 873, 887]
    (.letOp (n := 891) (.out 0x11fe9c (movR64R64Effect 0x11fe9c 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[845]
    (.letOp (n := 892) (.exec 0x11fe9c (fun s => s.RIP = 0x11fe9c) (movR64R64Effect 0x11fe9c 0 1) (Reg.operands [.gpr 1] [])) #v[845]
    (.letOp (n := 893) (.out 0x11fe9f (movR64M64Effect 0x11fe9f 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 894) (.exec 0x11fe9f (LoadPre 0x11fe9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11fe9f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fe9f 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 895) (.out 0x11fea4 (mulR64Effect 0x11fea4 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[893, 891]
    (.letOp (n := 896) (.out 0x11fea4 (mulR64Effect 0x11fea4 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[893, 891]
    (.letOp (n := 897) (.exec 0x11fea4 (fun s => s.RIP = 0x11fea4) (mulR64Effect 0x11fea4 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[893, 891]
    (.letOp (n := 898) (.out 0x11fea7 (movR64R64Effect 0x11fea7 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[896]
    (.letOp (n := 899) (.exec 0x11fea7 (fun s => s.RIP = 0x11fea7) (movR64R64Effect 0x11fea7 3 2) (Reg.operands [.gpr 2] [])) #v[896]
    (.letOp (n := 900) (.out 0x11feaa (movR64R64Effect 0x11feaa 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[895]
    (.letOp (n := 901) (.exec 0x11feaa (fun s => s.RIP = 0x11feaa) (movR64R64Effect 0x11feaa 15 0) (Reg.operands [.gpr 0] [])) #v[895]
    (.letOp (n := 902) (.out 0x11fead (addR64R64Effect 0x11fead 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[900, 886]
    (.letOp (n := 903) (.out 0x11fead (addR64R64Effect 0x11fead 15 7) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 7] []) (.flag .CF)) #v[900, 886]
    (.letOp (n := 904) (.exec 0x11fead (fun s => s.RIP = 0x11fead) (addR64R64Effect 0x11fead 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[900, 886]
    (.letOp (n := 905) (.out 0x11feb0 (atFlags StatusFlags.CF (adcR64R64Effect 0x11feb0 3 6)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[898, 889, 903]
    (.letOp (n := 906) (.exec 0x11feb0 (fun s => s.RIP = 0x11feb0) (atFlags StatusFlags.CF (adcR64R64Effect 0x11feb0 3 6)) (Reg.operands [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[898, 889, 903]
    (.letOp (n := 907) (.out 0x11feb3 (movR64R64Effect 0x11feb3 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[829]
    (.letOp (n := 908) (.exec 0x11feb3 (fun s => s.RIP = 0x11feb3) (movR64R64Effect 0x11feb3 0 12) (Reg.operands [.gpr 12] [])) #v[829]
    (.letOp (n := 909) (.out 0x11feb6 (movR64M64Effect 0x11feb6 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 910) (.exec 0x11feb6 (LoadPre 0x11feb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11feb6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11feb6 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 911) (.out 0x11febb (mulR64Effect 0x11febb 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[909, 907]
    (.letOp (n := 912) (.out 0x11febb (mulR64Effect 0x11febb 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[909, 907]
    (.letOp (n := 913) (.exec 0x11febb (fun s => s.RIP = 0x11febb) (mulR64Effect 0x11febb 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[909, 907]
    (.letOp (n := 914) (.out 0x11febe (movR64R64Effect 0x11febe 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[912]
    (.letOp (n := 915) (.exec 0x11febe (fun s => s.RIP = 0x11febe) (movR64R64Effect 0x11febe 11 2) (Reg.operands [.gpr 2] [])) #v[912]
    (.letOp (n := 916) (.out 0x11fec1 (shldR64R64Effect 0x11fec1 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[914, 911]
    (.letOp (n := 917) (.exec 0x11fec1 (fun s => s.RIP = 0x11fec1) (shldR64R64Effect 0x11fec1 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[914, 911]
    (b_l11f8f6_20)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_19 : List UInt8 :=
  [0x49, 0x11, 0xF3, 0x4C, 0x89, 0xF8, 0x4C, 0x8B, 0x4C, 0x24, 0x30, 0x49, 0xF7, 0xE1, 0x48, 0x89,
    0xD6, 0x48, 0x89, 0xC7, 0x48, 0x01, 0xDF, 0x4C, 0x11, 0xDE, 0x48, 0x89, 0xC8, 0x48, 0x8B, 0x4C,
    0x24, 0x50, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC7, 0x49, 0x01, 0xFF, 0x48, 0x11,
    0xF3, 0x4C, 0x89, 0xE0, 0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0xF7, 0xE7, 0x49, 0x89, 0xD3, 0x49,
    0x0F, 0xA4, 0xC3, 0x0C] ++ bytes_l11f8f6_20

theorem code_l11f8f6_19 : ∀ x ∈ codeRange 0x11fe82 bytes_l11f8f6_19, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fe82 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_20

def b_l11f8f6_18 : Block Op Label signature Reg.count 834 :=
  .letOp (n := 834) (.out 0x11fe3c (andR64R64Effect 0x11fe3c 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[832, 757]
    (.letOp (n := 835) (.exec 0x11fe3c (fun s => s.RIP = 0x11fe3c) (andR64R64Effect 0x11fe3c 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[832, 757]
    (.letOp (n := 836) (.exec 0x11fe3f (StorePre 0x11fe3f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11fe3f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11fe3f 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[834, 4]
    (.letOp (n := 837) (.out 0x11fe44 (movR64R64Effect 0x11fe44 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 10] []) (.reg (.gpr 5))) #v[715]
    (.letOp (n := 838) (.exec 0x11fe44 (fun s => s.RIP = 0x11fe44) (movR64R64Effect 0x11fe44 5 10) (Reg.operands [.gpr 10] [])) #v[715]
    (.letOp (n := 839) (.out 0x11fe47 (andR64R64Effect 0x11fe47 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9] []) (.reg (.gpr 5))) #v[837, 699]
    (.letOp (n := 840) (.exec 0x11fe47 (fun s => s.RIP = 0x11fe47) (andR64R64Effect 0x11fe47 5 9) (Reg.operands [.gpr 5, .gpr 9] [])) #v[837, 699]
    (.letOp (n := 841) (.exec 0x11fe4a (StorePre 0x11fe4a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11fe4a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11fe4a 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[839, 4]
    (.letOp (n := 842) (.out 0x11fe4f (andR64R64Effect 0x11fe4f 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9] []) (.reg (.gpr 15))) #v[784, 699]
    (.letOp (n := 843) (.exec 0x11fe4f (fun s => s.RIP = 0x11fe4f) (andR64R64Effect 0x11fe4f 15 9) (Reg.operands [.gpr 15, .gpr 9] [])) #v[784, 699]
    (.letOp (n := 844) (.exec 0x11fe52 (StorePre 0x11fe52 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11fe52 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11fe52 15 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[842, 4]
    (.letOp (n := 845) (.out 0x11fe57 (andR64R64Effect 0x11fe57 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[816, 699]
    (.letOp (n := 846) (.exec 0x11fe57 (fun s => s.RIP = 0x11fe57) (andR64R64Effect 0x11fe57 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[816, 699]
    (.letOp (n := 847) (.exec 0x11fe5a (StorePre 0x11fe5a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11fe5a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11fe5a 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[845, 4]
    (.letOp (n := 848) (.out 0x11fe5f (movR64R64Effect 0x11fe5f 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[699]
    (.letOp (n := 849) (.exec 0x11fe5f (fun s => s.RIP = 0x11fe5f) (movR64R64Effect 0x11fe5f 10 9) (Reg.operands [.gpr 9] [])) #v[699]
    (.letOp (n := 850) (.out 0x11fe62 (movR64M64Effect 0x11fe62 8 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 851) (.exec 0x11fe62 (LoadPre 0x11fe62 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11fe62 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fe62 8 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 852) (.out 0x11fe67 (mulR64Effect 0x11fe67 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[850, 834]
    (.letOp (n := 853) (.out 0x11fe67 (mulR64Effect 0x11fe67 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[850, 834]
    (.letOp (n := 854) (.exec 0x11fe67 (fun s => s.RIP = 0x11fe67) (mulR64Effect 0x11fe67 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[850, 834]
    (.letOp (n := 855) (.out 0x11fe6a (movR64R64Effect 0x11fe6a 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[853]
    (.letOp (n := 856) (.exec 0x11fe6a (fun s => s.RIP = 0x11fe6a) (movR64R64Effect 0x11fe6a 6 2) (Reg.operands [.gpr 2] [])) #v[853]
    (.letOp (n := 857) (.out 0x11fe6d (movR64R64Effect 0x11fe6d 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[852]
    (.letOp (n := 858) (.exec 0x11fe6d (fun s => s.RIP = 0x11fe6d) (movR64R64Effect 0x11fe6d 7 0) (Reg.operands [.gpr 0] [])) #v[852]
    (.letOp (n := 859) (.out 0x11fe70 (movR64R64Effect 0x11fe70 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[839]
    (.letOp (n := 860) (.exec 0x11fe70 (fun s => s.RIP = 0x11fe70) (movR64R64Effect 0x11fe70 0 5) (Reg.operands [.gpr 5] [])) #v[839]
    (.letOp (n := 861) (.out 0x11fe73 (mulR64Effect 0x11fe73 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[468, 859]
    (.letOp (n := 862) (.out 0x11fe73 (mulR64Effect 0x11fe73 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[468, 859]
    (.letOp (n := 863) (.exec 0x11fe73 (fun s => s.RIP = 0x11fe73) (mulR64Effect 0x11fe73 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[468, 859]
    (.letOp (n := 864) (.out 0x11fe76 (movR64R64Effect 0x11fe76 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 13] []) (.reg (.gpr 5))) #v[468]
    (.letOp (n := 865) (.exec 0x11fe76 (fun s => s.RIP = 0x11fe76) (movR64R64Effect 0x11fe76 5 13) (Reg.operands [.gpr 13] [])) #v[468]
    (.letOp (n := 866) (.out 0x11fe79 (movR64R64Effect 0x11fe79 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[862]
    (.letOp (n := 867) (.exec 0x11fe79 (fun s => s.RIP = 0x11fe79) (movR64R64Effect 0x11fe79 11 2) (Reg.operands [.gpr 2] [])) #v[862]
    (.letOp (n := 868) (.out 0x11fe7c (movR64R64Effect 0x11fe7c 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[861]
    (.letOp (n := 869) (.exec 0x11fe7c (fun s => s.RIP = 0x11fe7c) (movR64R64Effect 0x11fe7c 3 0) (Reg.operands [.gpr 0] [])) #v[861]
    (.letOp (n := 870) (.out 0x11fe7f (addR64R64Effect 0x11fe7f 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[868, 857]
    (.letOp (n := 871) (.out 0x11fe7f (addR64R64Effect 0x11fe7f 3 7) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 7] []) (.flag .CF)) #v[868, 857]
    (.letOp (n := 872) (.exec 0x11fe7f (fun s => s.RIP = 0x11fe7f) (addR64R64Effect 0x11fe7f 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[868, 857]
    (b_l11f8f6_19)))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_18 : List UInt8 :=
  [0x48, 0x21, 0xE8, 0x48, 0x89, 0x44, 0x24, 0x18, 0x4C, 0x89, 0xD5, 0x4C, 0x21, 0xCD, 0x48, 0x89,
    0x6C, 0x24, 0x10, 0x4D, 0x21, 0xCF, 0x4C, 0x89, 0x7C, 0x24, 0x48, 0x4C, 0x21, 0xC9, 0x48, 0x89,
    0x4C, 0x24, 0x28, 0x4D, 0x89, 0xCA, 0x4C, 0x8B, 0x44, 0x24, 0x38, 0x49, 0xF7, 0xE0, 0x48, 0x89,
    0xD6, 0x48, 0x89, 0xC7, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE5, 0x4C, 0x89, 0xED, 0x49, 0x89, 0xD3,
    0x48, 0x89, 0xC3, 0x48, 0x01, 0xFB] ++ bytes_l11f8f6_19

theorem code_l11f8f6_18 : ∀ x ∈ codeRange 0x11fe3c bytes_l11f8f6_18, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fe3c 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_19

def b_l11f8f6_17 : Block Op Label signature Reg.count 792 :=
  .letOp (n := 792) (.out 0x11fded (movR64M64Effect 0x11fded 8 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 793) (.exec 0x11fded (LoadPre 0x11fded (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11fded + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fded 8 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 794) (.out 0x11fdf2 (andR64R64Effect 0x11fdf2 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[792, 790]
    (.letOp (n := 795) (.exec 0x11fdf2 (fun s => s.RIP = 0x11fdf2) (andR64R64Effect 0x11fdf2 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[792, 790]
    (.letOp (n := 796) (.out 0x11fdf5 (movR64R64Effect 0x11fdf5 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[786]
    (.letOp (n := 797) (.exec 0x11fdf5 (fun s => s.RIP = 0x11fdf5) (movR64R64Effect 0x11fdf5 7 3) (Reg.operands [.gpr 3] [])) #v[786]
    (.letOp (n := 798) (.out 0x11fdf8 (shrR64Effect 0x11fdf8 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[796]
    (.letOp (n := 799) (.exec 0x11fdf8 (fun s => s.RIP = 0x11fdf8) (shrR64Effect 0x11fdf8 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[796]
    (.letOp (n := 800) (.out 0x11fdfc (shldR64R64Effect 0x11fdfc 5 3 15 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[786, 784]
    (.letOp (n := 801) (.exec 0x11fdfc (fun s => s.RIP = 0x11fdfc) (shldR64R64Effect 0x11fdfc 5 3 15 12) (Reg.operands [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[786, 784]
    (.letOp (n := 802) (.out 0x11fe01 (movR64R64Effect 0x11fe01 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[788]
    (.letOp (n := 803) (.exec 0x11fe01 (fun s => s.RIP = 0x11fe01) (movR64R64Effect 0x11fe01 0 1) (Reg.operands [.gpr 1] [])) #v[788]
    (.letOp (n := 804) (.out 0x11fe04 (mulR64Effect 0x11fe04 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[703, 802]
    (.letOp (n := 805) (.out 0x11fe04 (mulR64Effect 0x11fe04 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[703, 802]
    (.letOp (n := 806) (.exec 0x11fe04 (fun s => s.RIP = 0x11fe04) (mulR64Effect 0x11fe04 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[703, 802]
    (.letOp (n := 807) (.out 0x11fe07 (movR64R64Effect 0x11fe07 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[703]
    (.letOp (n := 808) (.exec 0x11fe07 (fun s => s.RIP = 0x11fe07) (movR64R64Effect 0x11fe07 14 6) (Reg.operands [.gpr 6] [])) #v[703]
    (.letOp (n := 809) (.out 0x11fe0a (movR64R64Effect 0x11fe0a 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[804]
    (.letOp (n := 810) (.exec 0x11fe0a (fun s => s.RIP = 0x11fe0a) (movR64R64Effect 0x11fe0a 1 0) (Reg.operands [.gpr 0] [])) #v[804]
    (.letOp (n := 811) (.out 0x11fe0d (addR64R64Effect 0x11fe0d 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[809, 794]
    (.letOp (n := 812) (.out 0x11fe0d (addR64R64Effect 0x11fe0d 1 8) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 8] []) (.flag .CF)) #v[809, 794]
    (.letOp (n := 813) (.exec 0x11fe0d (fun s => s.RIP = 0x11fe0d) (addR64R64Effect 0x11fe0d 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[809, 794]
    (.letOp (n := 814) (.out 0x11fe10 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11fe10 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[805, 812]
    (.letOp (n := 815) (.exec 0x11fe10 (fun s => s.RIP = 0x11fe10) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11fe10 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[805, 812]
    (.letOp (n := 816) (.out 0x11fe14 (addR64R64Effect 0x11fe14 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[811, 800]
    (.letOp (n := 817) (.out 0x11fe14 (addR64R64Effect 0x11fe14 1 3) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 3] []) (.flag .CF)) #v[811, 800]
    (.letOp (n := 818) (.exec 0x11fe14 (fun s => s.RIP = 0x11fe14) (addR64R64Effect 0x11fe14 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[811, 800]
    (.letOp (n := 819) (.out 0x11fe17 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fe17 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[798, 814, 817]
    (.letOp (n := 820) (.exec 0x11fe17 (fun s => s.RIP = 0x11fe17) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fe17 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[798, 814, 817]
    (.letOp (n := 821) (.out 0x11fe1a (shldR64R64Effect 0x11fe1a 5 7 1 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[819, 816]
    (.letOp (n := 822) (.exec 0x11fe1a (fun s => s.RIP = 0x11fe1a) (shldR64R64Effect 0x11fe1a 5 7 1 12) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[819, 816]
    (.letOp (n := 823) (.out 0x11fe1f (movR64Imm64Effect 0x11fe1f 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 824) (.exec 0x11fe1f (fun s => s.RIP = 0x11fe1f) (movR64Imm64Effect 0x11fe1f 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 825) (.out 0x11fe29 (movR64M64Effect 0x11fe29 12 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 826) (.exec 0x11fe29 (LoadPre 0x11fe29 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11fe29 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11fe29 12 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 827) (.out 0x11fe2d (andR64R64Effect 0x11fe2d 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[825, 823]
    (.letOp (n := 828) (.exec 0x11fe2d (fun s => s.RIP = 0x11fe2d) (andR64R64Effect 0x11fe2d 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[825, 823]
    (.letOp (n := 829) (.out 0x11fe30 (addR64R64Effect 0x11fe30 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 7] []) (.reg (.gpr 12))) #v[827, 821]
    (.letOp (n := 830) (.exec 0x11fe30 (fun s => s.RIP = 0x11fe30) (addR64R64Effect 0x11fe30 12 7) (Reg.operands [.gpr 12, .gpr 7] [])) #v[827, 821]
    (.letOp (n := 831) (.exec 0x11fe33 (StorePre 0x11fe33 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11fe33 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11fe33 12 (.sib 4 none 0 .none)) (Reg.operands [.gpr 12, .gpr 4] [])) #v[829, 4]
    (.letOp (n := 832) (.out 0x11fe37 (movR64M64Effect 0x11fe37 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 833) (.exec 0x11fe37 (LoadPre 0x11fe37 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11fe37 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fe37 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l11f8f6_18))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_17 : List UInt8 :=
  [0x4C, 0x8B, 0x44, 0x24, 0x28, 0x49, 0x21, 0xC0, 0x48, 0x89, 0xDF, 0x48, 0xC1, 0xEF, 0x34, 0x4C,
    0x0F, 0xA4, 0xFB, 0x0C, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0xE6, 0x49, 0x89, 0xF6, 0x48, 0x89, 0xC1,
    0x4C, 0x01, 0xC1, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x01, 0xD9, 0x48, 0x11, 0xD7, 0x48, 0x0F, 0xA4,
    0xCF, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x4C, 0x8B, 0x24, 0x24,
    0x49, 0x21, 0xC4, 0x49, 0x01, 0xFC, 0x4C, 0x89, 0x24, 0x24, 0x48, 0x8B, 0x44, 0x24, 0x18] ++ bytes_l11f8f6_18

theorem code_l11f8f6_17 : ∀ x ∈ codeRange 0x11fded bytes_l11f8f6_17, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fded 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_18

def b_l11f8f6_16 : Block Op Label signature Reg.count 746 :=
  .letOp (n := 746) (.out 0x11fda6 (movR64R64Effect 0x11fda6 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[743]
    (.letOp (n := 747) (.exec 0x11fda6 (fun s => s.RIP = 0x11fda6) (movR64R64Effect 0x11fda6 11 0) (Reg.operands [.gpr 0] [])) #v[743]
    (.letOp (n := 748) (.out 0x11fda9 (addR64R64Effect 0x11fda9 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[746, 722]
    (.letOp (n := 749) (.out 0x11fda9 (addR64R64Effect 0x11fda9 11 14) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 14] []) (.flag .CF)) #v[746, 722]
    (.letOp (n := 750) (.exec 0x11fda9 (fun s => s.RIP = 0x11fda9) (addR64R64Effect 0x11fda9 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[746, 722]
    (.letOp (n := 751) (.out 0x11fdac (atFlags StatusFlags.CF (adcR64R64Effect 0x11fdac 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[724, 744, 749]
    (.letOp (n := 752) (.exec 0x11fdac (fun s => s.RIP = 0x11fdac) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fdac 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[724, 744, 749]
    (.letOp (n := 753) (.out 0x11fdaf (movR64R64Effect 0x11fdaf 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[748]
    (.letOp (n := 754) (.exec 0x11fdaf (fun s => s.RIP = 0x11fdaf) (movR64R64Effect 0x11fdaf 0 11) (Reg.operands [.gpr 11] [])) #v[748]
    (.letOp (n := 755) (.out 0x11fdb2 (andR64R64Effect 0x11fdb2 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[753, 699]
    (.letOp (n := 756) (.exec 0x11fdb2 (fun s => s.RIP = 0x11fdb2) (andR64R64Effect 0x11fdb2 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[753, 699]
    (.letOp (n := 757) (.out 0x11fdb5 (movR64R64Effect 0x11fdb5 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[699]
    (.letOp (n := 758) (.exec 0x11fdb5 (fun s => s.RIP = 0x11fdb5) (movR64R64Effect 0x11fdb5 5 9) (Reg.operands [.gpr 9] [])) #v[699]
    (.letOp (n := 759) (.out 0x11fdb8 (mulR64Effect 0x11fdb8 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[703, 755]
    (.letOp (n := 760) (.out 0x11fdb8 (mulR64Effect 0x11fdb8 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[703, 755]
    (.letOp (n := 761) (.exec 0x11fdb8 (fun s => s.RIP = 0x11fdb8) (mulR64Effect 0x11fdb8 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[703, 755]
    (.letOp (n := 762) (.out 0x11fdbb (movR64R64Effect 0x11fdbb 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[760]
    (.letOp (n := 763) (.exec 0x11fdbb (fun s => s.RIP = 0x11fdbb) (movR64R64Effect 0x11fdbb 14 2) (Reg.operands [.gpr 2] [])) #v[760]
    (.letOp (n := 764) (.out 0x11fdbe (movR64R64Effect 0x11fdbe 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[759]
    (.letOp (n := 765) (.exec 0x11fdbe (fun s => s.RIP = 0x11fdbe) (movR64R64Effect 0x11fdbe 12 0) (Reg.operands [.gpr 0] [])) #v[759]
    (.letOp (n := 766) (.out 0x11fdc1 (movR64M64Effect 0x11fdc1 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 767) (.exec 0x11fdc1 (LoadPre 0x11fdc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11fdc1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fdc1 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 768) (.out 0x11fdc6 (mulR64Effect 0x11fdc6 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[468, 766]
    (.letOp (n := 769) (.out 0x11fdc6 (mulR64Effect 0x11fdc6 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[468, 766]
    (.letOp (n := 770) (.exec 0x11fdc6 (fun s => s.RIP = 0x11fdc6) (mulR64Effect 0x11fdc6 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[468, 766]
    (.letOp (n := 771) (.out 0x11fdc9 (addR64R64Effect 0x11fdc9 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[768, 739]
    (.letOp (n := 772) (.out 0x11fdc9 (addR64R64Effect 0x11fdc9 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[768, 739]
    (.letOp (n := 773) (.exec 0x11fdc9 (fun s => s.RIP = 0x11fdc9) (addR64R64Effect 0x11fdc9 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[768, 739]
    (.letOp (n := 774) (.out 0x11fdcc (atFlags StatusFlags.CF (adcR64R64Effect 0x11fdcc 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[737, 769, 772]
    (.letOp (n := 775) (.exec 0x11fdcc (fun s => s.RIP = 0x11fdcc) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fdcc 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[737, 769, 772]
    (.letOp (n := 776) (.out 0x11fdcf (addR64R64Effect 0x11fdcf 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[771, 764]
    (.letOp (n := 777) (.out 0x11fdcf (addR64R64Effect 0x11fdcf 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[771, 764]
    (.letOp (n := 778) (.exec 0x11fdcf (fun s => s.RIP = 0x11fdcf) (addR64R64Effect 0x11fdcf 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[771, 764]
    (.letOp (n := 779) (.out 0x11fdd2 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fdd2 3 14)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[774, 762, 777]
    (.letOp (n := 780) (.exec 0x11fdd2 (fun s => s.RIP = 0x11fdd2) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fdd2 3 14)) (Reg.operands [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[774, 762, 777]
    (.letOp (n := 781) (.out 0x11fdd5 (addR64R64Effect 0x11fdd5 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[776, 730]
    (.letOp (n := 782) (.out 0x11fdd5 (addR64R64Effect 0x11fdd5 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[776, 730]
    (.letOp (n := 783) (.exec 0x11fdd5 (fun s => s.RIP = 0x11fdd5) (addR64R64Effect 0x11fdd5 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[776, 730]
    (.letOp (n := 784) (.out 0x11fdd8 (movR64R64Effect 0x11fdd8 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[781]
    (.letOp (n := 785) (.exec 0x11fdd8 (fun s => s.RIP = 0x11fdd8) (movR64R64Effect 0x11fdd8 15 0) (Reg.operands [.gpr 0] [])) #v[781]
    (.letOp (n := 786) (.out 0x11fddb (atFlags StatusFlags.CF (adcR64R64Effect 0x11fddb 3 8)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[779, 728, 782]
    (.letOp (n := 787) (.exec 0x11fddb (fun s => s.RIP = 0x11fddb) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fddb 3 8)) (Reg.operands [.gpr 3, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[779, 728, 782]
    (.letOp (n := 788) (.out 0x11fdde (shldR64R64Effect 0x11fdde 5 1 11 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[751, 748]
    (.letOp (n := 789) (.exec 0x11fdde (fun s => s.RIP = 0x11fdde) (shldR64R64Effect 0x11fdde 5 1 11 12) (Reg.operands [.gpr 1, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[751, 748]
    (.letOp (n := 790) (.out 0x11fde3 (movR64Imm64Effect 0x11fde3 0 0xffffffffffffe) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 791) (.exec 0x11fde3 (fun s => s.RIP = 0x11fde3) (movR64Imm64Effect 0x11fde3 0 0xffffffffffffe) (Reg.operands [] [])) #v[]
    (b_l11f8f6_17))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_16 : List UInt8 :=
  [0x49, 0x89, 0xC3, 0x4D, 0x01, 0xF3, 0x48, 0x11, 0xD1, 0x4C, 0x89, 0xD8, 0x4C, 0x21, 0xC8, 0x4C,
    0x89, 0xCD, 0x48, 0xF7, 0xE6, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x44, 0x24, 0x10,
    0x49, 0xF7, 0xE5, 0x4C, 0x01, 0xF8, 0x48, 0x11, 0xD3, 0x4C, 0x01, 0xE0, 0x4C, 0x11, 0xF3, 0x48,
    0x01, 0xF8, 0x49, 0x89, 0xC7, 0x4C, 0x11, 0xC3, 0x4C, 0x0F, 0xA4, 0xD9, 0x0C, 0x48, 0xB8, 0xFE,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] ++ bytes_l11f8f6_17

theorem code_l11f8f6_16 : ∀ x ∈ codeRange 0x11fda6 bytes_l11f8f6_16, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fda6 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_17

def b_l11f8f6_15 : Block Op Label signature Reg.count 701 :=
  .letOp (n := 701) (.out 0x11fd5a (andR64R64Effect 0x11fd5a 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[697, 699]
    (.letOp (n := 702) (.exec 0x11fd5a (fun s => s.RIP = 0x11fd5a) (andR64R64Effect 0x11fd5a 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[697, 699]
    (.letOp (n := 703) (.out 0x11fd5d (movR64Imm64Effect 0x11fd5d 6 0x1000003d10) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 704) (.exec 0x11fd5d (fun s => s.RIP = 0x11fd5d) (movR64Imm64Effect 0x11fd5d 6 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 705) (.out 0x11fd67 (mulR64Effect 0x11fd67 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[703, 701]
    (.letOp (n := 706) (.out 0x11fd67 (mulR64Effect 0x11fd67 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[703, 701]
    (.letOp (n := 707) (.exec 0x11fd67 (fun s => s.RIP = 0x11fd67) (mulR64Effect 0x11fd67 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[703, 701]
    (.letOp (n := 708) (.out 0x11fd6a (movR64R64Effect 0x11fd6a 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[705]
    (.letOp (n := 709) (.exec 0x11fd6a (fun s => s.RIP = 0x11fd6a) (movR64R64Effect 0x11fd6a 10 0) (Reg.operands [.gpr 0] [])) #v[705]
    (.letOp (n := 710) (.out 0x11fd6d (addR64R64Effect 0x11fd6d 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15] []) (.reg (.gpr 10))) #v[708, 665]
    (.letOp (n := 711) (.out 0x11fd6d (addR64R64Effect 0x11fd6d 10 15) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 15] []) (.flag .CF)) #v[708, 665]
    (.letOp (n := 712) (.exec 0x11fd6d (fun s => s.RIP = 0x11fd6d) (addR64R64Effect 0x11fd6d 10 15) (Reg.operands [.gpr 10, .gpr 15] [])) #v[708, 665]
    (.letOp (n := 713) (.out 0x11fd70 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fd70 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[663, 706, 711]
    (.letOp (n := 714) (.exec 0x11fd70 (fun s => s.RIP = 0x11fd70) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fd70 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[663, 706, 711]
    (.letOp (n := 715) (.out 0x11fd73 (addR64R64Effect 0x11fd73 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[710, 655]
    (.letOp (n := 716) (.out 0x11fd73 (addR64R64Effect 0x11fd73 10 1) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 1] []) (.flag .CF)) #v[710, 655]
    (.letOp (n := 717) (.exec 0x11fd73 (fun s => s.RIP = 0x11fd73) (addR64R64Effect 0x11fd73 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[710, 655]
    (.letOp (n := 718) (.out 0x11fd76 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11fd76 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[713, 716]
    (.letOp (n := 719) (.exec 0x11fd76 (fun s => s.RIP = 0x11fd76) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11fd76 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[713, 716]
    (.letOp (n := 720) (.out 0x11fd7a (movR64R64Effect 0x11fd7a 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[695]
    (.letOp (n := 721) (.exec 0x11fd7a (fun s => s.RIP = 0x11fd7a) (movR64R64Effect 0x11fd7a 1 14) (Reg.operands [.gpr 14] [])) #v[695]
    (.letOp (n := 722) (.out 0x11fd7d (shldR64R64Effect 0x11fd7d 5 14 12 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[695, 692]
    (.letOp (n := 723) (.exec 0x11fd7d (fun s => s.RIP = 0x11fd7d) (shldR64R64Effect 0x11fd7d 5 14 12 12) (Reg.operands [.gpr 14, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[695, 692]
    (.letOp (n := 724) (.out 0x11fd82 (shrR64Effect 0x11fd82 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[720]
    (.letOp (n := 725) (.exec 0x11fd82 (fun s => s.RIP = 0x11fd82) (shrR64Effect 0x11fd82 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[720]
    (.letOp (n := 726) (.out 0x11fd86 (movR64R64Effect 0x11fd86 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[718]
    (.letOp (n := 727) (.exec 0x11fd86 (fun s => s.RIP = 0x11fd86) (movR64R64Effect 0x11fd86 8 7) (Reg.operands [.gpr 7] [])) #v[718]
    (.letOp (n := 728) (.out 0x11fd89 (shrR64Effect 0x11fd89 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[726]
    (.letOp (n := 729) (.exec 0x11fd89 (fun s => s.RIP = 0x11fd89) (shrR64Effect 0x11fd89 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[726]
    (.letOp (n := 730) (.out 0x11fd8d (shldR64R64Effect 0x11fd8d 5 7 10 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[718, 715]
    (.letOp (n := 731) (.exec 0x11fd8d (fun s => s.RIP = 0x11fd8d) (shldR64R64Effect 0x11fd8d 5 7 10 12) (Reg.operands [.gpr 7, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[718, 715]
    (.letOp (n := 732) (.out 0x11fd92 (movR64M64Effect 0x11fd92 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 733) (.exec 0x11fd92 (LoadPre 0x11fd92 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11fd92 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fd92 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 734) (.out 0x11fd97 (mulR64Effect 0x11fd97 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[732, 732]
    (.letOp (n := 735) (.out 0x11fd97 (mulR64Effect 0x11fd97 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 0] []) (.reg (.gpr 2))) #v[732, 732]
    (.letOp (n := 736) (.exec 0x11fd97 (fun s => s.RIP = 0x11fd97) (mulR64Effect 0x11fd97 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[732, 732]
    (.letOp (n := 737) (.out 0x11fd9a (movR64R64Effect 0x11fd9a 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[735]
    (.letOp (n := 738) (.exec 0x11fd9a (fun s => s.RIP = 0x11fd9a) (movR64R64Effect 0x11fd9a 3 2) (Reg.operands [.gpr 2] [])) #v[735]
    (.letOp (n := 739) (.out 0x11fd9d (movR64R64Effect 0x11fd9d 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[734]
    (.letOp (n := 740) (.exec 0x11fd9d (fun s => s.RIP = 0x11fd9d) (movR64R64Effect 0x11fd9d 15 0) (Reg.operands [.gpr 0] [])) #v[734]
    (.letOp (n := 741) (.out 0x11fda0 (movR64R64Effect 0x11fda0 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[678]
    (.letOp (n := 742) (.exec 0x11fda0 (fun s => s.RIP = 0x11fda0) (movR64R64Effect 0x11fda0 0 5) (Reg.operands [.gpr 5] [])) #v[678]
    (.letOp (n := 743) (.out 0x11fda3 (mulR64Effect 0x11fda3 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[667, 741]
    (.letOp (n := 744) (.out 0x11fda3 (mulR64Effect 0x11fda3 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[667, 741]
    (.letOp (n := 745) (.exec 0x11fda3 (fun s => s.RIP = 0x11fda3) (mulR64Effect 0x11fda3 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[667, 741]
    (b_l11f8f6_16)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_15 : List UInt8 :=
  [0x4C, 0x21, 0xC8, 0x48, 0xBE, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE6,
    0x49, 0x89, 0xC2, 0x4D, 0x01, 0xFA, 0x48, 0x11, 0xD7, 0x49, 0x01, 0xCA, 0x48, 0x83, 0xD7, 0x00,
    0x4C, 0x89, 0xF1, 0x4D, 0x0F, 0xA4, 0xE6, 0x0C, 0x48, 0xC1, 0xE9, 0x34, 0x49, 0x89, 0xF8, 0x49,
    0xC1, 0xE8, 0x34, 0x4C, 0x0F, 0xA4, 0xD7, 0x0C, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0xF7, 0xE0,
    0x48, 0x89, 0xD3, 0x49, 0x89, 0xC7, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE3] ++ bytes_l11f8f6_16

theorem code_l11f8f6_15 : ∀ x ∈ codeRange 0x11fd5a bytes_l11f8f6_15, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fd5a 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_16

def b_l11f8f6_14 : Block Op Label signature Reg.count 657 :=
  .letOp (n := 657) (.out 0x11fd14 (leaR64Effect 0x11fd14 0 (.sib 6 (some 6) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 6] []) (.reg (.gpr 0))) #v[541, 541]
    (.letOp (n := 658) (.exec 0x11fd14 (fun s => s.RIP = 0x11fd14) (leaR64Effect 0x11fd14 0 (.sib 6 (some 6) 0 .none)) (Reg.operands [.gpr 6, .gpr 6] [])) #v[541, 541]
    (.letOp (n := 659) (.exec 0x11fd18 (StorePre 0x11fd18 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11fd18 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11fd18 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[657, 4]
    (.letOp (n := 660) (.out 0x11fd1d (mulR64Effect 0x11fd1d 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[472, 657]
    (.letOp (n := 661) (.out 0x11fd1d (mulR64Effect 0x11fd1d 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[472, 657]
    (.letOp (n := 662) (.exec 0x11fd1d (fun s => s.RIP = 0x11fd1d) (mulR64Effect 0x11fd1d 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[472, 657]
    (.letOp (n := 663) (.out 0x11fd20 (movR64R64Effect 0x11fd20 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[661]
    (.letOp (n := 664) (.exec 0x11fd20 (fun s => s.RIP = 0x11fd20) (movR64R64Effect 0x11fd20 7 2) (Reg.operands [.gpr 2] [])) #v[661]
    (.letOp (n := 665) (.out 0x11fd23 (movR64R64Effect 0x11fd23 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[660]
    (.letOp (n := 666) (.exec 0x11fd23 (fun s => s.RIP = 0x11fd23) (movR64R64Effect 0x11fd23 15 0) (Reg.operands [.gpr 0] [])) #v[660]
    (.letOp (n := 667) (.out 0x11fd26 (movR64R64Effect 0x11fd26 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 12] []) (.reg (.gpr 11))) #v[455]
    (.letOp (n := 668) (.exec 0x11fd26 (fun s => s.RIP = 0x11fd26) (movR64R64Effect 0x11fd26 11 12) (Reg.operands [.gpr 12] [])) #v[455]
    (.letOp (n := 669) (.out 0x11fd29 (movR64R64Effect 0x11fd29 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[455]
    (.letOp (n := 670) (.exec 0x11fd29 (fun s => s.RIP = 0x11fd29) (movR64R64Effect 0x11fd29 0 12) (Reg.operands [.gpr 12] [])) #v[455]
    (.letOp (n := 671) (.out 0x11fd2c (mulR64Effect 0x11fd2c 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[455, 669]
    (.letOp (n := 672) (.out 0x11fd2c (mulR64Effect 0x11fd2c 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[455, 669]
    (.letOp (n := 673) (.exec 0x11fd2c (fun s => s.RIP = 0x11fd2c) (mulR64Effect 0x11fd2c 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[455, 669]
    (.letOp (n := 674) (.out 0x11fd2f (movR64R64Effect 0x11fd2f 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[671]
    (.letOp (n := 675) (.exec 0x11fd2f (fun s => s.RIP = 0x11fd2f) (movR64R64Effect 0x11fd2f 8 0) (Reg.operands [.gpr 0] [])) #v[671]
    (.letOp (n := 676) (.out 0x11fd32 (movR64R64Effect 0x11fd32 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[672]
    (.letOp (n := 677) (.exec 0x11fd32 (fun s => s.RIP = 0x11fd32) (movR64R64Effect 0x11fd32 14 2) (Reg.operands [.gpr 2] [])) #v[672]
    (.letOp (n := 678) (.out 0x11fd35 (addR64R64Effect 0x11fd35 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 5] []) (.reg (.gpr 5))) #v[607, 607]
    (.letOp (n := 679) (.exec 0x11fd35 (fun s => s.RIP = 0x11fd35) (addR64R64Effect 0x11fd35 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[607, 607]
    (.letOp (n := 680) (.out 0x11fd38 (movR64R64Effect 0x11fd38 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[678]
    (.letOp (n := 681) (.exec 0x11fd38 (fun s => s.RIP = 0x11fd38) (movR64R64Effect 0x11fd38 0 5) (Reg.operands [.gpr 5] [])) #v[678]
    (.letOp (n := 682) (.out 0x11fd3b (mulR64Effect 0x11fd3b 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[468, 680]
    (.letOp (n := 683) (.out 0x11fd3b (mulR64Effect 0x11fd3b 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[468, 680]
    (.letOp (n := 684) (.exec 0x11fd3b (fun s => s.RIP = 0x11fd3b) (mulR64Effect 0x11fd3b 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[468, 680]
    (.letOp (n := 685) (.out 0x11fd3e (movR64R64Effect 0x11fd3e 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[682]
    (.letOp (n := 686) (.exec 0x11fd3e (fun s => s.RIP = 0x11fd3e) (movR64R64Effect 0x11fd3e 12 0) (Reg.operands [.gpr 0] [])) #v[682]
    (.letOp (n := 687) (.out 0x11fd41 (addR64R64Effect 0x11fd41 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 8] []) (.reg (.gpr 12))) #v[685, 674]
    (.letOp (n := 688) (.out 0x11fd41 (addR64R64Effect 0x11fd41 12 8) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 8] []) (.flag .CF)) #v[685, 674]
    (.letOp (n := 689) (.exec 0x11fd41 (fun s => s.RIP = 0x11fd41) (addR64R64Effect 0x11fd41 12 8) (Reg.operands [.gpr 12, .gpr 8] [])) #v[685, 674]
    (.letOp (n := 690) (.out 0x11fd44 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fd44 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[676, 683, 688]
    (.letOp (n := 691) (.exec 0x11fd44 (fun s => s.RIP = 0x11fd44) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fd44 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[676, 683, 688]
    (.letOp (n := 692) (.out 0x11fd47 (addR64R64Effect 0x11fd47 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[687, 632]
    (.letOp (n := 693) (.out 0x11fd47 (addR64R64Effect 0x11fd47 12 3) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 3] []) (.flag .CF)) #v[687, 632]
    (.letOp (n := 694) (.exec 0x11fd47 (fun s => s.RIP = 0x11fd47) (addR64R64Effect 0x11fd47 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[687, 632]
    (.letOp (n := 695) (.out 0x11fd4a (atFlags StatusFlags.CF (adcR64R64Effect 0x11fd4a 14 10)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[690, 642, 693]
    (.letOp (n := 696) (.exec 0x11fd4a (fun s => s.RIP = 0x11fd4a) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fd4a 14 10)) (Reg.operands [.gpr 14, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[690, 642, 693]
    (.letOp (n := 697) (.out 0x11fd4d (movR64R64Effect 0x11fd4d 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[692]
    (.letOp (n := 698) (.exec 0x11fd4d (fun s => s.RIP = 0x11fd4d) (movR64R64Effect 0x11fd4d 0 12) (Reg.operands [.gpr 12] [])) #v[692]
    (.letOp (n := 699) (.out 0x11fd50 (movR64Imm64Effect 0x11fd50 9 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 700) (.exec 0x11fd50 (fun s => s.RIP = 0x11fd50) (movR64Imm64Effect 0x11fd50 9 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (b_l11f8f6_15))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_14 : List UInt8 :=
  [0x48, 0x8D, 0x04, 0x36, 0x48, 0x89, 0x44, 0x24, 0x10, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0xD7, 0x49,
    0x89, 0xC7, 0x4D, 0x89, 0xE3, 0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE4, 0x49, 0x89, 0xC0, 0x49, 0x89,
    0xD6, 0x48, 0x01, 0xED, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xC4, 0x4D, 0x01, 0xC4,
    0x49, 0x11, 0xD6, 0x49, 0x01, 0xDC, 0x4D, 0x11, 0xD6, 0x4C, 0x89, 0xE0, 0x49, 0xB9, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] ++ bytes_l11f8f6_15

theorem code_l11f8f6_14 : ∀ x ∈ codeRange 0x11fd14 bytes_l11f8f6_14, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fd14 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_15

def b_l11f8f6_13 : Block Op Label signature Reg.count 614 :=
  .letOp (n := 614) (.out 0x11fcbf (andR32Imm8Effect 0x11fcbf 4 11 0xf) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[587]
    (.letOp (n := 615) (.exec 0x11fcbf (fun s => s.RIP = 0x11fcbf) (andR32Imm8Effect 0x11fcbf 4 11 0xf) (Reg.operands [.gpr 11] [])) #v[587]
    (.letOp (n := 616) (.out 0x11fcc3 (addR64R64Effect 0x11fcc3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[611, 605]
    (.letOp (n := 617) (.out 0x11fcc3 (addR64R64Effect 0x11fcc3 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[611, 605]
    (.letOp (n := 618) (.exec 0x11fcc3 (fun s => s.RIP = 0x11fcc3) (addR64R64Effect 0x11fcc3 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[611, 605]
    (.letOp (n := 619) (.out 0x11fcc6 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fcc6 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[603, 612, 617]
    (.letOp (n := 620) (.exec 0x11fcc6 (fun s => s.RIP = 0x11fcc6) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fcc6 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[603, 612, 617]
    (.letOp (n := 621) (.out 0x11fcc9 (shldR64R64Effect 0x11fcc9 5 3 0 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[619, 616]
    (.letOp (n := 622) (.exec 0x11fcc9 (fun s => s.RIP = 0x11fcc9) (shldR64R64Effect 0x11fcc9 5 3 0 1) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[619, 616]
    (.letOp (n := 623) (.out 0x11fcce (addR64R64Effect 0x11fcce 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[616, 616]
    (.letOp (n := 624) (.exec 0x11fcce (fun s => s.RIP = 0x11fcce) (addR64R64Effect 0x11fcce 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[616, 616]
    (.letOp (n := 625) (.out 0x11fcd1 (addR64R64Effect 0x11fcd1 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[623, 581]
    (.letOp (n := 626) (.out 0x11fcd1 (addR64R64Effect 0x11fcd1 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[623, 581]
    (.letOp (n := 627) (.exec 0x11fcd1 (fun s => s.RIP = 0x11fcd1) (addR64R64Effect 0x11fcd1 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[623, 581]
    (.letOp (n := 628) (.out 0x11fcd4 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fcd4 3 10)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[621, 583, 626]
    (.letOp (n := 629) (.exec 0x11fcd4 (fun s => s.RIP = 0x11fcd4) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fcd4 3 10)) (Reg.operands [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[621, 583, 626]
    (.letOp (n := 630) (.out 0x11fcd7 (movR64R64Effect 0x11fcd7 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 3] []) (.reg (.gpr 10))) #v[628]
    (.letOp (n := 631) (.exec 0x11fcd7 (fun s => s.RIP = 0x11fcd7) (movR64R64Effect 0x11fcd7 10 3) (Reg.operands [.gpr 3] [])) #v[628]
    (.letOp (n := 632) (.out 0x11fcda (shldR64R64Effect 0x11fcda 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[628, 625]
    (.letOp (n := 633) (.exec 0x11fcda (fun s => s.RIP = 0x11fcda) (shldR64R64Effect 0x11fcda 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[628, 625]
    (.letOp (n := 634) (.out 0x11fcdf (shlR64Effect 0x11fcdf 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[625]
    (.letOp (n := 635) (.exec 0x11fcdf (fun s => s.RIP = 0x11fcdf) (shlR64Effect 0x11fcdf 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[625]
    (.letOp (n := 636) (.out 0x11fce3 (movR64Imm64Effect 0x11fce3 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 637) (.exec 0x11fce3 (fun s => s.RIP = 0x11fce3) (movR64Imm64Effect 0x11fce3 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 638) (.out 0x11fced (andR64R64Effect 0x11fced 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[634, 636]
    (.letOp (n := 639) (.exec 0x11fced (fun s => s.RIP = 0x11fced) (andR64R64Effect 0x11fced 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[634, 636]
    (.letOp (n := 640) (.out 0x11fcf0 (orR64R64Effect 0x11fcf0 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[638, 614]
    (.letOp (n := 641) (.exec 0x11fcf0 (fun s => s.RIP = 0x11fcf0) (orR64R64Effect 0x11fcf0 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[638, 614]
    (.letOp (n := 642) (.out 0x11fcf3 (shrR64Effect 0x11fcf3 4 10 52) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[630]
    (.letOp (n := 643) (.exec 0x11fcf3 (fun s => s.RIP = 0x11fcf3) (shrR64Effect 0x11fcf3 4 10 52) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[630]
    (.letOp (n := 644) (.out 0x11fcf7 (movR64Imm64Effect 0x11fcf7 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 645) (.exec 0x11fcf7 (fun s => s.RIP = 0x11fcf7) (movR64Imm64Effect 0x11fcf7 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 646) (.out 0x11fd01 (mulR64Effect 0x11fd01 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[644, 640]
    (.letOp (n := 647) (.out 0x11fd01 (mulR64Effect 0x11fd01 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[644, 640]
    (.letOp (n := 648) (.exec 0x11fd01 (fun s => s.RIP = 0x11fd01) (mulR64Effect 0x11fd01 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[644, 640]
    (.letOp (n := 649) (.out 0x11fd04 (addR64R64Effect 0x11fd04 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[646, 596]
    (.letOp (n := 650) (.out 0x11fd04 (addR64R64Effect 0x11fd04 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[646, 596]
    (.letOp (n := 651) (.exec 0x11fd04 (fun s => s.RIP = 0x11fd04) (addR64R64Effect 0x11fd04 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[646, 596]
    (.letOp (n := 652) (.exec 0x11fd07 (StorePre 0x11fd07 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11fd07 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11fd07 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[649, 4]
    (.letOp (n := 653) (.out 0x11fd0c (atFlags StatusFlags.CF (adcR64R64Effect 0x11fd0c 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[594, 647, 650]
    (.letOp (n := 654) (.exec 0x11fd0c (fun s => s.RIP = 0x11fd0c) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fd0c 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[594, 647, 650]
    (.letOp (n := 655) (.out 0x11fd0f (shldR64R64Effect 0x11fd0f 5 1 0 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[653, 649]
    (.letOp (n := 656) (.exec 0x11fd0f (fun s => s.RIP = 0x11fd0f) (shldR64R64Effect 0x11fd0f 5 1 0 12) (Reg.operands [.gpr 1, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[653, 649]
    (b_l11f8f6_14)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_13 : List UInt8 :=
  [0x41, 0x83, 0xE3, 0x0F, 0x4C, 0x01, 0xC8, 0x48, 0x11, 0xD3, 0x48, 0x0F, 0xA4, 0xC3, 0x01, 0x48,
    0x01, 0xC0, 0x4C, 0x01, 0xC0, 0x4C, 0x11, 0xD3, 0x49, 0x89, 0xDA, 0x48, 0x0F, 0xA4, 0xC3, 0x0C,
    0x48, 0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21,
    0xD0, 0x4C, 0x09, 0xD8, 0x49, 0xC1, 0xEA, 0x34, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00,
    0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x01, 0xF8, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x11, 0xD1,
    0x48, 0x0F, 0xA4, 0xC1, 0x0C] ++ bytes_l11f8f6_14

theorem code_l11f8f6_13 : ∀ x ∈ codeRange 0x11fcbf bytes_l11f8f6_13, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fcbf 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_14

def b_l11f8f6_12 : Block Op Label signature Reg.count 571 :=
  .letOp (n := 571) (.out 0x11fc7c (atFlags StatusFlags.CF (adcR64R64Effect 0x11fc7c 8 3)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[566, 559, 569]
    (.letOp (n := 572) (.exec 0x11fc7c (fun s => s.RIP = 0x11fc7c) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fc7c 8 3)) (Reg.operands [.gpr 8, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[566, 559, 569]
    (.letOp (n := 573) (.out 0x11fc7f (addR64R64Effect 0x11fc7f 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[568, 516]
    (.letOp (n := 574) (.out 0x11fc7f (addR64R64Effect 0x11fc7f 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[568, 516]
    (.letOp (n := 575) (.exec 0x11fc7f (fun s => s.RIP = 0x11fc7f) (addR64R64Effect 0x11fc7f 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[568, 516]
    (.letOp (n := 576) (.exec 0x11fc82 (StorePre 0x11fc82 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11fc82 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11fc82 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[573, 4]
    (.letOp (n := 577) (.out 0x11fc86 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fc86 8 10)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[571, 552, 574]
    (.letOp (n := 578) (.exec 0x11fc86 (fun s => s.RIP = 0x11fc86) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fc86 8 10)) (Reg.operands [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[571, 552, 574]
    (.letOp (n := 579) (.out 0x11fc89 (movR64R64Effect 0x11fc89 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[577]
    (.letOp (n := 580) (.exec 0x11fc89 (fun s => s.RIP = 0x11fc89) (movR64R64Effect 0x11fc89 10 8) (Reg.operands [.gpr 8] [])) #v[577]
    (.letOp (n := 581) (.out 0x11fc8c (shldR64R64Effect 0x11fc8c 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[577, 573]
    (.letOp (n := 582) (.exec 0x11fc8c (fun s => s.RIP = 0x11fc8c) (shldR64R64Effect 0x11fc8c 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[577, 573]
    (.letOp (n := 583) (.out 0x11fc91 (shrR64Effect 0x11fc91 4 10 52) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[579]
    (.letOp (n := 584) (.exec 0x11fc91 (fun s => s.RIP = 0x11fc91) (shrR64Effect 0x11fc91 4 10 52) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[579]
    (.letOp (n := 585) (.out 0x11fc95 (movR64R64Effect 0x11fc95 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[573]
    (.letOp (n := 586) (.exec 0x11fc95 (fun s => s.RIP = 0x11fc95) (movR64R64Effect 0x11fc95 11 0) (Reg.operands [.gpr 0] [])) #v[573]
    (.letOp (n := 587) (.out 0x11fc98 (shrR64Effect 0x11fc98 4 11 48) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[585]
    (.letOp (n := 588) (.exec 0x11fc98 (fun s => s.RIP = 0x11fc98) (shrR64Effect 0x11fc98 4 11 48) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[585]
    (.letOp (n := 589) (.out 0x11fc9c (movR64R64Effect 0x11fc9c 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[541]
    (.letOp (n := 590) (.exec 0x11fc9c (fun s => s.RIP = 0x11fc9c) (movR64R64Effect 0x11fc9c 0 6) (Reg.operands [.gpr 6] [])) #v[541]
    (.letOp (n := 591) (.out 0x11fc9f (mulR64Effect 0x11fc9f 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[541, 589]
    (.letOp (n := 592) (.out 0x11fc9f (mulR64Effect 0x11fc9f 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[541, 589]
    (.letOp (n := 593) (.exec 0x11fc9f (fun s => s.RIP = 0x11fc9f) (mulR64Effect 0x11fc9f 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[541, 589]
    (.letOp (n := 594) (.out 0x11fca2 (movR64R64Effect 0x11fca2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[592]
    (.letOp (n := 595) (.exec 0x11fca2 (fun s => s.RIP = 0x11fca2) (movR64R64Effect 0x11fca2 1 2) (Reg.operands [.gpr 2] [])) #v[592]
    (.letOp (n := 596) (.out 0x11fca5 (movR64R64Effect 0x11fca5 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[591]
    (.letOp (n := 597) (.exec 0x11fca5 (fun s => s.RIP = 0x11fca5) (movR64R64Effect 0x11fca5 7 0) (Reg.operands [.gpr 0] [])) #v[591]
    (.letOp (n := 598) (.out 0x11fca8 (movR64R64Effect 0x11fca8 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[455]
    (.letOp (n := 599) (.exec 0x11fca8 (fun s => s.RIP = 0x11fca8) (movR64R64Effect 0x11fca8 0 12) (Reg.operands [.gpr 12] [])) #v[455]
    (.letOp (n := 600) (.out 0x11fcab (mulR64Effect 0x11fcab 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[468, 598]
    (.letOp (n := 601) (.out 0x11fcab (mulR64Effect 0x11fcab 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[468, 598]
    (.letOp (n := 602) (.exec 0x11fcab (fun s => s.RIP = 0x11fcab) (mulR64Effect 0x11fcab 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[468, 598]
    (.letOp (n := 603) (.out 0x11fcae (movR64R64Effect 0x11fcae 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[601]
    (.letOp (n := 604) (.exec 0x11fcae (fun s => s.RIP = 0x11fcae) (movR64R64Effect 0x11fcae 3 2) (Reg.operands [.gpr 2] [])) #v[601]
    (.letOp (n := 605) (.out 0x11fcb1 (movR64R64Effect 0x11fcb1 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[600]
    (.letOp (n := 606) (.exec 0x11fcb1 (fun s => s.RIP = 0x11fcb1) (movR64R64Effect 0x11fcb1 9 0) (Reg.operands [.gpr 0] [])) #v[600]
    (.letOp (n := 607) (.out 0x11fcb4 (movR64M64Effect 0x11fcb4 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 608) (.exec 0x11fcb4 (LoadPre 0x11fcb4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11fcb4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fcb4 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 609) (.out 0x11fcb9 (movR64R64Effect 0x11fcb9 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[607]
    (.letOp (n := 610) (.exec 0x11fcb9 (fun s => s.RIP = 0x11fcb9) (movR64R64Effect 0x11fcb9 0 5) (Reg.operands [.gpr 5] [])) #v[607]
    (.letOp (n := 611) (.out 0x11fcbc (mulR64Effect 0x11fcbc 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[472, 609]
    (.letOp (n := 612) (.out 0x11fcbc (mulR64Effect 0x11fcbc 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[472, 609]
    (.letOp (n := 613) (.exec 0x11fcbc (fun s => s.RIP = 0x11fcbc) (mulR64Effect 0x11fcbc 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[472, 609]
    (b_l11f8f6_13)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_12 : List UInt8 :=
  [0x49, 0x11, 0xD8, 0x48, 0x01, 0xF8, 0x48, 0x89, 0x04, 0x24, 0x4D, 0x11, 0xD0, 0x4D, 0x89, 0xC2,
    0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x49, 0xC1, 0xEA, 0x34, 0x49, 0x89, 0xC3, 0x49, 0xC1, 0xEB, 0x30,
    0x48, 0x89, 0xF0, 0x48, 0xF7, 0xE6, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC7, 0x4C, 0x89, 0xE0, 0x49,
    0xF7, 0xE5, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC1, 0x48, 0x8B, 0x6C, 0x24, 0x20, 0x48, 0x89, 0xE8,
    0x49, 0xF7, 0xE7] ++ bytes_l11f8f6_13

theorem code_l11f8f6_12 : ∀ x ∈ codeRange 0x11fc7c bytes_l11f8f6_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fc7c 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_13

def b_l11f8f6_11 : Block Op Label signature Reg.count 525 :=
  .letOp (n := 525) (.out 0x11fc3d (movR64R64Effect 0x11fc3d 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[520]
    (.letOp (n := 526) (.exec 0x11fc3d (fun s => s.RIP = 0x11fc3d) (movR64R64Effect 0x11fc3d 9 0) (Reg.operands [.gpr 0] [])) #v[520]
    (.letOp (n := 527) (.out 0x11fc40 (movR64R64Effect 0x11fc40 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[512]
    (.letOp (n := 528) (.exec 0x11fc40 (fun s => s.RIP = 0x11fc40) (movR64R64Effect 0x11fc40 0 8) (Reg.operands [.gpr 8] [])) #v[512]
    (.letOp (n := 529) (.out 0x11fc43 (mulR64Effect 0x11fc43 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[423, 527]
    (.letOp (n := 530) (.out 0x11fc43 (mulR64Effect 0x11fc43 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[423, 527]
    (.letOp (n := 531) (.exec 0x11fc43 (fun s => s.RIP = 0x11fc43) (mulR64Effect 0x11fc43 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[423, 527]
    (.letOp (n := 532) (.out 0x11fc46 (movR64R64Effect 0x11fc46 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[530]
    (.letOp (n := 533) (.exec 0x11fc46 (fun s => s.RIP = 0x11fc46) (movR64R64Effect 0x11fc46 8 2) (Reg.operands [.gpr 2] [])) #v[530]
    (.letOp (n := 534) (.out 0x11fc49 (movR64R64Effect 0x11fc49 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[529]
    (.letOp (n := 535) (.exec 0x11fc49 (fun s => s.RIP = 0x11fc49) (movR64R64Effect 0x11fc49 11 0) (Reg.operands [.gpr 0] [])) #v[529]
    (.letOp (n := 536) (.out 0x11fc4c (movR64R64Effect 0x11fc4c 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[486]
    (.letOp (n := 537) (.exec 0x11fc4c (fun s => s.RIP = 0x11fc4c) (movR64R64Effect 0x11fc4c 0 5) (Reg.operands [.gpr 5] [])) #v[486]
    (.letOp (n := 538) (.out 0x11fc4f (mulR64Effect 0x11fc4f 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[459, 536]
    (.letOp (n := 539) (.out 0x11fc4f (mulR64Effect 0x11fc4f 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[459, 536]
    (.letOp (n := 540) (.exec 0x11fc4f (fun s => s.RIP = 0x11fc4f) (mulR64Effect 0x11fc4f 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[459, 536]
    (.letOp (n := 541) (.out 0x11fc52 (movR64R64Effect 0x11fc52 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[459]
    (.letOp (n := 542) (.exec 0x11fc52 (fun s => s.RIP = 0x11fc52) (movR64R64Effect 0x11fc52 6 3) (Reg.operands [.gpr 3] [])) #v[459]
    (.letOp (n := 543) (.out 0x11fc55 (movR64R64Effect 0x11fc55 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[539]
    (.letOp (n := 544) (.exec 0x11fc55 (fun s => s.RIP = 0x11fc55) (movR64R64Effect 0x11fc55 3 2) (Reg.operands [.gpr 2] [])) #v[539]
    (.letOp (n := 545) (.out 0x11fc58 (movR64R64Effect 0x11fc58 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[538]
    (.letOp (n := 546) (.exec 0x11fc58 (fun s => s.RIP = 0x11fc58) (movR64R64Effect 0x11fc58 14 0) (Reg.operands [.gpr 0] [])) #v[538]
    (.letOp (n := 547) (.out 0x11fc5b (movR64R64Effect 0x11fc5b 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[455]
    (.letOp (n := 548) (.exec 0x11fc5b (fun s => s.RIP = 0x11fc5b) (movR64R64Effect 0x11fc5b 0 12) (Reg.operands [.gpr 12] [])) #v[455]
    (.letOp (n := 549) (.out 0x11fc5e (mulR64Effect 0x11fc5e 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[472, 547]
    (.letOp (n := 550) (.out 0x11fc5e (mulR64Effect 0x11fc5e 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[472, 547]
    (.letOp (n := 551) (.exec 0x11fc5e (fun s => s.RIP = 0x11fc5e) (mulR64Effect 0x11fc5e 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[472, 547]
    (.letOp (n := 552) (.out 0x11fc61 (shrR64Effect 0x11fc61 4 10 52) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[514]
    (.letOp (n := 553) (.exec 0x11fc61 (fun s => s.RIP = 0x11fc61) (shrR64Effect 0x11fc61 4 10 52) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[514]
    (.letOp (n := 554) (.out 0x11fc65 (addR64R64Effect 0x11fc65 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[549, 545]
    (.letOp (n := 555) (.out 0x11fc65 (addR64R64Effect 0x11fc65 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[549, 545]
    (.letOp (n := 556) (.exec 0x11fc65 (fun s => s.RIP = 0x11fc65) (addR64R64Effect 0x11fc65 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[549, 545]
    (.letOp (n := 557) (.out 0x11fc68 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fc68 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[543, 550, 555]
    (.letOp (n := 558) (.exec 0x11fc68 (fun s => s.RIP = 0x11fc68) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fc68 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[543, 550, 555]
    (.letOp (n := 559) (.out 0x11fc6b (shldR64R64Effect 0x11fc6b 5 3 0 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[557, 554]
    (.letOp (n := 560) (.exec 0x11fc6b (fun s => s.RIP = 0x11fc6b) (shldR64R64Effect 0x11fc6b 5 3 0 1) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[557, 554]
    (.letOp (n := 561) (.out 0x11fc70 (addR64R64Effect 0x11fc70 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[554, 554]
    (.letOp (n := 562) (.exec 0x11fc70 (fun s => s.RIP = 0x11fc70) (addR64R64Effect 0x11fc70 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[554, 554]
    (.letOp (n := 563) (.out 0x11fc73 (addR64R64Effect 0x11fc73 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[534, 525]
    (.letOp (n := 564) (.out 0x11fc73 (addR64R64Effect 0x11fc73 11 9) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 9] []) (.flag .CF)) #v[534, 525]
    (.letOp (n := 565) (.exec 0x11fc73 (fun s => s.RIP = 0x11fc73) (addR64R64Effect 0x11fc73 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[534, 525]
    (.letOp (n := 566) (.out 0x11fc76 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fc76 8 1)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[532, 523, 564]
    (.letOp (n := 567) (.exec 0x11fc76 (fun s => s.RIP = 0x11fc76) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fc76 8 1)) (Reg.operands [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[532, 523, 564]
    (.letOp (n := 568) (.out 0x11fc79 (addR64R64Effect 0x11fc79 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[561, 563]
    (.letOp (n := 569) (.out 0x11fc79 (addR64R64Effect 0x11fc79 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[561, 563]
    (.letOp (n := 570) (.exec 0x11fc79 (fun s => s.RIP = 0x11fc79) (addR64R64Effect 0x11fc79 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[561, 563]
    (b_l11f8f6_12))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_11 : List UInt8 :=
  [0x49, 0x89, 0xC1, 0x4C, 0x89, 0xC0, 0x49, 0xF7, 0xE3, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC3, 0x48,
    0x89, 0xE8, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0xDE, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC6, 0x4C, 0x89,
    0xE0, 0x49, 0xF7, 0xE7, 0x49, 0xC1, 0xEA, 0x34, 0x4C, 0x01, 0xF0, 0x48, 0x11, 0xD3, 0x48, 0x0F,
    0xA4, 0xC3, 0x01, 0x48, 0x01, 0xC0, 0x4D, 0x01, 0xCB, 0x49, 0x11, 0xC8, 0x4C, 0x01, 0xD8] ++ bytes_l11f8f6_12

theorem code_l11f8f6_11 : ∀ x ∈ codeRange 0x11fc3d bytes_l11f8f6_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fc3d 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_12

def b_l11f8f6_10 : Block Op Label signature Reg.count 482 :=
  .letOp (n := 482) (.out 0x11fbf0 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fbf0 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[464, 475, 480]
    (.letOp (n := 483) (.exec 0x11fbf0 (fun s => s.RIP = 0x11fbf0) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fbf0 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[464, 475, 480]
    (.letOp (n := 484) (.out 0x11fbf3 (shldR64R64Effect 0x11fbf3 5 7 9 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[482, 479]
    (.letOp (n := 485) (.exec 0x11fbf3 (fun s => s.RIP = 0x11fbf3) (shldR64R64Effect 0x11fbf3 5 7 9 1) (Reg.operands [.gpr 7, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[482, 479]
    (.letOp (n := 486) (.out 0x11fbf8 (movR64M64Effect 0x11fbf8 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 487) (.exec 0x11fbf8 (LoadPre 0x11fbf8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11fbf8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fbf8 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 488) (.out 0x11fbfd (movR64R64Effect 0x11fbfd 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[486]
    (.letOp (n := 489) (.exec 0x11fbfd (fun s => s.RIP = 0x11fbfd) (movR64R64Effect 0x11fbfd 0 5) (Reg.operands [.gpr 5] [])) #v[486]
    (.letOp (n := 490) (.out 0x11fc00 (mulR64Effect 0x11fc00 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[486, 488]
    (.letOp (n := 491) (.out 0x11fc00 (mulR64Effect 0x11fc00 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[486, 488]
    (.letOp (n := 492) (.exec 0x11fc00 (fun s => s.RIP = 0x11fc00) (mulR64Effect 0x11fc00 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[486, 488]
    (.letOp (n := 493) (.out 0x11fc03 (movR64R64Effect 0x11fc03 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[491]
    (.letOp (n := 494) (.exec 0x11fc03 (fun s => s.RIP = 0x11fc03) (movR64R64Effect 0x11fc03 8 2) (Reg.operands [.gpr 2] [])) #v[491]
    (.letOp (n := 495) (.out 0x11fc06 (movR64R64Effect 0x11fc06 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[490]
    (.letOp (n := 496) (.exec 0x11fc06 (fun s => s.RIP = 0x11fc06) (movR64R64Effect 0x11fc06 10 0) (Reg.operands [.gpr 0] [])) #v[490]
    (.letOp (n := 497) (.out 0x11fc09 (movR64Imm64Effect 0x11fc09 0 0xffffffffffffd) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 498) (.exec 0x11fc09 (fun s => s.RIP = 0x11fc09) (movR64Imm64Effect 0x11fc09 0 0xffffffffffffd) (Reg.operands [] [])) #v[]
    (.letOp (n := 499) (.out 0x11fc13 (andR64R64Effect 0x11fc13 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[497, 495]
    (.letOp (n := 500) (.exec 0x11fc13 (fun s => s.RIP = 0x11fc13) (andR64R64Effect 0x11fc13 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[497, 495]
    (.letOp (n := 501) (.out 0x11fc16 (mulR64Effect 0x11fc16 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[423, 499]
    (.letOp (n := 502) (.out 0x11fc16 (mulR64Effect 0x11fc16 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[423, 499]
    (.letOp (n := 503) (.exec 0x11fc16 (fun s => s.RIP = 0x11fc16) (mulR64Effect 0x11fc16 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[423, 499]
    (.letOp (n := 504) (.out 0x11fc19 (addR64R64Effect 0x11fc19 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[479, 479]
    (.letOp (n := 505) (.exec 0x11fc19 (fun s => s.RIP = 0x11fc19) (addR64R64Effect 0x11fc19 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[479, 479]
    (.letOp (n := 506) (.out 0x11fc1c (addR64R64Effect 0x11fc1c 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[501, 504]
    (.letOp (n := 507) (.out 0x11fc1c (addR64R64Effect 0x11fc1c 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[501, 504]
    (.letOp (n := 508) (.exec 0x11fc1c (fun s => s.RIP = 0x11fc1c) (addR64R64Effect 0x11fc1c 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[501, 504]
    (.letOp (n := 509) (.exec 0x11fc1f (StorePre 0x11fc1f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11fc1f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11fc1f 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[506, 4]
    (.letOp (n := 510) (.out 0x11fc24 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fc24 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[484, 502, 507]
    (.letOp (n := 511) (.exec 0x11fc24 (fun s => s.RIP = 0x11fc24) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fc24 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[484, 502, 507]
    (.letOp (n := 512) (.out 0x11fc27 (shldR64R64Effect 0x11fc27 5 8 10 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[493, 495]
    (.letOp (n := 513) (.exec 0x11fc27 (fun s => s.RIP = 0x11fc27) (shldR64R64Effect 0x11fc27 5 8 10 12) (Reg.operands [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[493, 495]
    (.letOp (n := 514) (.out 0x11fc2c (movR64R64Effect 0x11fc2c 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[510]
    (.letOp (n := 515) (.exec 0x11fc2c (fun s => s.RIP = 0x11fc2c) (movR64R64Effect 0x11fc2c 10 7) (Reg.operands [.gpr 7] [])) #v[510]
    (.letOp (n := 516) (.out 0x11fc2f (shldR64R64Effect 0x11fc2f 5 7 0 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[510, 506]
    (.letOp (n := 517) (.exec 0x11fc2f (fun s => s.RIP = 0x11fc2f) (shldR64R64Effect 0x11fc2f 5 7 0 12) (Reg.operands [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[510, 506]
    (.letOp (n := 518) (.out 0x11fc34 (movR64R64Effect 0x11fc34 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[468]
    (.letOp (n := 519) (.exec 0x11fc34 (fun s => s.RIP = 0x11fc34) (movR64R64Effect 0x11fc34 0 13) (Reg.operands [.gpr 13] [])) #v[468]
    (.letOp (n := 520) (.out 0x11fc37 (mulR64Effect 0x11fc37 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[468, 518]
    (.letOp (n := 521) (.out 0x11fc37 (mulR64Effect 0x11fc37 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[468, 518]
    (.letOp (n := 522) (.exec 0x11fc37 (fun s => s.RIP = 0x11fc37) (mulR64Effect 0x11fc37 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[468, 518]
    (.letOp (n := 523) (.out 0x11fc3a (movR64R64Effect 0x11fc3a 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[521]
    (.letOp (n := 524) (.exec 0x11fc3a (fun s => s.RIP = 0x11fc3a) (movR64R64Effect 0x11fc3a 1 2) (Reg.operands [.gpr 2] [])) #v[521]
    (b_l11f8f6_11)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_10 : List UInt8 :=
  [0x48, 0x11, 0xD7, 0x4C, 0x0F, 0xA4, 0xCF, 0x01, 0x48, 0x8B, 0x6C, 0x24, 0x20, 0x48, 0x89, 0xE8,
    0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC2, 0x48, 0xB8, 0xFD, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xD0, 0x49, 0xF7, 0xE3, 0x4D, 0x01, 0xC9, 0x4C, 0x01, 0xC8, 0x48,
    0x89, 0x44, 0x24, 0x28, 0x48, 0x11, 0xD7, 0x4D, 0x0F, 0xA4, 0xD0, 0x0C, 0x49, 0x89, 0xFA, 0x48,
    0x0F, 0xA4, 0xC7, 0x0C, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0xD1] ++ bytes_l11f8f6_11

theorem code_l11f8f6_10 : ∀ x ∈ codeRange 0x11fbf0 bytes_l11f8f6_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fbf0 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_11

def b_l11f8f6_9 : Block Op Label signature Reg.count 441 :=
  .letOp (n := 441) (.out 0x11fb9d (shldR64R64Effect 0x11fb9d 5 2 1 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[439, 436]
    (.letOp (n := 442) (.exec 0x11fb9d (fun s => s.RIP = 0x11fb9d) (shldR64R64Effect 0x11fb9d 5 2 1 12) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[439, 436]
    (.letOp (n := 443) (.out 0x11fba2 (andR64R64Effect 0x11fba2 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[436, 314]
    (.letOp (n := 444) (.exec 0x11fba2 (fun s => s.RIP = 0x11fba2) (andR64R64Effect 0x11fba2 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[436, 314]
    (.letOp (n := 445) (.exec 0x11fba5 (StorePre 0x11fba5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11fba5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11fba5 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[443, 4]
    (.letOp (n := 446) (.out 0x11fbaa (movR64Imm64Effect 0x11fbaa 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 447) (.exec 0x11fbaa (fun s => s.RIP = 0x11fbaa) (movR64Imm64Effect 0x11fbaa 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 448) (.out 0x11fbb4 (movR64M64Effect 0x11fbb4 1 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 449) (.exec 0x11fbb4 (LoadPre 0x11fbb4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11fbb4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fbb4 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 450) (.out 0x11fbb9 (andR64R64Effect 0x11fbb9 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[448, 446]
    (.letOp (n := 451) (.exec 0x11fbb9 (fun s => s.RIP = 0x11fbb9) (andR64R64Effect 0x11fbb9 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[448, 446]
    (.letOp (n := 452) (.out 0x11fbbc (addR64R64Effect 0x11fbbc 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[450, 441]
    (.letOp (n := 453) (.exec 0x11fbbc (fun s => s.RIP = 0x11fbbc) (addR64R64Effect 0x11fbbc 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[450, 441]
    (.letOp (n := 454) (.exec 0x11fbbf (StorePre 0x11fbbf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11fbbf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11fbbf 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[452, 4]
    (.letOp (n := 455) (.out 0x11fbc4 (movR64M64Effect 0x11fbc4 12 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 456) (.exec 0x11fbc4 (LoadPre 0x11fbc4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11fbc4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fbc4 12 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 457) (.out 0x11fbc9 (movR64R64Effect 0x11fbc9 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[455]
    (.letOp (n := 458) (.exec 0x11fbc9 (fun s => s.RIP = 0x11fbc9) (movR64R64Effect 0x11fbc9 0 12) (Reg.operands [.gpr 12] [])) #v[455]
    (.letOp (n := 459) (.out 0x11fbcc (movR64M64Effect 0x11fbcc 3 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 460) (.exec 0x11fbcc (LoadPre 0x11fbcc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11fbcc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fbcc 3 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 461) (.out 0x11fbd1 (mulR64Effect 0x11fbd1 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[459, 457]
    (.letOp (n := 462) (.out 0x11fbd1 (mulR64Effect 0x11fbd1 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[459, 457]
    (.letOp (n := 463) (.exec 0x11fbd1 (fun s => s.RIP = 0x11fbd1) (mulR64Effect 0x11fbd1 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[459, 457]
    (.letOp (n := 464) (.out 0x11fbd4 (movR64R64Effect 0x11fbd4 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[462]
    (.letOp (n := 465) (.exec 0x11fbd4 (fun s => s.RIP = 0x11fbd4) (movR64R64Effect 0x11fbd4 7 2) (Reg.operands [.gpr 2] [])) #v[462]
    (.letOp (n := 466) (.out 0x11fbd7 (movR64R64Effect 0x11fbd7 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[461]
    (.letOp (n := 467) (.exec 0x11fbd7 (fun s => s.RIP = 0x11fbd7) (movR64R64Effect 0x11fbd7 6 0) (Reg.operands [.gpr 0] [])) #v[461]
    (.letOp (n := 468) (.out 0x11fbda (movR64M64Effect 0x11fbda 13 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 469) (.exec 0x11fbda (LoadPre 0x11fbda (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11fbda + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fbda 13 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 470) (.out 0x11fbdf (movR64R64Effect 0x11fbdf 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[468]
    (.letOp (n := 471) (.exec 0x11fbdf (fun s => s.RIP = 0x11fbdf) (movR64R64Effect 0x11fbdf 0 13) (Reg.operands [.gpr 13] [])) #v[468]
    (.letOp (n := 472) (.out 0x11fbe2 (movR64M64Effect 0x11fbe2 15 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 473) (.exec 0x11fbe2 (LoadPre 0x11fbe2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11fbe2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fbe2 15 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 474) (.out 0x11fbe7 (mulR64Effect 0x11fbe7 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[472, 470]
    (.letOp (n := 475) (.out 0x11fbe7 (mulR64Effect 0x11fbe7 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[472, 470]
    (.letOp (n := 476) (.exec 0x11fbe7 (fun s => s.RIP = 0x11fbe7) (mulR64Effect 0x11fbe7 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[472, 470]
    (.letOp (n := 477) (.out 0x11fbea (movR64R64Effect 0x11fbea 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[474]
    (.letOp (n := 478) (.exec 0x11fbea (fun s => s.RIP = 0x11fbea) (movR64R64Effect 0x11fbea 9 0) (Reg.operands [.gpr 0] [])) #v[474]
    (.letOp (n := 479) (.out 0x11fbed (addR64R64Effect 0x11fbed 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[477, 466]
    (.letOp (n := 480) (.out 0x11fbed (addR64R64Effect 0x11fbed 9 6) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 6] []) (.flag .CF)) #v[477, 466]
    (.letOp (n := 481) (.exec 0x11fbed (fun s => s.RIP = 0x11fbed) (addR64R64Effect 0x11fbed 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[477, 466]
    (b_l11f8f6_10)))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_9 : List UInt8 :=
  [0x48, 0x0F, 0xA4, 0xCA, 0x0C, 0x4C, 0x21, 0xE1, 0x48, 0x89, 0x4C, 0x24, 0x68, 0x48, 0xB8, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x70, 0x48, 0x21, 0xC1, 0x48,
    0x01, 0xD1, 0x48, 0x89, 0x4C, 0x24, 0x70, 0x4C, 0x8B, 0x64, 0x24, 0x38, 0x4C, 0x89, 0xE0, 0x48,
    0x8B, 0x5C, 0x24, 0x50, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0xD7, 0x48, 0x89, 0xC6, 0x4C, 0x8B, 0x6C,
    0x24, 0x58, 0x4C, 0x89, 0xE8, 0x4C, 0x8B, 0x7C, 0x24, 0x30, 0x49, 0xF7, 0xE7, 0x49, 0x89, 0xC1,
    0x49, 0x01, 0xF1] ++ bytes_l11f8f6_10

theorem code_l11f8f6_9 : ∀ x ∈ codeRange 0x11fb9d bytes_l11f8f6_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fb9d 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_10

def b_l11f8f6_8 : Block Op Label signature Reg.count 397 :=
  .letOp (n := 397) (.out 0x11fb4d (addR64R64Effect 0x11fb4d 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[392, 383]
    (.letOp (n := 398) (.out 0x11fb4d (addR64R64Effect 0x11fb4d 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[392, 383]
    (.letOp (n := 399) (.exec 0x11fb4d (fun s => s.RIP = 0x11fb4d) (addR64R64Effect 0x11fb4d 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[392, 383]
    (.letOp (n := 400) (.out 0x11fb50 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fb50 6 9)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[395, 381, 398]
    (.letOp (n := 401) (.exec 0x11fb50 (fun s => s.RIP = 0x11fb50) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fb50 6 9)) (Reg.operands [.gpr 6, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[395, 381, 398]
    (.letOp (n := 402) (.out 0x11fb53 (addR64R64Effect 0x11fb53 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[397, 345]
    (.letOp (n := 403) (.out 0x11fb53 (addR64R64Effect 0x11fb53 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[397, 345]
    (.letOp (n := 404) (.exec 0x11fb53 (fun s => s.RIP = 0x11fb53) (addR64R64Effect 0x11fb53 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[397, 345]
    (.letOp (n := 405) (.out 0x11fb56 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fb56 6 15)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[400, 343, 403]
    (.letOp (n := 406) (.exec 0x11fb56 (fun s => s.RIP = 0x11fb56) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fb56 6 15)) (Reg.operands [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[400, 343, 403]
    (.letOp (n := 407) (.out 0x11fb59 (shldR64R64Effect 0x11fb59 5 8 10 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[370, 367]
    (.letOp (n := 408) (.exec 0x11fb59 (fun s => s.RIP = 0x11fb59) (shldR64R64Effect 0x11fb59 5 8 10 12) (Reg.operands [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[370, 367]
    (.letOp (n := 409) (.out 0x11fb5e (movR64R64Effect 0x11fb5e 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[405]
    (.letOp (n := 410) (.exec 0x11fb5e (fun s => s.RIP = 0x11fb5e) (movR64R64Effect 0x11fb5e 7 6) (Reg.operands [.gpr 6] [])) #v[405]
    (.letOp (n := 411) (.out 0x11fb61 (shrR64Effect 0x11fb61 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[409]
    (.letOp (n := 412) (.exec 0x11fb61 (fun s => s.RIP = 0x11fb61) (shrR64Effect 0x11fb61 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[409]
    (.letOp (n := 413) (.out 0x11fb65 (shldR64R64Effect 0x11fb65 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[405, 402]
    (.letOp (n := 414) (.exec 0x11fb65 (fun s => s.RIP = 0x11fb65) (shldR64R64Effect 0x11fb65 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[405, 402]
    (.letOp (n := 415) (.out 0x11fb6a (andR64R64Effect 0x11fb6a 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[402, 314]
    (.letOp (n := 416) (.exec 0x11fb6a (fun s => s.RIP = 0x11fb6a) (andR64R64Effect 0x11fb6a 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[402, 314]
    (.letOp (n := 417) (.exec 0x11fb6d (StorePre 0x11fb6d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11fb6d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11fb6d 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[415, 4]
    (.letOp (n := 418) (.out 0x11fb75 (movR64R64Effect 0x11fb75 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[407]
    (.letOp (n := 419) (.exec 0x11fb75 (fun s => s.RIP = 0x11fb75) (movR64R64Effect 0x11fb75 0 8) (Reg.operands [.gpr 8] [])) #v[407]
    (.letOp (n := 420) (.out 0x11fb78 (mulR64Effect 0x11fb78 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[376, 418]
    (.letOp (n := 421) (.out 0x11fb78 (mulR64Effect 0x11fb78 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[376, 418]
    (.letOp (n := 422) (.exec 0x11fb78 (fun s => s.RIP = 0x11fb78) (mulR64Effect 0x11fb78 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[376, 418]
    (.letOp (n := 423) (.out 0x11fb7b (movR64R64Effect 0x11fb7b 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 13] []) (.reg (.gpr 11))) #v[376]
    (.letOp (n := 424) (.exec 0x11fb7b (fun s => s.RIP = 0x11fb7b) (movR64R64Effect 0x11fb7b 11 13) (Reg.operands [.gpr 13] [])) #v[376]
    (.letOp (n := 425) (.out 0x11fb7e (movR64Imm64Effect 0x11fb7e 8 0xffffffffffffe) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 426) (.exec 0x11fb7e (fun s => s.RIP = 0x11fb7e) (movR64Imm64Effect 0x11fb7e 8 0xffffffffffffe) (Reg.operands [] [])) #v[]
    (.letOp (n := 427) (.out 0x11fb88 (movR64M64Effect 0x11fb88 1 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 428) (.exec 0x11fb88 (LoadPre 0x11fb88 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11fb88 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11fb88 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 429) (.out 0x11fb8d (andR64R64Effect 0x11fb8d 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[427, 425]
    (.letOp (n := 430) (.exec 0x11fb8d (fun s => s.RIP = 0x11fb8d) (andR64R64Effect 0x11fb8d 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[427, 425]
    (.letOp (n := 431) (.out 0x11fb90 (addR64R64Effect 0x11fb90 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[429, 420]
    (.letOp (n := 432) (.out 0x11fb90 (addR64R64Effect 0x11fb90 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[429, 420]
    (.letOp (n := 433) (.exec 0x11fb90 (fun s => s.RIP = 0x11fb90) (addR64R64Effect 0x11fb90 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[429, 420]
    (.letOp (n := 434) (.out 0x11fb93 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11fb93 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[421, 432]
    (.letOp (n := 435) (.exec 0x11fb93 (fun s => s.RIP = 0x11fb93) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11fb93 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[421, 432]
    (.letOp (n := 436) (.out 0x11fb97 (addR64R64Effect 0x11fb97 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[431, 413]
    (.letOp (n := 437) (.out 0x11fb97 (addR64R64Effect 0x11fb97 1 6) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 6] []) (.flag .CF)) #v[431, 413]
    (.letOp (n := 438) (.exec 0x11fb97 (fun s => s.RIP = 0x11fb97) (addR64R64Effect 0x11fb97 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[431, 413]
    (.letOp (n := 439) (.out 0x11fb9a (atFlags StatusFlags.CF (adcR64R64Effect 0x11fb9a 2 7)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[434, 411, 437]
    (.letOp (n := 440) (.exec 0x11fb9a (fun s => s.RIP = 0x11fb9a) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fb9a 2 7)) (Reg.operands [.gpr 2, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[434, 411, 437]
    (b_l11f8f6_9))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_8 : List UInt8 :=
  [0x4C, 0x01, 0xF0, 0x4C, 0x11, 0xCE, 0x48, 0x01, 0xF8, 0x4C, 0x11, 0xFE, 0x4D, 0x0F, 0xA4, 0xD0,
    0x0C, 0x48, 0x89, 0xF7, 0x48, 0xC1, 0xEF, 0x34, 0x48, 0x0F, 0xA4, 0xC6, 0x0C, 0x4C, 0x21, 0xE0,
    0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xC0, 0x49, 0xF7, 0xE5, 0x4D, 0x89,
    0xEB, 0x49, 0xB8, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x68,
    0x4C, 0x21, 0xC1, 0x48, 0x01, 0xC1, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x01, 0xF1, 0x48, 0x11, 0xFA] ++ bytes_l11f8f6_9

theorem code_l11f8f6_8 : ∀ x ∈ codeRange 0x11fb4d bytes_l11f8f6_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fb4d 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_9

def b_l11f8f6_7 : Block Op Label signature Reg.count 351 :=
  .letOp (n := 351) (.out 0x11fb10 (movR64R64Effect 0x11fb10 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[60]
    (.letOp (n := 352) (.exec 0x11fb10 (fun s => s.RIP = 0x11fb10) (movR64R64Effect 0x11fb10 0 13) (Reg.operands [.gpr 13] [])) #v[60]
    (.letOp (n := 353) (.out 0x11fb13 (mulR64Effect 0x11fb13 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[60, 351]
    (.letOp (n := 354) (.out 0x11fb13 (mulR64Effect 0x11fb13 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[60, 351]
    (.letOp (n := 355) (.exec 0x11fb13 (fun s => s.RIP = 0x11fb13) (mulR64Effect 0x11fb13 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[60, 351]
    (.letOp (n := 356) (.out 0x11fb16 (movR64R64Effect 0x11fb16 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[354]
    (.letOp (n := 357) (.exec 0x11fb16 (fun s => s.RIP = 0x11fb16) (movR64R64Effect 0x11fb16 11 2) (Reg.operands [.gpr 2] [])) #v[354]
    (.letOp (n := 358) (.out 0x11fb19 (movR64R64Effect 0x11fb19 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[353]
    (.letOp (n := 359) (.exec 0x11fb19 (fun s => s.RIP = 0x11fb19) (movR64R64Effect 0x11fb19 3 0) (Reg.operands [.gpr 0] [])) #v[353]
    (.letOp (n := 360) (.out 0x11fb1c (movR64R64Effect 0x11fb1c 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[292]
    (.letOp (n := 361) (.exec 0x11fb1c (fun s => s.RIP = 0x11fb1c) (movR64R64Effect 0x11fb1c 0 10) (Reg.operands [.gpr 10] [])) #v[292]
    (.letOp (n := 362) (.out 0x11fb1f (mulR64Effect 0x11fb1f 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[70, 360]
    (.letOp (n := 363) (.out 0x11fb1f (mulR64Effect 0x11fb1f 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[70, 360]
    (.letOp (n := 364) (.exec 0x11fb1f (fun s => s.RIP = 0x11fb1f) (mulR64Effect 0x11fb1f 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[70, 360]
    (.letOp (n := 365) (.out 0x11fb22 (movR64R64Effect 0x11fb22 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[362]
    (.letOp (n := 366) (.exec 0x11fb22 (fun s => s.RIP = 0x11fb22) (movR64R64Effect 0x11fb22 10 0) (Reg.operands [.gpr 0] [])) #v[362]
    (.letOp (n := 367) (.out 0x11fb25 (addR64R64Effect 0x11fb25 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[365, 337]
    (.letOp (n := 368) (.out 0x11fb25 (addR64R64Effect 0x11fb25 10 9) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 9] []) (.flag .CF)) #v[365, 337]
    (.letOp (n := 369) (.exec 0x11fb25 (fun s => s.RIP = 0x11fb25) (addR64R64Effect 0x11fb25 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[365, 337]
    (.letOp (n := 370) (.out 0x11fb28 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fb28 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[339, 363, 368]
    (.letOp (n := 371) (.exec 0x11fb28 (fun s => s.RIP = 0x11fb28) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fb28 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[339, 363, 368]
    (.letOp (n := 372) (.out 0x11fb2b (movR64R64Effect 0x11fb2b 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[367]
    (.letOp (n := 373) (.exec 0x11fb2b (fun s => s.RIP = 0x11fb2b) (movR64R64Effect 0x11fb2b 0 10) (Reg.operands [.gpr 10] [])) #v[367]
    (.letOp (n := 374) (.out 0x11fb2e (andR64R64Effect 0x11fb2e 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[372, 314]
    (.letOp (n := 375) (.exec 0x11fb2e (fun s => s.RIP = 0x11fb2e) (andR64R64Effect 0x11fb2e 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[372, 314]
    (.letOp (n := 376) (.out 0x11fb31 (movR64R64Effect 0x11fb31 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[318]
    (.letOp (n := 377) (.exec 0x11fb31 (fun s => s.RIP = 0x11fb31) (movR64R64Effect 0x11fb31 13 6) (Reg.operands [.gpr 6] [])) #v[318]
    (.letOp (n := 378) (.out 0x11fb34 (mulR64Effect 0x11fb34 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[318, 374]
    (.letOp (n := 379) (.out 0x11fb34 (mulR64Effect 0x11fb34 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[318, 374]
    (.letOp (n := 380) (.exec 0x11fb34 (fun s => s.RIP = 0x11fb34) (mulR64Effect 0x11fb34 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[318, 374]
    (.letOp (n := 381) (.out 0x11fb37 (movR64R64Effect 0x11fb37 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[379]
    (.letOp (n := 382) (.exec 0x11fb37 (fun s => s.RIP = 0x11fb37) (movR64R64Effect 0x11fb37 9 2) (Reg.operands [.gpr 2] [])) #v[379]
    (.letOp (n := 383) (.out 0x11fb3a (movR64R64Effect 0x11fb3a 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[378]
    (.letOp (n := 384) (.exec 0x11fb3a (fun s => s.RIP = 0x11fb3a) (movR64R64Effect 0x11fb3a 14 0) (Reg.operands [.gpr 0] [])) #v[378]
    (.letOp (n := 385) (.out 0x11fb3d (movR64M64Effect 0x11fb3d 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 386) (.exec 0x11fb3d (LoadPre 0x11fb3d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11fb3d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11fb3d 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 387) (.out 0x11fb41 (mulR64Effect 0x11fb41 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[127, 385]
    (.letOp (n := 388) (.out 0x11fb41 (mulR64Effect 0x11fb41 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[127, 385]
    (.letOp (n := 389) (.exec 0x11fb41 (fun s => s.RIP = 0x11fb41) (mulR64Effect 0x11fb41 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[127, 385]
    (.letOp (n := 390) (.out 0x11fb44 (movR64R64Effect 0x11fb44 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[388]
    (.letOp (n := 391) (.exec 0x11fb44 (fun s => s.RIP = 0x11fb44) (movR64R64Effect 0x11fb44 6 2) (Reg.operands [.gpr 2] [])) #v[388]
    (.letOp (n := 392) (.out 0x11fb47 (addR64R64Effect 0x11fb47 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[387, 358]
    (.letOp (n := 393) (.out 0x11fb47 (addR64R64Effect 0x11fb47 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[387, 358]
    (.letOp (n := 394) (.exec 0x11fb47 (fun s => s.RIP = 0x11fb47) (addR64R64Effect 0x11fb47 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[387, 358]
    (.letOp (n := 395) (.out 0x11fb4a (atFlags StatusFlags.CF (adcR64R64Effect 0x11fb4a 6 11)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[390, 356, 393]
    (.letOp (n := 396) (.exec 0x11fb4a (fun s => s.RIP = 0x11fb4a) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fb4a 6 11)) (Reg.operands [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[390, 356, 393]
    (b_l11f8f6_8))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_7 : List UInt8 :=
  [0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC3, 0x4C, 0x89, 0xD0, 0x48,
    0xF7, 0xE5, 0x49, 0x89, 0xC2, 0x4D, 0x01, 0xCA, 0x49, 0x11, 0xD0, 0x4C, 0x89, 0xD0, 0x4C, 0x21,
    0xE0, 0x49, 0x89, 0xF5, 0x48, 0xF7, 0xE6, 0x49, 0x89, 0xD1, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0x04,
    0x24, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD6, 0x48, 0x01, 0xD8, 0x4C, 0x11, 0xDE] ++ bytes_l11f8f6_8

theorem code_l11f8f6_7 : ∀ x ∈ codeRange 0x11fb10 bytes_l11f8f6_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fb10 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_8

def b_l11f8f6_6 : Block Op Label signature Reg.count 310 :=
  .letOp (n := 310) (.out 0x11fabc (atFlags StatusFlags.CF (adcR64R64Effect 0x11fabc 9 12)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[305, 241, 308]
    (.letOp (n := 311) (.exec 0x11fabc (fun s => s.RIP = 0x11fabc) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fabc 9 12)) (Reg.operands [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[305, 241, 308]
    (.letOp (n := 312) (.out 0x11fabf (movR64R64Effect 0x11fabf 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[307]
    (.letOp (n := 313) (.exec 0x11fabf (fun s => s.RIP = 0x11fabf) (movR64R64Effect 0x11fabf 0 14) (Reg.operands [.gpr 14] [])) #v[307]
    (.letOp (n := 314) (.out 0x11fac2 (movR64R64Effect 0x11fac2 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[267]
    (.letOp (n := 315) (.exec 0x11fac2 (fun s => s.RIP = 0x11fac2) (movR64R64Effect 0x11fac2 12 6) (Reg.operands [.gpr 6] [])) #v[267]
    (.letOp (n := 316) (.out 0x11fac5 (andR64R64Effect 0x11fac5 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[312, 267]
    (.letOp (n := 317) (.exec 0x11fac5 (fun s => s.RIP = 0x11fac5) (andR64R64Effect 0x11fac5 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[312, 267]
    (.letOp (n := 318) (.out 0x11fac8 (movR64Imm64Effect 0x11fac8 6 0x1000003d10) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 319) (.exec 0x11fac8 (fun s => s.RIP = 0x11fac8) (movR64Imm64Effect 0x11fac8 6 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 320) (.out 0x11fad2 (mulR64Effect 0x11fad2 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[318, 316]
    (.letOp (n := 321) (.out 0x11fad2 (mulR64Effect 0x11fad2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[318, 316]
    (.letOp (n := 322) (.exec 0x11fad2 (fun s => s.RIP = 0x11fad2) (mulR64Effect 0x11fad2 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[318, 316]
    (.letOp (n := 323) (.out 0x11fad5 (movR64R64Effect 0x11fad5 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[321]
    (.letOp (n := 324) (.exec 0x11fad5 (fun s => s.RIP = 0x11fad5) (movR64R64Effect 0x11fad5 7 2) (Reg.operands [.gpr 2] [])) #v[321]
    (.letOp (n := 325) (.out 0x11fad8 (addR64R64Effect 0x11fad8 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[320, 280]
    (.letOp (n := 326) (.out 0x11fad8 (addR64R64Effect 0x11fad8 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[320, 280]
    (.letOp (n := 327) (.exec 0x11fad8 (fun s => s.RIP = 0x11fad8) (addR64R64Effect 0x11fad8 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[320, 280]
    (.letOp (n := 328) (.out 0x11fadb (atFlags StatusFlags.CF (adcR64R64Effect 0x11fadb 7 11)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[323, 278, 326]
    (.letOp (n := 329) (.exec 0x11fadb (fun s => s.RIP = 0x11fadb) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fadb 7 11)) (Reg.operands [.gpr 7, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[323, 278, 326]
    (.letOp (n := 330) (.out 0x11fade (addR64R64Effect 0x11fade 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[325, 265]
    (.letOp (n := 331) (.out 0x11fade (addR64R64Effect 0x11fade 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[325, 265]
    (.letOp (n := 332) (.exec 0x11fade (fun s => s.RIP = 0x11fade) (addR64R64Effect 0x11fade 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[325, 265]
    (.letOp (n := 333) (.out 0x11fae1 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11fae1 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[328, 331]
    (.letOp (n := 334) (.exec 0x11fae1 (fun s => s.RIP = 0x11fae1) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11fae1 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[328, 331]
    (.letOp (n := 335) (.out 0x11fae5 (movR64R64Effect 0x11fae5 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[310]
    (.letOp (n := 336) (.exec 0x11fae5 (fun s => s.RIP = 0x11fae5) (movR64R64Effect 0x11fae5 8 9) (Reg.operands [.gpr 9] [])) #v[310]
    (.letOp (n := 337) (.out 0x11fae8 (shldR64R64Effect 0x11fae8 5 9 14 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[310, 307]
    (.letOp (n := 338) (.exec 0x11fae8 (fun s => s.RIP = 0x11fae8) (shldR64R64Effect 0x11fae8 5 9 14 12) (Reg.operands [.gpr 9, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[310, 307]
    (.letOp (n := 339) (.out 0x11faed (shrR64Effect 0x11faed 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[335]
    (.letOp (n := 340) (.exec 0x11faed (fun s => s.RIP = 0x11faed) (shrR64Effect 0x11faed 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[335]
    (.letOp (n := 341) (.out 0x11faf1 (movR64R64Effect 0x11faf1 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[333]
    (.letOp (n := 342) (.exec 0x11faf1 (fun s => s.RIP = 0x11faf1) (movR64R64Effect 0x11faf1 15 7) (Reg.operands [.gpr 7] [])) #v[333]
    (.letOp (n := 343) (.out 0x11faf4 (shrR64Effect 0x11faf4 4 15 52) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[341]
    (.letOp (n := 344) (.exec 0x11faf4 (fun s => s.RIP = 0x11faf4) (shrR64Effect 0x11faf4 4 15 52) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[341]
    (.letOp (n := 345) (.out 0x11faf8 (shldR64R64Effect 0x11faf8 5 7 0 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[333, 330]
    (.letOp (n := 346) (.exec 0x11faf8 (fun s => s.RIP = 0x11faf8) (shldR64R64Effect 0x11faf8 5 7 0 12) (Reg.operands [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[333, 330]
    (.letOp (n := 347) (.out 0x11fafd (andR64R64Effect 0x11fafd 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[330, 314]
    (.letOp (n := 348) (.exec 0x11fafd (fun s => s.RIP = 0x11fafd) (andR64R64Effect 0x11fafd 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[330, 314]
    (.letOp (n := 349) (.exec 0x11fb00 (StorePre 0x11fb00 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11fb00 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11fb00 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[347, 4]
    (.letOp (n := 350) (.exec 0x11fb08 (StorePre 0x11fb08 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11fb08 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11fb08 13 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[60, 4]
    (b_l11f8f6_7)))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_6 : List UInt8 :=
  [0x4D, 0x11, 0xE1, 0x4C, 0x89, 0xF0, 0x49, 0x89, 0xF4, 0x48, 0x21, 0xF0, 0x48, 0xBE, 0x10, 0x3D,
    0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE6, 0x48, 0x89, 0xD7, 0x48, 0x01, 0xD8, 0x4C,
    0x11, 0xDF, 0x4C, 0x01, 0xC0, 0x48, 0x83, 0xD7, 0x00, 0x4D, 0x89, 0xC8, 0x4D, 0x0F, 0xA4, 0xF1,
    0x0C, 0x49, 0xC1, 0xE8, 0x34, 0x49, 0x89, 0xFF, 0x49, 0xC1, 0xEF, 0x34, 0x48, 0x0F, 0xA4, 0xC7,
    0x0C, 0x4C, 0x21, 0xE0, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xAC, 0x24,
    0xA8, 0x00, 0x00, 0x00] ++ bytes_l11f8f6_7

theorem code_l11f8f6_6 : ∀ x ∈ codeRange 0x11fabc bytes_l11f8f6_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fabc 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_7

def b_l11f8f6_5 : Block Op Label signature Reg.count 269 :=
  .letOp (n := 269) (.out 0x11fa6e (andR64R64Effect 0x11fa6e 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[260, 267]
    (.letOp (n := 270) (.exec 0x11fa6e (fun s => s.RIP = 0x11fa6e) (andR64R64Effect 0x11fa6e 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[260, 267]
    (.letOp (n := 271) (.exec 0x11fa71 (StorePre 0x11fa71 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11fa71 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11fa71 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[269, 4]
    (.letOp (n := 272) (.out 0x11fa79 (leaR64Effect 0x11fa79 0 (.sib 15 (some 15) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 15] []) (.reg (.gpr 0))) #v[58, 58]
    (.letOp (n := 273) (.exec 0x11fa79 (fun s => s.RIP = 0x11fa79) (leaR64Effect 0x11fa79 0 (.sib 15 (some 15) 0 .none)) (Reg.operands [.gpr 15, .gpr 15] [])) #v[58, 58]
    (.letOp (n := 274) (.exec 0x11fa7d (StorePre 0x11fa7d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11fa7d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11fa7d 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[272, 4]
    (.letOp (n := 275) (.out 0x11fa81 (mulR64Effect 0x11fa81 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[60, 272]
    (.letOp (n := 276) (.out 0x11fa81 (mulR64Effect 0x11fa81 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[60, 272]
    (.letOp (n := 277) (.exec 0x11fa81 (fun s => s.RIP = 0x11fa81) (mulR64Effect 0x11fa81 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[60, 272]
    (.letOp (n := 278) (.out 0x11fa84 (movR64R64Effect 0x11fa84 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[276]
    (.letOp (n := 279) (.exec 0x11fa84 (fun s => s.RIP = 0x11fa84) (movR64R64Effect 0x11fa84 11 2) (Reg.operands [.gpr 2] [])) #v[276]
    (.letOp (n := 280) (.out 0x11fa87 (movR64R64Effect 0x11fa87 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[275]
    (.letOp (n := 281) (.exec 0x11fa87 (fun s => s.RIP = 0x11fa87) (movR64R64Effect 0x11fa87 3 0) (Reg.operands [.gpr 0] [])) #v[275]
    (.letOp (n := 282) (.out 0x11fa8a (movR64R64Effect 0x11fa8a 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 283) (.exec 0x11fa8a (fun s => s.RIP = 0x11fa8a) (movR64R64Effect 0x11fa8a 0 5) (Reg.operands [.gpr 5] [])) #v[70]
    (.letOp (n := 284) (.out 0x11fa8d (mulR64Effect 0x11fa8d 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[70, 282]
    (.letOp (n := 285) (.out 0x11fa8d (mulR64Effect 0x11fa8d 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[70, 282]
    (.letOp (n := 286) (.exec 0x11fa8d (fun s => s.RIP = 0x11fa8d) (mulR64Effect 0x11fa8d 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[70, 282]
    (.letOp (n := 287) (.exec 0x11fa90 (StorePre 0x11fa90 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11fa90 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11fa90 5 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 288) (.out 0x11fa98 (movR64R64Effect 0x11fa98 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[284]
    (.letOp (n := 289) (.exec 0x11fa98 (fun s => s.RIP = 0x11fa98) (movR64R64Effect 0x11fa98 15 0) (Reg.operands [.gpr 0] [])) #v[284]
    (.letOp (n := 290) (.out 0x11fa9b (movR64R64Effect 0x11fa9b 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[285]
    (.letOp (n := 291) (.exec 0x11fa9b (fun s => s.RIP = 0x11fa9b) (movR64R64Effect 0x11fa9b 9 2) (Reg.operands [.gpr 2] [])) #v[285]
    (.letOp (n := 292) (.out 0x11fa9e (leaR64Effect 0x11fa9e 10 (.sib 14 (some 14) 0 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14, .gpr 14] []) (.reg (.gpr 10))) #v[62, 62]
    (.letOp (n := 293) (.exec 0x11fa9e (fun s => s.RIP = 0x11fa9e) (leaR64Effect 0x11fa9e 10 (.sib 14 (some 14) 0 .none)) (Reg.operands [.gpr 14, .gpr 14] [])) #v[62, 62]
    (.letOp (n := 294) (.out 0x11faa2 (movR64R64Effect 0x11faa2 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[292]
    (.letOp (n := 295) (.exec 0x11faa2 (fun s => s.RIP = 0x11faa2) (movR64R64Effect 0x11faa2 0 10) (Reg.operands [.gpr 10] [])) #v[292]
    (.letOp (n := 296) (.exec 0x11faa5 (StorePre 0x11faa5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11faa5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11faa5 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[127, 4]
    (.letOp (n := 297) (.out 0x11faad (mulR64Effect 0x11faad 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[127, 294]
    (.letOp (n := 298) (.out 0x11faad (mulR64Effect 0x11faad 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[127, 294]
    (.letOp (n := 299) (.exec 0x11faad (fun s => s.RIP = 0x11faad) (mulR64Effect 0x11faad 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[127, 294]
    (.letOp (n := 300) (.out 0x11fab0 (movR64R64Effect 0x11fab0 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[297]
    (.letOp (n := 301) (.exec 0x11fab0 (fun s => s.RIP = 0x11fab0) (movR64R64Effect 0x11fab0 14 0) (Reg.operands [.gpr 0] [])) #v[297]
    (.letOp (n := 302) (.out 0x11fab3 (addR64R64Effect 0x11fab3 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[300, 288]
    (.letOp (n := 303) (.out 0x11fab3 (addR64R64Effect 0x11fab3 14 15) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 15] []) (.flag .CF)) #v[300, 288]
    (.letOp (n := 304) (.exec 0x11fab3 (fun s => s.RIP = 0x11fab3) (addR64R64Effect 0x11fab3 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[300, 288]
    (.letOp (n := 305) (.out 0x11fab6 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fab6 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[290, 298, 303]
    (.letOp (n := 306) (.exec 0x11fab6 (fun s => s.RIP = 0x11fab6) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fab6 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[290, 298, 303]
    (.letOp (n := 307) (.out 0x11fab9 (addR64R64Effect 0x11fab9 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[302, 243]
    (.letOp (n := 308) (.out 0x11fab9 (addR64R64Effect 0x11fab9 14 7) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 7] []) (.flag .CF)) #v[302, 243]
    (.letOp (n := 309) (.exec 0x11fab9 (fun s => s.RIP = 0x11fab9) (addR64R64Effect 0x11fab9 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[302, 243]
    (b_l11f8f6_6)))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_5 : List UInt8 :=
  [0x48, 0x21, 0xF0, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4B, 0x8D, 0x04, 0x3F, 0x48,
    0x89, 0x04, 0x24, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC3, 0x48, 0x89, 0xE8, 0x48,
    0xF7, 0xE5, 0x48, 0x89, 0xAC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC7, 0x49, 0x89, 0xD1,
    0x4F, 0x8D, 0x14, 0x36, 0x4C, 0x89, 0xD0, 0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE1, 0x49, 0x89, 0xC6, 0x4D, 0x01, 0xFE, 0x49, 0x11, 0xD1, 0x49, 0x01, 0xFE] ++ bytes_l11f8f6_6

theorem code_l11f8f6_5 : ∀ x ∈ codeRange 0x11fa6e bytes_l11f8f6_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fa6e 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_6

def b_l11f8f6_4 : Block Op Label signature Reg.count 225 :=
  .letOp (n := 225) (.out 0x11fa15 (addR64R64Effect 0x11fa15 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[222, 217]
    (.letOp (n := 226) (.out 0x11fa15 (addR64R64Effect 0x11fa15 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[222, 217]
    (.letOp (n := 227) (.exec 0x11fa15 (fun s => s.RIP = 0x11fa15) (addR64R64Effect 0x11fa15 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[222, 217]
    (.letOp (n := 228) (.out 0x11fa18 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fa18 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[215, 223, 226]
    (.letOp (n := 229) (.exec 0x11fa18 (fun s => s.RIP = 0x11fa18) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fa18 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[215, 223, 226]
    (.letOp (n := 230) (.out 0x11fa1b (shldR64R64Effect 0x11fa1b 5 7 0 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[228, 225]
    (.letOp (n := 231) (.exec 0x11fa1b (fun s => s.RIP = 0x11fa1b) (shldR64R64Effect 0x11fa1b 5 7 0 1) (Reg.operands [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[228, 225]
    (.letOp (n := 232) (.out 0x11fa20 (addR64R64Effect 0x11fa20 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[225, 225]
    (.letOp (n := 233) (.exec 0x11fa20 (fun s => s.RIP = 0x11fa20) (addR64R64Effect 0x11fa20 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[225, 225]
    (.letOp (n := 234) (.out 0x11fa23 (addR64R64Effect 0x11fa23 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[232, 192]
    (.letOp (n := 235) (.out 0x11fa23 (addR64R64Effect 0x11fa23 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[232, 192]
    (.letOp (n := 236) (.exec 0x11fa23 (fun s => s.RIP = 0x11fa23) (addR64R64Effect 0x11fa23 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[232, 192]
    (.letOp (n := 237) (.out 0x11fa26 (atFlags StatusFlags.CF (adcR64R64Effect 0x11fa26 7 3)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[230, 190, 235]
    (.letOp (n := 238) (.exec 0x11fa26 (fun s => s.RIP = 0x11fa26) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fa26 7 3)) (Reg.operands [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[230, 190, 235]
    (.letOp (n := 239) (.out 0x11fa29 (movR64R64Effect 0x11fa29 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 7] []) (.reg (.gpr 12))) #v[237]
    (.letOp (n := 240) (.exec 0x11fa29 (fun s => s.RIP = 0x11fa29) (movR64R64Effect 0x11fa29 12 7) (Reg.operands [.gpr 7] [])) #v[237]
    (.letOp (n := 241) (.out 0x11fa2c (shrR64Effect 0x11fa2c 4 12 52) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[239]
    (.letOp (n := 242) (.exec 0x11fa2c (fun s => s.RIP = 0x11fa2c) (shrR64Effect 0x11fa2c 4 12 52) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[239]
    (.letOp (n := 243) (.out 0x11fa30 (shldR64R64Effect 0x11fa30 5 7 0 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[237, 234]
    (.letOp (n := 244) (.exec 0x11fa30 (fun s => s.RIP = 0x11fa30) (shldR64R64Effect 0x11fa30 5 7 0 12) (Reg.operands [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[237, 234]
    (.letOp (n := 245) (.out 0x11fa35 (shlR64Effect 0x11fa35 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[234]
    (.letOp (n := 246) (.exec 0x11fa35 (fun s => s.RIP = 0x11fa35) (shlR64Effect 0x11fa35 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[234]
    (.letOp (n := 247) (.out 0x11fa39 (movR64Imm64Effect 0x11fa39 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 248) (.exec 0x11fa39 (fun s => s.RIP = 0x11fa39) (movR64Imm64Effect 0x11fa39 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 249) (.out 0x11fa43 (andR64R64Effect 0x11fa43 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[245, 247]
    (.letOp (n := 250) (.exec 0x11fa43 (fun s => s.RIP = 0x11fa43) (andR64R64Effect 0x11fa43 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[245, 247]
    (.letOp (n := 251) (.out 0x11fa46 (orR64R64Effect 0x11fa46 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[249, 208]
    (.letOp (n := 252) (.exec 0x11fa46 (fun s => s.RIP = 0x11fa46) (orR64R64Effect 0x11fa46 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[249, 208]
    (.letOp (n := 253) (.out 0x11fa49 (movR64Imm64Effect 0x11fa49 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 254) (.exec 0x11fa49 (fun s => s.RIP = 0x11fa49) (movR64Imm64Effect 0x11fa49 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 255) (.out 0x11fa53 (mulR64Effect 0x11fa53 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[253, 251]
    (.letOp (n := 256) (.out 0x11fa53 (mulR64Effect 0x11fa53 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[253, 251]
    (.letOp (n := 257) (.exec 0x11fa53 (fun s => s.RIP = 0x11fa53) (mulR64Effect 0x11fa53 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[253, 251]
    (.letOp (n := 258) (.out 0x11fa56 (movR64R64Effect 0x11fa56 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[256]
    (.letOp (n := 259) (.exec 0x11fa56 (fun s => s.RIP = 0x11fa56) (movR64R64Effect 0x11fa56 8 2) (Reg.operands [.gpr 2] [])) #v[256]
    (.letOp (n := 260) (.out 0x11fa59 (addR64R64Effect 0x11fa59 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[255, 204]
    (.letOp (n := 261) (.out 0x11fa59 (addR64R64Effect 0x11fa59 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[255, 204]
    (.letOp (n := 262) (.exec 0x11fa59 (fun s => s.RIP = 0x11fa59) (addR64R64Effect 0x11fa59 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[255, 204]
    (.letOp (n := 263) (.out 0x11fa5c (atFlags StatusFlags.CF (adcR64R64Effect 0x11fa5c 8 9)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[258, 206, 261]
    (.letOp (n := 264) (.exec 0x11fa5c (fun s => s.RIP = 0x11fa5c) (atFlags StatusFlags.CF (adcR64R64Effect 0x11fa5c 8 9)) (Reg.operands [.gpr 8, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[258, 206, 261]
    (.letOp (n := 265) (.out 0x11fa5f (shldR64R64Effect 0x11fa5f 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[263, 260]
    (.letOp (n := 266) (.exec 0x11fa5f (fun s => s.RIP = 0x11fa5f) (shldR64R64Effect 0x11fa5f 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[263, 260]
    (.letOp (n := 267) (.out 0x11fa64 (movR64Imm64Effect 0x11fa64 6 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 268) (.exec 0x11fa64 (fun s => s.RIP = 0x11fa64) (movR64Imm64Effect 0x11fa64 6 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (b_l11f8f6_5))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_4 : List UInt8 :=
  [0x4C, 0x01, 0xC0, 0x48, 0x11, 0xD7, 0x48, 0x0F, 0xA4, 0xC7, 0x01, 0x48, 0x01, 0xC0, 0x48, 0x01,
    0xF0, 0x48, 0x11, 0xDF, 0x49, 0x89, 0xFC, 0x49, 0xC1, 0xEC, 0x34, 0x48, 0x0F, 0xA4, 0xC7, 0x0C,
    0x48, 0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21,
    0xD0, 0x4C, 0x09, 0xD8, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7,
    0xE2, 0x49, 0x89, 0xD0, 0x4C, 0x01, 0xD0, 0x4D, 0x11, 0xC8, 0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x48,
    0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] ++ bytes_l11f8f6_5

theorem code_l11f8f6_4 : ∀ x ∈ codeRange 0x11fa15 bytes_l11f8f6_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fa15 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_5

def b_l11f8f6_3 : Block Op Label signature Reg.count 185 :=
  .letOp (n := 185) (.exec 0x11f9c8 (StorePre 0x11f9c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11f9c8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f9c8 12 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[182, 4]
    (.letOp (n := 186) (.out 0x11f9cd (atFlags StatusFlags.CF (adcR64R64Effect 0x11f9cd 6 3)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[180, 161, 183]
    (.letOp (n := 187) (.exec 0x11f9cd (fun s => s.RIP = 0x11f9cd) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f9cd 6 3)) (Reg.operands [.gpr 6, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[180, 161, 183]
    (.letOp (n := 188) (.out 0x11f9d0 (movR64R64Effect 0x11f9d0 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[186]
    (.letOp (n := 189) (.exec 0x11f9d0 (fun s => s.RIP = 0x11f9d0) (movR64R64Effect 0x11f9d0 3 6) (Reg.operands [.gpr 6] [])) #v[186]
    (.letOp (n := 190) (.out 0x11f9d3 (shrR64Effect 0x11f9d3 4 3 52) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[188]
    (.letOp (n := 191) (.exec 0x11f9d3 (fun s => s.RIP = 0x11f9d3) (shrR64Effect 0x11f9d3 4 3 52) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[188]
    (.letOp (n := 192) (.out 0x11f9d7 (shldR64R64Effect 0x11f9d7 5 6 12 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[186, 182]
    (.letOp (n := 193) (.exec 0x11f9d7 (fun s => s.RIP = 0x11f9d7) (shldR64R64Effect 0x11f9d7 5 6 12 12) (Reg.operands [.gpr 6, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[186, 182]
    (.letOp (n := 194) (.out 0x11f9dc (movR64R64Effect 0x11f9dc 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 12] []) (.reg (.gpr 11))) #v[182]
    (.letOp (n := 195) (.exec 0x11f9dc (fun s => s.RIP = 0x11f9dc) (movR64R64Effect 0x11f9dc 11 12) (Reg.operands [.gpr 12] [])) #v[182]
    (.letOp (n := 196) (.out 0x11f9df (shrR64Effect 0x11f9df 4 11 48) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[194]
    (.letOp (n := 197) (.exec 0x11f9df (fun s => s.RIP = 0x11f9df) (shrR64Effect 0x11f9df 4 11 48) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[194]
    (.letOp (n := 198) (.out 0x11f9e3 (movR64R64Effect 0x11f9e3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[58]
    (.letOp (n := 199) (.exec 0x11f9e3 (fun s => s.RIP = 0x11f9e3) (movR64R64Effect 0x11f9e3 0 15) (Reg.operands [.gpr 15] [])) #v[58]
    (.letOp (n := 200) (.out 0x11f9e6 (mulR64Effect 0x11f9e6 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[58, 198]
    (.letOp (n := 201) (.out 0x11f9e6 (mulR64Effect 0x11f9e6 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[58, 198]
    (.letOp (n := 202) (.exec 0x11f9e6 (fun s => s.RIP = 0x11f9e6) (mulR64Effect 0x11f9e6 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[58, 198]
    (.letOp (n := 203) (.exec 0x11f9e9 (StorePre 0x11f9e9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11f9e9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11f9e9 15 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 204) (.out 0x11f9f1 (movR64R64Effect 0x11f9f1 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[200]
    (.letOp (n := 205) (.exec 0x11f9f1 (fun s => s.RIP = 0x11f9f1) (movR64R64Effect 0x11f9f1 10 0) (Reg.operands [.gpr 0] [])) #v[200]
    (.letOp (n := 206) (.out 0x11f9f4 (movR64R64Effect 0x11f9f4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[201]
    (.letOp (n := 207) (.exec 0x11f9f4 (fun s => s.RIP = 0x11f9f4) (movR64R64Effect 0x11f9f4 9 2) (Reg.operands [.gpr 2] [])) #v[201]
    (.letOp (n := 208) (.out 0x11f9f7 (andR32Imm8Effect 0x11f9f7 4 11 0xf) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[196]
    (.letOp (n := 209) (.exec 0x11f9f7 (fun s => s.RIP = 0x11f9f7) (andR32Imm8Effect 0x11f9f7 4 11 0xf) (Reg.operands [.gpr 11] [])) #v[196]
    (.letOp (n := 210) (.out 0x11f9fb (movR64R64Effect 0x11f9fb 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 211) (.exec 0x11f9fb (fun s => s.RIP = 0x11f9fb) (movR64R64Effect 0x11f9fb 0 5) (Reg.operands [.gpr 5] [])) #v[70]
    (.letOp (n := 212) (.out 0x11f9fe (mulR64Effect 0x11f9fe 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[127, 210]
    (.letOp (n := 213) (.out 0x11f9fe (mulR64Effect 0x11f9fe 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[127, 210]
    (.letOp (n := 214) (.exec 0x11f9fe (fun s => s.RIP = 0x11f9fe) (mulR64Effect 0x11f9fe 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[127, 210]
    (.letOp (n := 215) (.out 0x11fa01 (movR64R64Effect 0x11fa01 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[213]
    (.letOp (n := 216) (.exec 0x11fa01 (fun s => s.RIP = 0x11fa01) (movR64R64Effect 0x11fa01 7 2) (Reg.operands [.gpr 2] [])) #v[213]
    (.letOp (n := 217) (.out 0x11fa04 (movR64R64Effect 0x11fa04 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[212]
    (.letOp (n := 218) (.exec 0x11fa04 (fun s => s.RIP = 0x11fa04) (movR64R64Effect 0x11fa04 8 0) (Reg.operands [.gpr 0] [])) #v[212]
    (.letOp (n := 219) (.out 0x11fa07 (movR64R64Effect 0x11fa07 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[62]
    (.letOp (n := 220) (.exec 0x11fa07 (fun s => s.RIP = 0x11fa07) (movR64R64Effect 0x11fa07 0 14) (Reg.operands [.gpr 14] [])) #v[62]
    (.letOp (n := 221) (.exec 0x11fa0a (StorePre 0x11fa0a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11fa0a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11fa0a 14 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 222) (.out 0x11fa12 (mulR64Effect 0x11fa12 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[60, 219]
    (.letOp (n := 223) (.out 0x11fa12 (mulR64Effect 0x11fa12 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[60, 219]
    (.letOp (n := 224) (.exec 0x11fa12 (fun s => s.RIP = 0x11fa12) (mulR64Effect 0x11fa12 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[60, 219]
    (b_l11f8f6_4))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_3 : List UInt8 :=
  [0x4C, 0x89, 0x64, 0x24, 0x70, 0x48, 0x11, 0xDE, 0x48, 0x89, 0xF3, 0x48, 0xC1, 0xEB, 0x34, 0x4C,
    0x0F, 0xA4, 0xE6, 0x0C, 0x4D, 0x89, 0xE3, 0x49, 0xC1, 0xEB, 0x30, 0x4C, 0x89, 0xF8, 0x49, 0xF7,
    0xE7, 0x4C, 0x89, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC2, 0x49, 0x89, 0xD1, 0x41,
    0x83, 0xE3, 0x0F, 0x48, 0x89, 0xE8, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC0, 0x4C,
    0x89, 0xF0, 0x4C, 0x89, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5] ++ bytes_l11f8f6_4

theorem code_l11f8f6_3 : ∀ x ∈ codeRange 0x11f9c8 bytes_l11f8f6_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f9c8 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_4

def b_l11f8f6_2 : Block Op Label signature Reg.count 138 :=
  .letOp (n := 138) (.out 0x11f989 (movR64R64Effect 0x11f989 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[106]
    (.letOp (n := 139) (.exec 0x11f989 (fun s => s.RIP = 0x11f989) (movR64R64Effect 0x11f989 0 9) (Reg.operands [.gpr 9] [])) #v[106]
    (.letOp (n := 140) (.out 0x11f98c (mulR64Effect 0x11f98c 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[110, 138]
    (.letOp (n := 141) (.out 0x11f98c (mulR64Effect 0x11f98c 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[110, 138]
    (.letOp (n := 142) (.exec 0x11f98c (fun s => s.RIP = 0x11f98c) (mulR64Effect 0x11f98c 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[110, 138]
    (.letOp (n := 143) (.out 0x11f98f (movR64R64Effect 0x11f98f 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[141]
    (.letOp (n := 144) (.exec 0x11f98f (fun s => s.RIP = 0x11f98f) (movR64R64Effect 0x11f98f 6 2) (Reg.operands [.gpr 2] [])) #v[141]
    (.letOp (n := 145) (.out 0x11f992 (movR64R64Effect 0x11f992 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[140]
    (.letOp (n := 146) (.exec 0x11f992 (fun s => s.RIP = 0x11f992) (movR64R64Effect 0x11f992 12 0) (Reg.operands [.gpr 0] [])) #v[140]
    (.letOp (n := 147) (.out 0x11f995 (movR64R64Effect 0x11f995 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[62]
    (.letOp (n := 148) (.exec 0x11f995 (fun s => s.RIP = 0x11f995) (movR64R64Effect 0x11f995 0 14) (Reg.operands [.gpr 14] [])) #v[62]
    (.letOp (n := 149) (.out 0x11f998 (mulR64Effect 0x11f998 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[58, 147]
    (.letOp (n := 150) (.out 0x11f998 (mulR64Effect 0x11f998 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[58, 147]
    (.letOp (n := 151) (.exec 0x11f998 (fun s => s.RIP = 0x11f998) (mulR64Effect 0x11f998 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[58, 147]
    (.letOp (n := 152) (.out 0x11f99b (movR64R64Effect 0x11f99b 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[150]
    (.letOp (n := 153) (.exec 0x11f99b (fun s => s.RIP = 0x11f99b) (movR64R64Effect 0x11f99b 9 2) (Reg.operands [.gpr 2] [])) #v[150]
    (.letOp (n := 154) (.out 0x11f99e (movR64R64Effect 0x11f99e 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[149]
    (.letOp (n := 155) (.exec 0x11f99e (fun s => s.RIP = 0x11f99e) (movR64R64Effect 0x11f99e 11 0) (Reg.operands [.gpr 0] [])) #v[149]
    (.letOp (n := 156) (.out 0x11f9a1 (movR64R64Effect 0x11f9a1 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 157) (.exec 0x11f9a1 (fun s => s.RIP = 0x11f9a1) (movR64R64Effect 0x11f9a1 0 5) (Reg.operands [.gpr 5] [])) #v[70]
    (.letOp (n := 158) (.out 0x11f9a4 (mulR64Effect 0x11f9a4 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[60, 156]
    (.letOp (n := 159) (.out 0x11f9a4 (mulR64Effect 0x11f9a4 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[60, 156]
    (.letOp (n := 160) (.exec 0x11f9a4 (fun s => s.RIP = 0x11f9a4) (mulR64Effect 0x11f9a4 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[60, 156]
    (.letOp (n := 161) (.out 0x11f9a7 (shrR64Effect 0x11f9a7 4 3 52) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[123]
    (.letOp (n := 162) (.exec 0x11f9a7 (fun s => s.RIP = 0x11f9a7) (shrR64Effect 0x11f9a7 4 3 52) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[123]
    (.letOp (n := 163) (.out 0x11f9ab (addR64R64Effect 0x11f9ab 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[158, 154]
    (.letOp (n := 164) (.out 0x11f9ab (addR64R64Effect 0x11f9ab 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[158, 154]
    (.letOp (n := 165) (.exec 0x11f9ab (fun s => s.RIP = 0x11f9ab) (addR64R64Effect 0x11f9ab 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[158, 154]
    (.letOp (n := 166) (.out 0x11f9ae (atFlags StatusFlags.CF (adcR64R64Effect 0x11f9ae 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[152, 159, 164]
    (.letOp (n := 167) (.exec 0x11f9ae (fun s => s.RIP = 0x11f9ae) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f9ae 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[152, 159, 164]
    (.letOp (n := 168) (.out 0x11f9b1 (shldR64R64Effect 0x11f9b1 5 9 0 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[166, 163]
    (.letOp (n := 169) (.exec 0x11f9b1 (fun s => s.RIP = 0x11f9b1) (shldR64R64Effect 0x11f9b1 5 9 0 1) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[166, 163]
    (.letOp (n := 170) (.out 0x11f9b6 (addR64R64Effect 0x11f9b6 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[163, 163]
    (.letOp (n := 171) (.exec 0x11f9b6 (fun s => s.RIP = 0x11f9b6) (addR64R64Effect 0x11f9b6 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[163, 163]
    (.letOp (n := 172) (.out 0x11f9b9 (addR64R64Effect 0x11f9b9 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[145, 136]
    (.letOp (n := 173) (.out 0x11f9b9 (addR64R64Effect 0x11f9b9 12 10) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 10] []) (.flag .CF)) #v[145, 136]
    (.letOp (n := 174) (.exec 0x11f9b9 (fun s => s.RIP = 0x11f9b9) (addR64R64Effect 0x11f9b9 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[145, 136]
    (.letOp (n := 175) (.out 0x11f9bc (atFlags StatusFlags.CF (adcR64R64Effect 0x11f9bc 6 8)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[143, 134, 173]
    (.letOp (n := 176) (.exec 0x11f9bc (fun s => s.RIP = 0x11f9bc) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f9bc 6 8)) (Reg.operands [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[143, 134, 173]
    (.letOp (n := 177) (.out 0x11f9bf (addR64R64Effect 0x11f9bf 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[172, 170]
    (.letOp (n := 178) (.out 0x11f9bf (addR64R64Effect 0x11f9bf 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[172, 170]
    (.letOp (n := 179) (.exec 0x11f9bf (fun s => s.RIP = 0x11f9bf) (addR64R64Effect 0x11f9bf 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[172, 170]
    (.letOp (n := 180) (.out 0x11f9c2 (atFlags StatusFlags.CF (adcR64R64Effect 0x11f9c2 6 9)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[175, 168, 178]
    (.letOp (n := 181) (.exec 0x11f9c2 (fun s => s.RIP = 0x11f9c2) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f9c2 6 9)) (Reg.operands [.gpr 6, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[175, 168, 178]
    (.letOp (n := 182) (.out 0x11f9c5 (addR64R64Effect 0x11f9c5 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 7] []) (.reg (.gpr 12))) #v[177, 125]
    (.letOp (n := 183) (.out 0x11f9c5 (addR64R64Effect 0x11f9c5 12 7) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 7] []) (.flag .CF)) #v[177, 125]
    (.letOp (n := 184) (.exec 0x11f9c5 (fun s => s.RIP = 0x11f9c5) (addR64R64Effect 0x11f9c5 12 7) (Reg.operands [.gpr 12, .gpr 7] [])) #v[177, 125]
    (b_l11f8f6_3)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_2 : List UInt8 :=
  [0x4C, 0x89, 0xC8, 0x49, 0xF7, 0xE3, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x4C, 0x89, 0xF0, 0x49,
    0xF7, 0xE7, 0x49, 0x89, 0xD1, 0x49, 0x89, 0xC3, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE5, 0x48, 0xC1,
    0xEB, 0x34, 0x4C, 0x01, 0xD8, 0x49, 0x11, 0xD1, 0x49, 0x0F, 0xA4, 0xC1, 0x01, 0x48, 0x01, 0xC0,
    0x4D, 0x01, 0xD4, 0x4C, 0x11, 0xC6, 0x49, 0x01, 0xC4, 0x4C, 0x11, 0xCE, 0x49, 0x01, 0xFC] ++ bytes_l11f8f6_3

theorem code_l11f8f6_2 : ∀ x ∈ codeRange 0x11f989 bytes_l11f8f6_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f989 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_3

def b_l11f8f6_1 : Block Op Label signature Reg.count 95 :=
  .letOp (n := 95) (.out 0x11f939 (movR64R64Effect 0x11f939 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[62]
    (.letOp (n := 96) (.exec 0x11f939 (fun s => s.RIP = 0x11f939) (movR64R64Effect 0x11f939 0 14) (Reg.operands [.gpr 14] [])) #v[62]
    (.letOp (n := 97) (.out 0x11f93c (mulR64Effect 0x11f93c 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[62, 95]
    (.letOp (n := 98) (.out 0x11f93c (mulR64Effect 0x11f93c 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[62, 95]
    (.letOp (n := 99) (.exec 0x11f93c (fun s => s.RIP = 0x11f93c) (mulR64Effect 0x11f93c 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[62, 95]
    (.letOp (n := 100) (.out 0x11f93f (movR64R64Effect 0x11f93f 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[98]
    (.letOp (n := 101) (.exec 0x11f93f (fun s => s.RIP = 0x11f93f) (movR64R64Effect 0x11f93f 9 2) (Reg.operands [.gpr 2] [])) #v[98]
    (.letOp (n := 102) (.out 0x11f942 (addR64R64Effect 0x11f942 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[88, 88]
    (.letOp (n := 103) (.exec 0x11f942 (fun s => s.RIP = 0x11f942) (addR64R64Effect 0x11f942 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[88, 88]
    (.letOp (n := 104) (.out 0x11f945 (movR64Imm64Effect 0x11f945 1 0xffffffffffffd) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 105) (.exec 0x11f945 (fun s => s.RIP = 0x11f945) (movR64Imm64Effect 0x11f945 1 0xffffffffffffd) (Reg.operands [] [])) #v[]
    (.letOp (n := 106) (.out 0x11f94f (shldR64R64Effect 0x11f94f 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[100, 97]
    (.letOp (n := 107) (.exec 0x11f94f (fun s => s.RIP = 0x11f94f) (shldR64R64Effect 0x11f94f 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[100, 97]
    (.letOp (n := 108) (.out 0x11f954 (andR64R64Effect 0x11f954 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[97, 104]
    (.letOp (n := 109) (.exec 0x11f954 (fun s => s.RIP = 0x11f954) (andR64R64Effect 0x11f954 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[97, 104]
    (.letOp (n := 110) (.out 0x11f957 (movR64Imm64Effect 0x11f957 11 0x1000003d10) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 111) (.exec 0x11f957 (fun s => s.RIP = 0x11f957) (movR64Imm64Effect 0x11f957 11 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 112) (.out 0x11f961 (mulR64Effect 0x11f961 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[110, 108]
    (.letOp (n := 113) (.out 0x11f961 (mulR64Effect 0x11f961 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[110, 108]
    (.letOp (n := 114) (.exec 0x11f961 (fun s => s.RIP = 0x11f961) (mulR64Effect 0x11f961 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[110, 108]
    (.letOp (n := 115) (.out 0x11f964 (movR64R64Effect 0x11f964 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[113]
    (.letOp (n := 116) (.exec 0x11f964 (fun s => s.RIP = 0x11f964) (movR64R64Effect 0x11f964 7 2) (Reg.operands [.gpr 2] [])) #v[113]
    (.letOp (n := 117) (.out 0x11f967 (addR64R64Effect 0x11f967 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[112, 102]
    (.letOp (n := 118) (.out 0x11f967 (addR64R64Effect 0x11f967 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[112, 102]
    (.letOp (n := 119) (.exec 0x11f967 (fun s => s.RIP = 0x11f967) (addR64R64Effect 0x11f967 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[112, 102]
    (.letOp (n := 120) (.exec 0x11f96a (StorePre 0x11f96a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11f96a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f96a 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[117, 4]
    (.letOp (n := 121) (.out 0x11f96f (atFlags StatusFlags.CF (adcR64R64Effect 0x11f96f 7 6)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[115, 93, 118]
    (.letOp (n := 122) (.exec 0x11f96f (fun s => s.RIP = 0x11f96f) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f96f 7 6)) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[115, 93, 118]
    (.letOp (n := 123) (.out 0x11f972 (movR64R64Effect 0x11f972 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[121]
    (.letOp (n := 124) (.exec 0x11f972 (fun s => s.RIP = 0x11f972) (movR64R64Effect 0x11f972 3 7) (Reg.operands [.gpr 7] [])) #v[121]
    (.letOp (n := 125) (.out 0x11f975 (shldR64R64Effect 0x11f975 5 7 0 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[121, 117]
    (.letOp (n := 126) (.exec 0x11f975 (fun s => s.RIP = 0x11f975) (shldR64R64Effect 0x11f975 5 7 0 12) (Reg.operands [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[121, 117]
    (.letOp (n := 127) (.out 0x11f97a (movR64R64Effect 0x11f97a 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[66]
    (.letOp (n := 128) (.exec 0x11f97a (fun s => s.RIP = 0x11f97a) (movR64R64Effect 0x11f97a 1 12) (Reg.operands [.gpr 12] [])) #v[66]
    (.letOp (n := 129) (.out 0x11f97d (movR64R64Effect 0x11f97d 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[66]
    (.letOp (n := 130) (.exec 0x11f97d (fun s => s.RIP = 0x11f97d) (movR64R64Effect 0x11f97d 0 12) (Reg.operands [.gpr 12] [])) #v[66]
    (.letOp (n := 131) (.out 0x11f980 (mulR64Effect 0x11f980 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[66, 129]
    (.letOp (n := 132) (.out 0x11f980 (mulR64Effect 0x11f980 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[66, 129]
    (.letOp (n := 133) (.exec 0x11f980 (fun s => s.RIP = 0x11f980) (mulR64Effect 0x11f980 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[66, 129]
    (.letOp (n := 134) (.out 0x11f983 (movR64R64Effect 0x11f983 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[132]
    (.letOp (n := 135) (.exec 0x11f983 (fun s => s.RIP = 0x11f983) (movR64R64Effect 0x11f983 8 2) (Reg.operands [.gpr 2] [])) #v[132]
    (.letOp (n := 136) (.out 0x11f986 (movR64R64Effect 0x11f986 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[131]
    (.letOp (n := 137) (.exec 0x11f986 (fun s => s.RIP = 0x11f986) (movR64R64Effect 0x11f986 10 0) (Reg.operands [.gpr 0] [])) #v[131]
    (b_l11f8f6_2)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6_1 : List UInt8 :=
  [0x4C, 0x89, 0xF0, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xD1, 0x4D, 0x01, 0xC0, 0x48, 0xB9, 0xFD, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x21, 0xC8, 0x49, 0xBB,
    0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE3, 0x48, 0x89, 0xD7, 0x4C, 0x01,
    0xC0, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x11, 0xF7, 0x48, 0x89, 0xFB, 0x48, 0x0F, 0xA4, 0xC7,
    0x0C, 0x4C, 0x89, 0xE1, 0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE4, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC2] ++ bytes_l11f8f6_2

theorem code_l11f8f6_1 : ∀ x ∈ codeRange 0x11f939 bytes_l11f8f6_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f939 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_2

def b_l11f8f6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f8f6 (movzxR32R8Effect 0x11f8f6 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x11f8f6 (fun s => s.RIP = 0x11f8f6) (movzxR32R8Effect 0x11f8f6 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.exec 0x11f8f9 (StorePre 0x11f8f9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11f8f9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11f8f9 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11f901 (negR64Effect 0x11f901 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 57) (.exec 0x11f901 (fun s => s.RIP = 0x11f901) (negR64Effect 0x11f901 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 58) (.out 0x11f904 (andR64R64Effect 0x11f904 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[15, 56]
    (.letOp (n := 59) (.exec 0x11f904 (fun s => s.RIP = 0x11f904) (andR64R64Effect 0x11f904 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[15, 56]
    (.letOp (n := 60) (.out 0x11f907 (andR64R64Effect 0x11f907 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[13, 56]
    (.letOp (n := 61) (.exec 0x11f907 (fun s => s.RIP = 0x11f907) (andR64R64Effect 0x11f907 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[13, 56]
    (.letOp (n := 62) (.out 0x11f90a (andR64R64Effect 0x11f90a 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[14, 56]
    (.letOp (n := 63) (.exec 0x11f90a (fun s => s.RIP = 0x11f90a) (andR64R64Effect 0x11f90a 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[14, 56]
    (.letOp (n := 64) (.out 0x11f90d (andR64R64Effect 0x11f90d 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[56, 5]
    (.letOp (n := 65) (.exec 0x11f90d (fun s => s.RIP = 0x11f90d) (andR64R64Effect 0x11f90d 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[56, 5]
    (.letOp (n := 66) (.out 0x11f910 (andR64R64Effect 0x11f910 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[12, 64]
    (.letOp (n := 67) (.exec 0x11f910 (fun s => s.RIP = 0x11f910) (andR64R64Effect 0x11f910 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[12, 64]
    (.letOp (n := 68) (.out 0x11f913 (andR64R64Effect 0x11f913 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[64, 3]
    (.letOp (n := 69) (.exec 0x11f913 (fun s => s.RIP = 0x11f913) (andR64R64Effect 0x11f913 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[64, 3]
    (.letOp (n := 70) (.out 0x11f916 (movR64R64Effect 0x11f916 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.exec 0x11f916 (fun s => s.RIP = 0x11f916) (movR64R64Effect 0x11f916 5 0) (Reg.operands [.gpr 0] [])) #v[68]
    (.letOp (n := 72) (.out 0x11f919 (mulR64Effect 0x11f919 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[58, 68]
    (.letOp (n := 73) (.out 0x11f919 (mulR64Effect 0x11f919 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[58, 68]
    (.letOp (n := 74) (.exec 0x11f919 (fun s => s.RIP = 0x11f919) (mulR64Effect 0x11f919 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[58, 68]
    (.letOp (n := 75) (.out 0x11f91c (movR64R64Effect 0x11f91c 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[73]
    (.letOp (n := 76) (.exec 0x11f91c (fun s => s.RIP = 0x11f91c) (movR64R64Effect 0x11f91c 1 2) (Reg.operands [.gpr 2] [])) #v[73]
    (.letOp (n := 77) (.out 0x11f91f (movR64R64Effect 0x11f91f 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[72]
    (.letOp (n := 78) (.exec 0x11f91f (fun s => s.RIP = 0x11f91f) (movR64R64Effect 0x11f91f 7 0) (Reg.operands [.gpr 0] [])) #v[72]
    (.letOp (n := 79) (.out 0x11f922 (movR64R64Effect 0x11f922 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[66]
    (.letOp (n := 80) (.exec 0x11f922 (fun s => s.RIP = 0x11f922) (movR64R64Effect 0x11f922 0 12) (Reg.operands [.gpr 12] [])) #v[66]
    (.letOp (n := 81) (.out 0x11f925 (mulR64Effect 0x11f925 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[60, 79]
    (.letOp (n := 82) (.out 0x11f925 (mulR64Effect 0x11f925 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[60, 79]
    (.letOp (n := 83) (.exec 0x11f925 (fun s => s.RIP = 0x11f925) (mulR64Effect 0x11f925 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[60, 79]
    (.letOp (n := 84) (.out 0x11f928 (movR64R64Effect 0x11f928 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[82]
    (.letOp (n := 85) (.exec 0x11f928 (fun s => s.RIP = 0x11f928) (movR64R64Effect 0x11f928 6 2) (Reg.operands [.gpr 2] [])) #v[82]
    (.letOp (n := 86) (.out 0x11f92b (movR64R64Effect 0x11f92b 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[81]
    (.letOp (n := 87) (.exec 0x11f92b (fun s => s.RIP = 0x11f92b) (movR64R64Effect 0x11f92b 8 0) (Reg.operands [.gpr 0] [])) #v[81]
    (.letOp (n := 88) (.out 0x11f92e (addR64R64Effect 0x11f92e 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[86, 77]
    (.letOp (n := 89) (.out 0x11f92e (addR64R64Effect 0x11f92e 8 7) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 7] []) (.flag .CF)) #v[86, 77]
    (.letOp (n := 90) (.exec 0x11f92e (fun s => s.RIP = 0x11f92e) (addR64R64Effect 0x11f92e 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[86, 77]
    (.letOp (n := 91) (.out 0x11f931 (atFlags StatusFlags.CF (adcR64R64Effect 0x11f931 6 1)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[84, 75, 89]
    (.letOp (n := 92) (.exec 0x11f931 (fun s => s.RIP = 0x11f931) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f931 6 1)) (Reg.operands [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[84, 75, 89]
    (.letOp (n := 93) (.out 0x11f934 (shldR64R64Effect 0x11f934 5 6 8 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[91, 88]
    (.letOp (n := 94) (.exec 0x11f934 (fun s => s.RIP = 0x11f934) (shldR64R64Effect 0x11f934 5 6 8 1) (Reg.operands [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[91, 88]
    (b_l11f8f6_1))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f8f6 : List UInt8 :=
  [0x0F, 0xB6, 0xC0, 0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xD8, 0x49, 0x21,
    0xC7, 0x49, 0x21, 0xC5, 0x49, 0x21, 0xC6, 0x48, 0x21, 0xE8, 0x49, 0x21, 0xC4, 0x48, 0x21, 0xD8,
    0x48, 0x89, 0xC5, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC7, 0x4C, 0x89, 0xE0, 0x49,
    0xF7, 0xE5, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC0, 0x49, 0x01, 0xF8, 0x48, 0x11, 0xCE, 0x4C, 0x0F,
    0xA4, 0xC6, 0x01] ++ bytes_l11f8f6_1

theorem code_l11f8f6 : ∀ x ∈ codeRange 0x11f8f6 bytes_l11f8f6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f8f6 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f8f6_1

@[cfg_block] def b_l120298_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.exec 0x120304 (StorePre 0x120304 4 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x120304 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x120304 1 (.base 3 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[82, 53]
    (.letOp (n := 85) (.exec 0x120308 (StorePre 0x120308 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x120308 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x120308 (.base 3 (.d8 0x50)) 0x0) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 86) (.out 0x12030c (movR64M64Effect 0x12030c 1 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 87) (.exec 0x12030c (LoadPre 0x12030c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x12030c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12030c 1 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 88) (.out 0x120314 (andR8R8Effect 0x120314 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[86, 0]
    (.letOp (n := 89) (.exec 0x120314 (fun s => s.RIP = 0x120314) (andR8R8Effect 0x120314 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[86, 0]
    (.letOp (n := 90) (.out 0x120316 (movzxR32R8Effect 0x120316 3 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[88]
    (.letOp (n := 91) (.exec 0x120316 (fun s => s.RIP = 0x120316) (movzxR32R8Effect 0x120316 3 7 1) (Reg.operands [.gpr 1] [])) #v[88]
    (.letOp (n := 92) (.out 0x120319 (callEffect (fun _ => 0x127d50) 0x12031e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 93) (.exec 0x120319 (PushPre 0x120319 5) (callEffect (fun _ => 0x127d50) 0x12031e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 94) (.const ⟨64, 0x12031e⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 0), (1, 88), (2, 2), (3, 53), (4, 92), (5, 5), (6, 6), (7, 90), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 95⟩ { target := .l12031e, kept := #v[], arity := rfl, guard := some (Fin.last 94) }))))))))))))

def bytes_l120298_1 : List UInt8 :=
  [0x48, 0x89, 0x4B, 0x48, 0xC6, 0x43, 0x50, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00,
    0x20, 0xC1, 0x0F, 0xB6, 0xF9, 0xE8, 0x32, 0x7A, 0x00, 0x00]

theorem code_l120298_1 : ∀ x ∈ codeRange 0x120304 bytes_l120298_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x20304 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l120298 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x120298 (movR64M64Effect 0x120298 3 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x120298 (LoadPre 0x120298 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x120298 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120298 3 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1202a0 (movR64M64Effect 0x1202a0 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1202a0 (LoadPre 0x1202a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1202a0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1202a0 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1202a5 (StorePre 0x1202a5 3 (fun s => AddrMode.addr (.base 3 .none) s (0x1202a5 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1202a5 1 (.base 3 .none)) (Reg.operands [.gpr 1, .gpr 3] [])) #v[55, 53]
    (.letOp (n := 58) (.out 0x1202a8 (movR64M64Effect 0x1202a8 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x1202a8 (LoadPre 0x1202a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1202a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1202a8 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x1202ad (StorePre 0x1202ad 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1202ad + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1202ad 1 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[58, 53]
    (.letOp (n := 61) (.out 0x1202b1 (movR64M64Effect 0x1202b1 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x1202b1 (LoadPre 0x1202b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1202b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1202b1 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x1202b6 (StorePre 0x1202b6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1202b6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1202b6 1 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[61, 53]
    (.letOp (n := 64) (.out 0x1202ba (movR64M64Effect 0x1202ba 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1202ba (LoadPre 0x1202ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1202ba + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1202ba 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1202bf (StorePre 0x1202bf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1202bf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1202bf 1 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[64, 53]
    (.letOp (n := 67) (.out 0x1202c3 (movR64M64Effect 0x1202c3 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 68) (.exec 0x1202c3 (LoadPre 0x1202c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1202c3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1202c3 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x1202c8 (StorePre 0x1202c8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1202c8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1202c8 1 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[67, 53]
    (.letOp (n := 70) (.out 0x1202cc (movR64M64Effect 0x1202cc 1 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 71) (.exec 0x1202cc (LoadPre 0x1202cc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1202cc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1202cc 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x1202d4 (StorePre 0x1202d4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1202d4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1202d4 1 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[70, 53]
    (.letOp (n := 73) (.out 0x1202d8 (movR64M64Effect 0x1202d8 1 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 74) (.exec 0x1202d8 (LoadPre 0x1202d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1202d8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1202d8 1 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x1202e0 (StorePre 0x1202e0 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x1202e0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1202e0 1 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[73, 53]
    (.letOp (n := 76) (.out 0x1202e4 (movR64M64Effect 0x1202e4 1 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 77) (.exec 0x1202e4 (LoadPre 0x1202e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1202e4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1202e4 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x1202ec (StorePre 0x1202ec 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x1202ec + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1202ec 1 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[76, 53]
    (.letOp (n := 79) (.out 0x1202f0 (movR64M64Effect 0x1202f0 1 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 80) (.exec 0x1202f0 (LoadPre 0x1202f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1202f0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1202f0 1 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x1202f8 (StorePre 0x1202f8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x1202f8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1202f8 1 (.base 3 (.d8 0x40))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[79, 53]
    (.letOp (n := 82) (.out 0x1202fc (movR64M64Effect 0x1202fc 1 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 83) (.exec 0x1202fc (LoadPre 0x1202fc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1202fc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1202fc 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l120298_1)))))))))))))))))))))))))))))))

def bytes_l120298 : List UInt8 :=
  [0x48, 0x8B, 0x9C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x50, 0x48, 0x89, 0x0B,
    0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4B, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x58, 0x48, 0x89,
    0x4B, 0x10, 0x48, 0x8B, 0x4C, 0x24, 0x38, 0x48, 0x89, 0x4B, 0x18, 0x48, 0x8B, 0x4C, 0x24, 0x20,
    0x48, 0x89, 0x4B, 0x20, 0x48, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4B, 0x28,
    0x48, 0x8B, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4B, 0x30, 0x48, 0x8B, 0x8C, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4B, 0x38, 0x48, 0x8B, 0x8C, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x4B, 0x40, 0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] ++ bytes_l120298_1

theorem code_l120298 : ∀ x ∈ codeRange 0x120298 bytes_l120298, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20298 108 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l120298_1

@[cfg_block] def b_l12031e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12031e (movR64M64Effect 0x12031e 1 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x12031e (LoadPre 0x12031e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x12031e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12031e 1 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x120326 (andR8R8Effect 0x120326 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[53, 0]
    (.letOp (n := 56) (.exec 0x120326 (fun s => s.RIP = 0x120326) (andR8R8Effect 0x120326 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 57) (.out 0x120328 (movzxR32R8Effect 0x120328 3 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x120328 (fun s => s.RIP = 0x120328) (movzxR32R8Effect 0x120328 3 7 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 59) (.out 0x12032b (callEffect (fun _ => 0x127d50) 0x120330) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x12032b (PushPre 0x12032b 5) (callEffect (fun _ => 0x127d50) 0x120330) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x120330⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l120330, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l12031e : List UInt8 :=
  [0x48, 0x8B, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x20, 0xC1, 0x0F, 0xB6, 0xF9, 0xE8, 0x20, 0x7A,
    0x00, 0x00]

theorem code_l12031e : ∀ x ∈ codeRange 0x12031e bytes_l12031e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2031e 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l120330 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x120330 (StorePre 0x120330 3 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x120330 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x120330 3 0 (.base 3 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 54) (.out 0x120333 (movR64R64Effect 0x120333 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 55) (.exec 0x120333 (fun s => s.RIP = 0x120333) (movR64R64Effect 0x120333 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 56) (.out 0x120336 (addR64Imm32Effect 0x120336 4 0xd8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x120336 (fun s => s.RIP = 0x120336) (addR64Imm32Effect 0x120336 4 0xd8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x12033d (popR64Effect 0x12033d 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[56]
    (.letOp (n := 59) (.out 0x12033d (popR64Effect 0x12033d 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x12033d (PopPre 0x12033d) (popR64Effect 0x12033d 1 3) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x12033e (popR64Effect 0x12033e 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[59]
    (.letOp (n := 62) (.out 0x12033e (popR64Effect 0x12033e 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x12033e (PopPre 0x12033e) (popR64Effect 0x12033e 2 12) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x120340 (popR64Effect 0x120340 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[62]
    (.letOp (n := 65) (.out 0x120340 (popR64Effect 0x120340 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x120340 (PopPre 0x120340) (popR64Effect 0x120340 2 13) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x120342 (popR64Effect 0x120342 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 68) (.out 0x120342 (popR64Effect 0x120342 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x120342 (PopPre 0x120342) (popR64Effect 0x120342 2 14) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x120344 (popR64Effect 0x120344 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[68]
    (.letOp (n := 71) (.out 0x120344 (popR64Effect 0x120344 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x120344 (PopPre 0x120344) (popR64Effect 0x120344 2 15) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x120346 (popR64Effect 0x120346 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[71]
    (.letOp (n := 74) (.out 0x120346 (popR64Effect 0x120346 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x120346 (PopPre 0x120346) (popR64Effect 0x120346 1 5) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x120347 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[74]
    (.letOp (n := 77) (.out 0x120347 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x120347 (RetPre 0x120347) (retEffect) (Reg.operands [.gpr 4] [])) #v[74]
    (.terminate (.ret (RegMap.args [(0, 54), (1, 1), (2, 2), (3, 58), (4, 77), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 79) (some ⟨76, by decide⟩))))))))))))))))))))))))))))

def bytes_l120330 : List UInt8 :=
  [0x88, 0x43, 0x58, 0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xD8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C,
    0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l120330 : ∀ x ∈ codeRange 0x120330 bytes_l120330, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x20330 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1205b0_2 : Block Op Label signature Reg.count 133 :=
  .letOp (n := 133) (.out 0x120649 (andR8R8Effect 0x120649 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[131, 124]
    (.letOp (n := 134) (.exec 0x120649 (fun s => s.RIP = 0x120649) (andR8R8Effect 0x120649 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[131, 124]
    (.letOp (n := 135) (.out 0x12064b (movzxR32R8Effect 0x12064b 3 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[133]
    (.letOp (n := 136) (.exec 0x12064b (fun s => s.RIP = 0x12064b) (movzxR32R8Effect 0x12064b 3 7 1) (Reg.operands [.gpr 1] [])) #v[133]
    (.letOp (n := 137) (.out 0x12064e (callEffect (fun _ => 0x127d50) 0x120653) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 138) (.exec 0x12064e (PushPre 0x12064e 5) (callEffect (fun _ => 0x127d50) 0x120653) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 139) (.const ⟨64, 0x120653⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 124), (1, 133), (2, 101), (3, 89), (4, 137), (5, 85), (6, 111), (7, 135), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 115), (22, 22), (39, 39), (50, 50), (51, 51)] 140⟩ { target := .l120653, kept := #v[], arity := rfl, guard := some (Fin.last 139) }))))))))

def bytes_l1205b0_2 : List UInt8 :=
  [0x20, 0xC1, 0x0F, 0xB6, 0xF9, 0xE8, 0xFD, 0x76, 0x00, 0x00]

theorem code_l1205b0_2 : ∀ x ∈ codeRange 0x120649 bytes_l1205b0_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x20649 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1205b0_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x1205fa (movR64R64Effect 0x1205fa 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[79]
    (.letOp (n := 92) (.exec 0x1205fa (fun s => s.RIP = 0x1205fa) (movR64R64Effect 0x1205fa 1 0) (Reg.operands [.gpr 0] [])) #v[79]
    (.letOp (n := 93) (.out 0x1205fd (shldR64R64Effect 0x1205fd 5 14 0 24) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[75, 79]
    (.letOp (n := 94) (.exec 0x1205fd (fun s => s.RIP = 0x1205fd) (shldR64R64Effect 0x1205fd 5 14 0 24) (Reg.operands [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[75, 79]
    (.letOp (n := 95) (.out 0x120602 (shldR64R64Effect 0x120602 5 1 12 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[91, 83]
    (.letOp (n := 96) (.exec 0x120602 (fun s => s.RIP = 0x120602) (shldR64R64Effect 0x120602 5 1 12 12) (Reg.operands [.gpr 1, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[91, 83]
    (.letOp (n := 97) (.out 0x120607 (andR64R64Effect 0x120607 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[83, 85]
    (.letOp (n := 98) (.exec 0x120607 (fun s => s.RIP = 0x120607) (andR64R64Effect 0x120607 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[83, 85]
    (.letOp (n := 99) (.out 0x12060a (andR64R64Effect 0x12060a 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[95, 85]
    (.letOp (n := 100) (.exec 0x12060a (fun s => s.RIP = 0x12060a) (andR64R64Effect 0x12060a 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[95, 85]
    (.letOp (n := 101) (.out 0x12060d (shrR64Effect 0x12060d 4 2 16) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[73]
    (.letOp (n := 102) (.exec 0x12060d (fun s => s.RIP = 0x12060d) (shrR64Effect 0x12060d 4 2 16) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 103) (.out 0x120611 (movR64R64Effect 0x120611 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[93]
    (.letOp (n := 104) (.exec 0x120611 (fun s => s.RIP = 0x120611) (movR64R64Effect 0x120611 0 14) (Reg.operands [.gpr 14] [])) #v[93]
    (.letOp (n := 105) (.out 0x120614 (andR64R64Effect 0x120614 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[103, 89]
    (.letOp (n := 106) (.exec 0x120614 (fun s => s.RIP = 0x120614) (andR64R64Effect 0x120614 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[103, 89]
    (.letOp (n := 107) (.out 0x120617 (andR64R64Effect 0x120617 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[105, 99]
    (.letOp (n := 108) (.exec 0x120617 (fun s => s.RIP = 0x120617) (andR64R64Effect 0x120617 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[105, 99]
    (.letOp (n := 109) (.out 0x12061a (movR64R64Effect 0x12061a 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[99]
    (.letOp (n := 110) (.exec 0x12061a (fun s => s.RIP = 0x12061a) (movR64R64Effect 0x12061a 13 1) (Reg.operands [.gpr 1] [])) #v[99]
    (.letOp (n := 111) (.out 0x12061d (movR64Imm64Effect 0x12061d 6 0xffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 112) (.exec 0x12061d (fun s => s.RIP = 0x12061d) (movR64Imm64Effect 0x12061d 6 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 113) (.out 0x120627 (movR64R64Effect 0x120627 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[101]
    (.letOp (n := 114) (.exec 0x120627 (fun s => s.RIP = 0x120627) (movR64R64Effect 0x120627 1 2) (Reg.operands [.gpr 2] [])) #v[101]
    (.letOp (n := 115) (.out 0x12062a (movR64R64Effect 0x12062a 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[101]
    (.letOp (n := 116) (.exec 0x12062a (fun s => s.RIP = 0x12062a) (movR64R64Effect 0x12062a 15 2) (Reg.operands [.gpr 2] [])) #v[101]
    (.letOp (n := 117) (.out 0x12062d (xorR64R64Effect 0x12062d 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[113, 111]
    (.letOp (n := 118) (.exec 0x12062d (fun s => s.RIP = 0x12062d) (xorR64R64Effect 0x12062d 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[113, 111]
    (.letOp (n := 119) (.out 0x120630 (xorR64R64Effect 0x120630 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[107, 85]
    (.letOp (n := 120) (.exec 0x120630 (fun s => s.RIP = 0x120630) (xorR64R64Effect 0x120630 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[107, 85]
    (.letOp (n := 121) (.out 0x120633 (orR64R64Effect 0x120633 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[119, 117]
    (.letOp (n := 122) (.out 0x120633 (orR64R64Effect 0x120633 0 1) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 1] []) (.flag .ZF)) #v[119, 117]
    (.letOp (n := 123) (.exec 0x120633 (fun s => s.RIP = 0x120633) (orR64R64Effect 0x120633 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[119, 117]
    (.letOp (n := 124) (.out 0x120636 (atFlags (condHolds 4) (setccR8Effect 0x120636 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[121, 122]
    (.letOp (n := 125) (.exec 0x120636 (fun s => s.RIP = 0x120636) (atFlags (condHolds 4) (setccR8Effect 0x120636 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[121, 122]
    (.letOp (n := 126) (.out 0x120639 (movR64Imm64Effect 0x120639 1 0xffffefffffc2e) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 127) (.exec 0x120639 (fun s => s.RIP = 0x120639) (movR64Imm64Effect 0x120639 1 0xffffefffffc2e) (Reg.operands [] [])) #v[]
    (.letOp (n := 128) (.out 0x120643 (cmpR64R64Effect 0x120643 12 1) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 1] []) (.flag .CF)) #v[97, 126]
    (.letOp (n := 129) (.out 0x120643 (cmpR64R64Effect 0x120643 12 1) (EffectPart.reads (.flag .ZF) [.gpr 12, .gpr 1] []) (.flag .ZF)) #v[97, 126]
    (.letOp (n := 130) (.exec 0x120643 (fun s => s.RIP = 0x120643) (cmpR64R64Effect 0x120643 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[97, 126]
    (.letOp (n := 131) (.out 0x120646 (atFlags (condHolds 7) (setccR8Effect 0x120646 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 1))) #v[126, 128, 129]
    (.letOp (n := 132) (.exec 0x120646 (fun s => s.RIP = 0x120646) (atFlags (condHolds 7) (setccR8Effect 0x120646 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[126, 128, 129]
    (b_l1205b0_2))))))))))))))))))))))))))))))))))))))))))

def bytes_l1205b0_1 : List UInt8 :=
  [0x48, 0x89, 0xC1, 0x49, 0x0F, 0xA4, 0xC6, 0x18, 0x4C, 0x0F, 0xA4, 0xE1, 0x0C, 0x49, 0x21, 0xEC,
    0x48, 0x21, 0xE9, 0x48, 0xC1, 0xEA, 0x10, 0x4C, 0x89, 0xF0, 0x48, 0x21, 0xD8, 0x48, 0x21, 0xC8,
    0x49, 0x89, 0xCD, 0x48, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x89, 0xD1,
    0x49, 0x89, 0xD7, 0x48, 0x31, 0xF1, 0x48, 0x31, 0xE8, 0x48, 0x09, 0xC8, 0x0F, 0x94, 0xC0, 0x48,
    0xB9, 0x2E, 0xFC, 0xFF, 0xFF, 0xFE, 0xFF, 0x0F, 0x00, 0x49, 0x39, 0xCC, 0x0F, 0x97, 0xC1] ++ bytes_l1205b0_2

theorem code_l1205b0_1 : ∀ x ∈ codeRange 0x1205fa bytes_l1205b0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x205fa 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1205b0_2

@[cfg_block] def b_l1205b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1205b0 (pushR64Effect 0x1205b0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1205b0 (PushPre 0x1205b0 1) (pushR64Effect 0x1205b0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1205b1 (pushR64Effect 0x1205b1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1205b1 (PushPre 0x1205b1 2) (pushR64Effect 0x1205b1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1205b3 (pushR64Effect 0x1205b3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1205b3 (PushPre 0x1205b3 2) (pushR64Effect 0x1205b3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1205b5 (pushR64Effect 0x1205b5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1205b5 (PushPre 0x1205b5 2) (pushR64Effect 0x1205b5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1205b7 (pushR64Effect 0x1205b7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1205b7 (PushPre 0x1205b7 2) (pushR64Effect 0x1205b7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1205b9 (pushR64Effect 0x1205b9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1205b9 (PushPre 0x1205b9 1) (pushR64Effect 0x1205b9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1205ba (subR64Imm32Effect 0x1205ba 4 0x1b8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1205ba (fun s => s.RIP = 0x1205ba) (subR64Imm32Effect 0x1205ba 4 0x1b8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.exec 0x1205c1 (StorePre 0x1205c1 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x1205c1 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1205c1 2 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 65]
    (.letOp (n := 68) (.exec 0x1205c5 (StorePre 0x1205c5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1205c5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1205c5 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 69) (.out 0x1205cd (movR64M64Effect 0x1205cd 2 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 70) (.exec 0x1205cd (LoadPre 0x1205cd (fun s => AddrMode.addr (.base 6 .none) s (0x1205cd + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1205cd 2 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x1205d0 (movR64M64Effect 0x1205d0 14 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 72) (.exec 0x1205d0 (LoadPre 0x1205d0 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1205d0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1205d0 14 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x1205d4 (bswapR64Effect 0x1205d4 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[69]
    (.letOp (n := 74) (.exec 0x1205d4 (fun s => s.RIP = 0x1205d4) (bswapR64Effect 0x1205d4 3 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 75) (.out 0x1205d7 (bswapR64Effect 0x1205d7 3 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[71]
    (.letOp (n := 76) (.exec 0x1205d7 (fun s => s.RIP = 0x1205d7) (bswapR64Effect 0x1205d7 3 14) (Reg.operands [.gpr 14] [])) #v[71]
    (.letOp (n := 77) (.out 0x1205da (movR64M64Effect 0x1205da 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 78) (.exec 0x1205da (LoadPre 0x1205da (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1205da + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1205da 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 79) (.out 0x1205de (bswapR64Effect 0x1205de 3 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[77]
    (.letOp (n := 80) (.exec 0x1205de (fun s => s.RIP = 0x1205de) (bswapR64Effect 0x1205de 3 0) (Reg.operands [.gpr 0] [])) #v[77]
    (.letOp (n := 81) (.out 0x1205e1 (movR64M64Effect 0x1205e1 12 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 82) (.exec 0x1205e1 (LoadPre 0x1205e1 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1205e1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1205e1 12 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 83) (.out 0x1205e5 (bswapR64Effect 0x1205e5 3 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[81]
    (.letOp (n := 84) (.exec 0x1205e5 (fun s => s.RIP = 0x1205e5) (bswapR64Effect 0x1205e5 3 12) (Reg.operands [.gpr 12] [])) #v[81]
    (.letOp (n := 85) (.out 0x1205e8 (movR64Imm64Effect 0x1205e8 5 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 86) (.exec 0x1205e8 (fun s => s.RIP = 0x1205e8) (movR64Imm64Effect 0x1205e8 5 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 87) (.out 0x1205f2 (movR64R64Effect 0x1205f2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[73]
    (.letOp (n := 88) (.exec 0x1205f2 (fun s => s.RIP = 0x1205f2) (movR64R64Effect 0x1205f2 3 2) (Reg.operands [.gpr 2] [])) #v[73]
    (.letOp (n := 89) (.out 0x1205f5 (shldR64R64Effect 0x1205f5 5 3 14 36) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[87, 75]
    (.letOp (n := 90) (.exec 0x1205f5 (fun s => s.RIP = 0x1205f5) (shldR64R64Effect 0x1205f5 5 3 14 36) (Reg.operands [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87, 75]
    (b_l1205b0_1))))))))))))))))))))))))))))))))))))))

def bytes_l1205b0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xB8, 0x01, 0x00,
    0x00, 0x89, 0x54, 0x24, 0x6C, 0x48, 0x89, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x16,
    0x4C, 0x8B, 0x76, 0x08, 0x48, 0x0F, 0xCA, 0x49, 0x0F, 0xCE, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x0F,
    0xC8, 0x4C, 0x8B, 0x66, 0x18, 0x49, 0x0F, 0xCC, 0x48, 0xBD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x0F, 0x00, 0x48, 0x89, 0xD3, 0x4C, 0x0F, 0xA4, 0xF3, 0x24] ++ bytes_l1205b0_1

theorem code_l1205b0 : ∀ x ∈ codeRange 0x1205b0 bytes_l1205b0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x205b0 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1205b0_1

@[cfg_block] def b_l120653 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x120653 (notR8Effect 0x120653 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x120653 (fun s => s.RIP = 0x120653) (notR8Effect 0x120653 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x120655 (andAlImm8Effect 0x120655 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x120655 (fun s => s.RIP = 0x120655) (andAlImm8Effect 0x120655 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x120657 (movzxR32R8Effect 0x120657 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x120657 (fun s => s.RIP = 0x120657) (movzxR32R8Effect 0x120657 3 7 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x12065a (callEffect (fun _ => 0x127d50) 0x12065f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x12065a (PushPre 0x12065a 5) (callEffect (fun _ => 0x127d50) 0x12065f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x12065f⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l12065f, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l120653 : List UInt8 :=
  [0xF6, 0xD0, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0xF1, 0x76, 0x00, 0x00]

theorem code_l120653 : ∀ x ∈ codeRange 0x120653 bytes_l120653, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x20653 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l12065f_21 : Block Op Label signature Reg.count 967 :=
  .letOp (n := 967) (.out 0x120ca2 (atFlags StatusFlags.CF (adcR64R64Effect 0x120ca2 2 9)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[962, 944, 965]
    (.letOp (n := 968) (.exec 0x120ca2 (fun s => s.RIP = 0x120ca2) (atFlags StatusFlags.CF (adcR64R64Effect 0x120ca2 2 9)) (Reg.operands [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[962, 944, 965]
    (.letOp (n := 969) (.out 0x120ca5 (andR64R64Effect 0x120ca5 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[907, 964]
    (.letOp (n := 970) (.exec 0x120ca5 (fun s => s.RIP = 0x120ca5) (andR64R64Effect 0x120ca5 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[907, 964]
    (.letOp (n := 971) (.out 0x120ca8 (shldR64R64Effect 0x120ca8 5 2 8 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[967, 964]
    (.letOp (n := 972) (.exec 0x120ca8 (fun s => s.RIP = 0x120ca8) (shldR64R64Effect 0x120ca8 5 2 8 12) (Reg.operands [.gpr 2, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[967, 964]
    (.letOp (n := 973) (.out 0x120cad (movR64Imm64Effect 0x120cad 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 974) (.exec 0x120cad (fun s => s.RIP = 0x120cad) (movR64Imm64Effect 0x120cad 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 975) (.out 0x120cb7 (andR64R64Effect 0x120cb7 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[638, 973]
    (.letOp (n := 976) (.exec 0x120cb7 (fun s => s.RIP = 0x120cb7) (andR64R64Effect 0x120cb7 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[638, 973]
    (.letOp (n := 977) (.out 0x120cba (addR64R64Effect 0x120cba 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[975, 971]
    (.letOp (n := 978) (.exec 0x120cba (fun s => s.RIP = 0x120cba) (addR64R64Effect 0x120cba 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[975, 971]
    (.letOp (n := 979) (.out 0x120cbd (movR64M64Effect 0x120cbd 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 980) (.exec 0x120cbd (LoadPre 0x120cbd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x120cbd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120cbd 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 981) (.out 0x120cc2 (addR64Imm8Effect 0x120cc2 0 0x7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[979]
    (.letOp (n := 982) (.exec 0x120cc2 (fun s => s.RIP = 0x120cc2) (addR64Imm8Effect 0x120cc2 0 0x7) (Reg.operands [.gpr 0] [])) #v[979]
    (.letOp (n := 983) (.exec 0x120cc6 (StorePre 0x120cc6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x120cc6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120cc6 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[981, 4]
    (.letOp (n := 984) (.exec 0x120cce (StorePre 0x120cce 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x120cce + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120cce 11 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[875, 4]
    (.letOp (n := 985) (.exec 0x120cd6 (StorePre 0x120cd6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x120cd6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120cd6 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[946, 4]
    (.letOp (n := 986) (.exec 0x120cde (StorePre 0x120cde 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x120cde + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120cde 3 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[969, 4]
    (.letOp (n := 987) (.exec 0x120ce6 (StorePre 0x120ce6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x120ce6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120ce6 14 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[977, 4]
    (.letOp (n := 988) (.out 0x120cee (leaR64Effect 0x120cee 7 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 989) (.exec 0x120cee (fun s => s.RIP = 0x120cee) (leaR64Effect 0x120cee 7 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 990) (.out 0x120cf6 (leaR64Effect 0x120cf6 6 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 991) (.exec 0x120cf6 (fun s => s.RIP = 0x120cf6) (leaR64Effect 0x120cf6 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 992) (.out 0x120cfe (callEffect (fun _ => 0x115950) 0x120d03) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 993) (.exec 0x120cfe (PushPre 0x120cfe 5) (callEffect (fun _ => 0x115950) 0x120d03) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 994) (.const ⟨64, 0x120d03⟩) #v[]
    (.terminate (.call ⟨.l115950, RegMap.args [(0, 981), (1, 948), (2, 971), (3, 969), (4, 992), (5, 872), (6, 990), (7, 988), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 977), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)] 995⟩ { target := .l120d03, kept := #v[], arity := rfl, guard := some (Fin.last 994) })))))))))))))))))))))))))))))

def bytes_l12065f_21 : List UInt8 :=
  [0x4C, 0x11, 0xCA, 0x4C, 0x21, 0xC3, 0x4C, 0x0F, 0xA4, 0xC2, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x49, 0x21, 0xC6, 0x49, 0x01, 0xD6, 0x48, 0x8B, 0x44, 0x24, 0x38,
    0x48, 0x83, 0xC0, 0x07, 0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x9C, 0x24,
    0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x9C, 0x24,
    0xA8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24,
    0x30, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0xE8, 0x4D, 0x4C, 0xFF,
    0xFF]

theorem code_l12065f_21 : ∀ x ∈ codeRange 0x120ca2 bytes_l12065f_21, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x20ca2 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l12065f_20 : Block Op Label signature Reg.count 921 :=
  .letOp (n := 921) (.out 0x120c5b (addR64R64Effect 0x120c5b 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[916, 872]
    (.letOp (n := 922) (.out 0x120c5b (addR64R64Effect 0x120c5b 6 5) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 5] []) (.flag .CF)) #v[916, 872]
    (.letOp (n := 923) (.exec 0x120c5b (fun s => s.RIP = 0x120c5b) (addR64R64Effect 0x120c5b 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[916, 872]
    (.letOp (n := 924) (.out 0x120c5e (atFlags StatusFlags.CF (adcR64M64Effect 0x120c5e 7 (.sib 4 none 0 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[919, 4, 922]
    (.letOp (n := 925) (.exec 0x120c5e (LoadPre 0x120c5e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120c5e + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x120c5e 7 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[919, 4, 922]
    (.letOp (n := 926) (.out 0x120c63 (addR64R64Effect 0x120c63 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[921, 913]
    (.letOp (n := 927) (.out 0x120c63 (addR64R64Effect 0x120c63 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[921, 913]
    (.letOp (n := 928) (.exec 0x120c63 (fun s => s.RIP = 0x120c63) (addR64R64Effect 0x120c63 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[921, 913]
    (.letOp (n := 929) (.out 0x120c66 (atFlags StatusFlags.CF (adcR64R64Effect 0x120c66 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[924, 914, 927]
    (.letOp (n := 930) (.exec 0x120c66 (fun s => s.RIP = 0x120c66) (atFlags StatusFlags.CF (adcR64R64Effect 0x120c66 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[924, 914, 927]
    (.letOp (n := 931) (.out 0x120c69 (addR64R64Effect 0x120c69 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[926, 849]
    (.letOp (n := 932) (.out 0x120c69 (addR64R64Effect 0x120c69 6 13) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 13] []) (.flag .CF)) #v[926, 849]
    (.letOp (n := 933) (.exec 0x120c69 (fun s => s.RIP = 0x120c69) (addR64R64Effect 0x120c69 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[926, 849]
    (.letOp (n := 934) (.out 0x120c6c (atFlags StatusFlags.CF (adcR64R64Effect 0x120c6c 7 15)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[929, 847, 932]
    (.letOp (n := 935) (.exec 0x120c6c (fun s => s.RIP = 0x120c6c) (atFlags StatusFlags.CF (adcR64R64Effect 0x120c6c 7 15)) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[929, 847, 932]
    (.letOp (n := 936) (.out 0x120c6f (shrdR64R64Effect 0x120c6f 5 8 1 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[900, 903]
    (.letOp (n := 937) (.exec 0x120c6f (fun s => s.RIP = 0x120c6f) (shrdR64R64Effect 0x120c6f 5 8 1 52) (Reg.operands [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[900, 903]
    (.letOp (n := 938) (.out 0x120c74 (shrR64Effect 0x120c74 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[903]
    (.letOp (n := 939) (.exec 0x120c74 (fun s => s.RIP = 0x120c74) (shrR64Effect 0x120c74 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[903]
    (.letOp (n := 940) (.out 0x120c78 (movR64R64Effect 0x120c78 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[934]
    (.letOp (n := 941) (.exec 0x120c78 (fun s => s.RIP = 0x120c78) (movR64R64Effect 0x120c78 9 7) (Reg.operands [.gpr 7] [])) #v[934]
    (.letOp (n := 942) (.out 0x120c7b (shldR64R64Effect 0x120c7b 5 7 6 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[934, 931]
    (.letOp (n := 943) (.exec 0x120c7b (fun s => s.RIP = 0x120c7b) (shldR64R64Effect 0x120c7b 5 7 6 12) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[934, 931]
    (.letOp (n := 944) (.out 0x120c80 (shrR64Effect 0x120c80 4 9 52) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[940]
    (.letOp (n := 945) (.exec 0x120c80 (fun s => s.RIP = 0x120c80) (shrR64Effect 0x120c80 4 9 52) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[940]
    (.letOp (n := 946) (.out 0x120c84 (andR64R64Effect 0x120c84 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[931, 907]
    (.letOp (n := 947) (.exec 0x120c84 (fun s => s.RIP = 0x120c84) (andR64R64Effect 0x120c84 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[931, 907]
    (.letOp (n := 948) (.out 0x120c87 (imulR64R64Effect 0x120c87 4 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[938, 911]
    (.letOp (n := 949) (.exec 0x120c87 (fun s => s.RIP = 0x120c87) (imulR64R64Effect 0x120c87 4 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[938, 911]
    (.letOp (n := 950) (.out 0x120c8b (movR64R64Effect 0x120c8b 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[936]
    (.letOp (n := 951) (.exec 0x120c8b (fun s => s.RIP = 0x120c8b) (movR64R64Effect 0x120c8b 0 8) (Reg.operands [.gpr 8] [])) #v[936]
    (.letOp (n := 952) (.out 0x120c8e (mulR64Effect 0x120c8e 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[911, 950]
    (.letOp (n := 953) (.out 0x120c8e (mulR64Effect 0x120c8e 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[911, 950]
    (.letOp (n := 954) (.exec 0x120c8e (fun s => s.RIP = 0x120c8e) (mulR64Effect 0x120c8e 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[911, 950]
    (.letOp (n := 955) (.out 0x120c91 (movR64M64Effect 0x120c91 8 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 956) (.exec 0x120c91 (LoadPre 0x120c91 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x120c91 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120c91 8 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 957) (.out 0x120c96 (andR64R64Effect 0x120c96 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[955, 907]
    (.letOp (n := 958) (.exec 0x120c96 (fun s => s.RIP = 0x120c96) (andR64R64Effect 0x120c96 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[955, 907]
    (.letOp (n := 959) (.out 0x120c99 (addR64R64Effect 0x120c99 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[957, 952]
    (.letOp (n := 960) (.out 0x120c99 (addR64R64Effect 0x120c99 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[957, 952]
    (.letOp (n := 961) (.exec 0x120c99 (fun s => s.RIP = 0x120c99) (addR64R64Effect 0x120c99 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[957, 952]
    (.letOp (n := 962) (.out 0x120c9c (atFlags StatusFlags.CF (adcR64R64Effect 0x120c9c 2 1)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[953, 948, 960]
    (.letOp (n := 963) (.exec 0x120c9c (fun s => s.RIP = 0x120c9c) (atFlags StatusFlags.CF (adcR64R64Effect 0x120c9c 2 1)) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[953, 948, 960]
    (.letOp (n := 964) (.out 0x120c9f (addR64R64Effect 0x120c9f 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[959, 942]
    (.letOp (n := 965) (.out 0x120c9f (addR64R64Effect 0x120c9f 8 7) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 7] []) (.flag .CF)) #v[959, 942]
    (.letOp (n := 966) (.exec 0x120c9f (fun s => s.RIP = 0x120c9f) (addR64R64Effect 0x120c9f 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[959, 942]
    (b_l12065f_21))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_20 : List UInt8 :=
  [0x48, 0x01, 0xEE, 0x48, 0x13, 0x7C, 0x24, 0x08, 0x48, 0x01, 0xC6, 0x48, 0x11, 0xD7, 0x4C, 0x01,
    0xEE, 0x4C, 0x11, 0xFF, 0x49, 0x0F, 0xAC, 0xC8, 0x34, 0x48, 0xC1, 0xE9, 0x34, 0x49, 0x89, 0xF9,
    0x48, 0x0F, 0xA4, 0xF7, 0x0C, 0x49, 0xC1, 0xE9, 0x34, 0x48, 0x21, 0xDE, 0x49, 0x0F, 0xAF, 0xCA,
    0x4C, 0x89, 0xC0, 0x49, 0xF7, 0xE2, 0x4C, 0x8B, 0x44, 0x24, 0x60, 0x49, 0x21, 0xD8, 0x49, 0x01,
    0xC0, 0x48, 0x11, 0xCA, 0x49, 0x01, 0xF8] ++ bytes_l12065f_21

theorem code_l12065f_20 : ∀ x ∈ codeRange 0x120c5b bytes_l12065f_20, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20c5b 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_21

def b_l12065f_19 : Block Op Label signature Reg.count 875 :=
  .letOp (n := 875) (.out 0x120c05 (andR64R64Effect 0x120c05 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[834, 815]
    (.letOp (n := 876) (.exec 0x120c05 (fun s => s.RIP = 0x120c05) (andR64R64Effect 0x120c05 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[834, 815]
    (.letOp (n := 877) (.out 0x120c08 (movR64M64Effect 0x120c08 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 878) (.exec 0x120c08 (LoadPre 0x120c08 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x120c08 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120c08 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 879) (.out 0x120c0d (mulM64Effect 0x120c0d 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[877, 4]
    (.letOp (n := 880) (.out 0x120c0d (mulM64Effect 0x120c0d 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[877, 4]
    (.letOp (n := 881) (.exec 0x120c0d (LoadPre 0x120c0d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x120c0d + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120c0d 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[877, 4]
    (.letOp (n := 882) (.out 0x120c12 (movR64R64Effect 0x120c12 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[880]
    (.letOp (n := 883) (.exec 0x120c12 (fun s => s.RIP = 0x120c12) (movR64R64Effect 0x120c12 3 2) (Reg.operands [.gpr 2] [])) #v[880]
    (.letOp (n := 884) (.out 0x120c15 (movR64R64Effect 0x120c15 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[879]
    (.letOp (n := 885) (.exec 0x120c15 (fun s => s.RIP = 0x120c15) (movR64R64Effect 0x120c15 10 0) (Reg.operands [.gpr 0] [])) #v[879]
    (.letOp (n := 886) (.out 0x120c18 (movR64M64Effect 0x120c18 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 887) (.exec 0x120c18 (LoadPre 0x120c18 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x120c18 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120c18 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 888) (.out 0x120c1d (mulM64Effect 0x120c1d 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[886, 4]
    (.letOp (n := 889) (.out 0x120c1d (mulM64Effect 0x120c1d 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[886, 4]
    (.letOp (n := 890) (.exec 0x120c1d (LoadPre 0x120c1d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x120c1d + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120c1d 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[886, 4]
    (.letOp (n := 891) (.out 0x120c22 (movR64R64Effect 0x120c22 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[889]
    (.letOp (n := 892) (.exec 0x120c22 (fun s => s.RIP = 0x120c22) (movR64R64Effect 0x120c22 1 2) (Reg.operands [.gpr 2] [])) #v[889]
    (.letOp (n := 893) (.out 0x120c25 (movR64R64Effect 0x120c25 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[888]
    (.letOp (n := 894) (.exec 0x120c25 (fun s => s.RIP = 0x120c25) (movR64R64Effect 0x120c25 8 0) (Reg.operands [.gpr 0] [])) #v[888]
    (.letOp (n := 895) (.out 0x120c28 (addR64R64Effect 0x120c28 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[893, 884]
    (.letOp (n := 896) (.out 0x120c28 (addR64R64Effect 0x120c28 8 10) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 10] []) (.flag .CF)) #v[893, 884]
    (.letOp (n := 897) (.exec 0x120c28 (fun s => s.RIP = 0x120c28) (addR64R64Effect 0x120c28 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[893, 884]
    (.letOp (n := 898) (.out 0x120c2b (atFlags StatusFlags.CF (adcR64R64Effect 0x120c2b 1 3)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[891, 882, 896]
    (.letOp (n := 899) (.exec 0x120c2b (fun s => s.RIP = 0x120c2b) (atFlags StatusFlags.CF (adcR64R64Effect 0x120c2b 1 3)) (Reg.operands [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[891, 882, 896]
    (.letOp (n := 900) (.out 0x120c2e (addR64R64Effect 0x120c2e 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[895, 841]
    (.letOp (n := 901) (.out 0x120c2e (addR64R64Effect 0x120c2e 8 12) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 12] []) (.flag .CF)) #v[895, 841]
    (.letOp (n := 902) (.exec 0x120c2e (fun s => s.RIP = 0x120c2e) (addR64R64Effect 0x120c2e 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[895, 841]
    (.letOp (n := 903) (.out 0x120c31 (atFlags StatusFlags.CF (adcR64R64Effect 0x120c31 1 9)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[898, 843, 901]
    (.letOp (n := 904) (.exec 0x120c31 (fun s => s.RIP = 0x120c31) (atFlags StatusFlags.CF (adcR64R64Effect 0x120c31 1 9)) (Reg.operands [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[898, 843, 901]
    (.letOp (n := 905) (.out 0x120c34 (movR64R64Effect 0x120c34 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[900]
    (.letOp (n := 906) (.exec 0x120c34 (fun s => s.RIP = 0x120c34) (movR64R64Effect 0x120c34 0 8) (Reg.operands [.gpr 8] [])) #v[900]
    (.letOp (n := 907) (.out 0x120c37 (movR64Imm64Effect 0x120c37 3 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 908) (.exec 0x120c37 (fun s => s.RIP = 0x120c37) (movR64Imm64Effect 0x120c37 3 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 909) (.out 0x120c41 (andR64R64Effect 0x120c41 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[905, 907]
    (.letOp (n := 910) (.exec 0x120c41 (fun s => s.RIP = 0x120c41) (andR64R64Effect 0x120c41 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[905, 907]
    (.letOp (n := 911) (.out 0x120c44 (movR64Imm64Effect 0x120c44 10 0x1000003d10) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 912) (.exec 0x120c44 (fun s => s.RIP = 0x120c44) (movR64Imm64Effect 0x120c44 10 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 913) (.out 0x120c4e (mulR64Effect 0x120c4e 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[911, 909]
    (.letOp (n := 914) (.out 0x120c4e (mulR64Effect 0x120c4e 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[911, 909]
    (.letOp (n := 915) (.exec 0x120c4e (fun s => s.RIP = 0x120c4e) (mulR64Effect 0x120c4e 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[911, 909]
    (.letOp (n := 916) (.out 0x120c51 (addR64M64Effect 0x120c51 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[865, 4]
    (.letOp (n := 917) (.out 0x120c51 (addR64M64Effect 0x120c51 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 4] []) (.flag .CF)) #v[865, 4]
    (.letOp (n := 918) (.exec 0x120c51 (LoadPre 0x120c51 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120c51 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x120c51 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[865, 4]
    (.letOp (n := 919) (.out 0x120c56 (atFlags StatusFlags.CF (adcR64M64Effect 0x120c56 7 (.sib 4 none 0 (.d8 0x10)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[863, 4, 917]
    (.letOp (n := 920) (.exec 0x120c56 (LoadPre 0x120c56 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120c56 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x120c56 7 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[863, 4, 917]
    (b_l12065f_20))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_19 : List UInt8 :=
  [0x49, 0x21, 0xCB, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0xF7, 0x64, 0x24, 0x48, 0x48, 0x89, 0xD3,
    0x49, 0x89, 0xC2, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0xF7, 0x64, 0x24, 0x30, 0x48, 0x89, 0xD1,
    0x49, 0x89, 0xC0, 0x4D, 0x01, 0xD0, 0x48, 0x11, 0xD9, 0x4D, 0x01, 0xE0, 0x4C, 0x11, 0xC9, 0x4C,
    0x89, 0xC0, 0x48, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD8, 0x49,
    0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x48, 0x03, 0x74, 0x24,
    0x18, 0x48, 0x13, 0x7C, 0x24, 0x10] ++ bytes_l12065f_20

theorem code_l12065f_19 : ∀ x ∈ codeRange 0x120c05 bytes_l12065f_19, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20c05 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_20

def b_l12065f_18 : Block Op Label signature Reg.count 834 :=
  .letOp (n := 834) (.out 0x120bb4 (addR64R64Effect 0x120bb4 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[829, 746]
    (.letOp (n := 835) (.out 0x120bb4 (addR64R64Effect 0x120bb4 11 6) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 6] []) (.flag .CF)) #v[829, 746]
    (.letOp (n := 836) (.exec 0x120bb4 (fun s => s.RIP = 0x120bb4) (addR64R64Effect 0x120bb4 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[829, 746]
    (.letOp (n := 837) (.out 0x120bb7 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x120bb7 13 0x0)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[832, 835]
    (.letOp (n := 838) (.exec 0x120bb7 (fun s => s.RIP = 0x120bb7) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x120bb7 13 0x0)) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[832, 835]
    (.letOp (n := 839) (.out 0x120bbb (movR64R64Effect 0x120bbb 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 12] []) (.reg (.gpr 9))) #v[811]
    (.letOp (n := 840) (.exec 0x120bbb (fun s => s.RIP = 0x120bbb) (movR64R64Effect 0x120bbb 9 12) (Reg.operands [.gpr 12] [])) #v[811]
    (.letOp (n := 841) (.out 0x120bbe (shldR64R64Effect 0x120bbe 5 12 5 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[811, 808]
    (.letOp (n := 842) (.exec 0x120bbe (fun s => s.RIP = 0x120bbe) (shldR64R64Effect 0x120bbe 5 12 5 12) (Reg.operands [.gpr 12, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[811, 808]
    (.letOp (n := 843) (.out 0x120bc3 (shrR64Effect 0x120bc3 4 9 52) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[839]
    (.letOp (n := 844) (.exec 0x120bc3 (fun s => s.RIP = 0x120bc3) (shrR64Effect 0x120bc3 4 9 52) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[839]
    (.letOp (n := 845) (.out 0x120bc7 (movR64R64Effect 0x120bc7 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 13] []) (.reg (.gpr 15))) #v[837]
    (.letOp (n := 846) (.exec 0x120bc7 (fun s => s.RIP = 0x120bc7) (movR64R64Effect 0x120bc7 15 13) (Reg.operands [.gpr 13] [])) #v[837]
    (.letOp (n := 847) (.out 0x120bca (shrR64Effect 0x120bca 4 15 52) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[845]
    (.letOp (n := 848) (.exec 0x120bca (fun s => s.RIP = 0x120bca) (shrR64Effect 0x120bca 4 15 52) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[845]
    (.letOp (n := 849) (.out 0x120bce (shldR64R64Effect 0x120bce 5 13 11 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[837, 834]
    (.letOp (n := 850) (.exec 0x120bce (fun s => s.RIP = 0x120bce) (shldR64R64Effect 0x120bce 5 13 11 12) (Reg.operands [.gpr 13, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[837, 834]
    (.letOp (n := 851) (.out 0x120bd3 (movR64M64Effect 0x120bd3 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 852) (.exec 0x120bd3 (LoadPre 0x120bd3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120bd3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120bd3 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 853) (.out 0x120bd8 (mulR64Effect 0x120bd8 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[791, 851]
    (.letOp (n := 854) (.out 0x120bd8 (mulR64Effect 0x120bd8 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[791, 851]
    (.letOp (n := 855) (.exec 0x120bd8 (fun s => s.RIP = 0x120bd8) (mulR64Effect 0x120bd8 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[791, 851]
    (.letOp (n := 856) (.exec 0x120bdb (StorePre 0x120bdb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120bdb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120bdb 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[854, 4]
    (.letOp (n := 857) (.exec 0x120be0 (StorePre 0x120be0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120be0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120be0 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[853, 4]
    (.letOp (n := 858) (.out 0x120be5 (movR64M64Effect 0x120be5 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 859) (.exec 0x120be5 (LoadPre 0x120be5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120be5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120be5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 860) (.out 0x120bea (mulM64Effect 0x120bea 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[858, 4]
    (.letOp (n := 861) (.out 0x120bea (mulM64Effect 0x120bea 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[858, 4]
    (.letOp (n := 862) (.exec 0x120bea (LoadPre 0x120bea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x120bea + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120bea 5 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[858, 4]
    (.letOp (n := 863) (.out 0x120bef (movR64R64Effect 0x120bef 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[861]
    (.letOp (n := 864) (.exec 0x120bef (fun s => s.RIP = 0x120bef) (movR64R64Effect 0x120bef 7 2) (Reg.operands [.gpr 2] [])) #v[861]
    (.letOp (n := 865) (.out 0x120bf2 (movR64R64Effect 0x120bf2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[860]
    (.letOp (n := 866) (.exec 0x120bf2 (fun s => s.RIP = 0x120bf2) (movR64R64Effect 0x120bf2 6 0) (Reg.operands [.gpr 0] [])) #v[860]
    (.letOp (n := 867) (.out 0x120bf5 (movR64R64Effect 0x120bf5 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[669]
    (.letOp (n := 868) (.exec 0x120bf5 (fun s => s.RIP = 0x120bf5) (movR64R64Effect 0x120bf5 0 10) (Reg.operands [.gpr 10] [])) #v[669]
    (.letOp (n := 869) (.out 0x120bf8 (mulM64Effect 0x120bf8 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[867, 4]
    (.letOp (n := 870) (.out 0x120bf8 (mulM64Effect 0x120bf8 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[867, 4]
    (.letOp (n := 871) (.exec 0x120bf8 (LoadPre 0x120bf8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x120bf8 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120bf8 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[867, 4]
    (.letOp (n := 872) (.out 0x120bfd (movR64R64Effect 0x120bfd 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[869]
    (.letOp (n := 873) (.exec 0x120bfd (fun s => s.RIP = 0x120bfd) (movR64R64Effect 0x120bfd 5 0) (Reg.operands [.gpr 0] [])) #v[869]
    (.letOp (n := 874) (.exec 0x120c00 (StorePre 0x120c00 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120c00 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120c00 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[870, 4]
    (b_l12065f_19)))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_18 : List UInt8 :=
  [0x49, 0x01, 0xF3, 0x49, 0x83, 0xD5, 0x00, 0x4D, 0x89, 0xE1, 0x49, 0x0F, 0xA4, 0xEC, 0x0C, 0x49,
    0xC1, 0xE9, 0x34, 0x4D, 0x89, 0xEF, 0x49, 0xC1, 0xEF, 0x34, 0x4D, 0x0F, 0xA4, 0xDD, 0x0C, 0x48,
    0x8B, 0x44, 0x24, 0x10, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24,
    0x18, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0xF7, 0x64, 0x24, 0x58, 0x48, 0x89, 0xD7, 0x48, 0x89,
    0xC6, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0x64, 0x24, 0x50, 0x48, 0x89, 0xC5, 0x48, 0x89, 0x54, 0x24,
    0x08] ++ bytes_l12065f_19

theorem code_l12065f_18 : ∀ x ∈ codeRange 0x120bb4 bytes_l12065f_18, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20bb4 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_19

def b_l12065f_17 : Block Op Label signature Reg.count 787 :=
  .letOp (n := 787) (.out 0x120b62 (movR64R64Effect 0x120b62 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[782]
    (.letOp (n := 788) (.exec 0x120b62 (fun s => s.RIP = 0x120b62) (movR64R64Effect 0x120b62 1 0) (Reg.operands [.gpr 0] [])) #v[782]
    (.letOp (n := 789) (.out 0x120b65 (movR64M64Effect 0x120b65 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 790) (.exec 0x120b65 (LoadPre 0x120b65 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x120b65 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120b65 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 791) (.out 0x120b6a (movR64M64Effect 0x120b6a 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 792) (.exec 0x120b6a (LoadPre 0x120b6a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x120b6a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120b6a 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 793) (.out 0x120b6f (mulR64Effect 0x120b6f 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[791, 789]
    (.letOp (n := 794) (.out 0x120b6f (mulR64Effect 0x120b6f 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[791, 789]
    (.letOp (n := 795) (.exec 0x120b6f (fun s => s.RIP = 0x120b6f) (mulR64Effect 0x120b6f 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[791, 789]
    (.letOp (n := 796) (.out 0x120b72 (movR64R64Effect 0x120b72 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[793]
    (.letOp (n := 797) (.exec 0x120b72 (fun s => s.RIP = 0x120b72) (movR64R64Effect 0x120b72 5 0) (Reg.operands [.gpr 0] [])) #v[793]
    (.letOp (n := 798) (.out 0x120b75 (addR64R64Effect 0x120b75 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[787, 778]
    (.letOp (n := 799) (.out 0x120b75 (addR64R64Effect 0x120b75 1 9) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 9] []) (.flag .CF)) #v[787, 778]
    (.letOp (n := 800) (.exec 0x120b75 (fun s => s.RIP = 0x120b75) (addR64R64Effect 0x120b75 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[787, 778]
    (.letOp (n := 801) (.out 0x120b78 (atFlags StatusFlags.CF (adcR64R64Effect 0x120b78 12 8)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[785, 776, 799]
    (.letOp (n := 802) (.exec 0x120b78 (fun s => s.RIP = 0x120b78) (atFlags StatusFlags.CF (adcR64R64Effect 0x120b78 12 8)) (Reg.operands [.gpr 12, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[785, 776, 799]
    (.letOp (n := 803) (.out 0x120b7b (addR64R64Effect 0x120b7b 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[796, 798]
    (.letOp (n := 804) (.out 0x120b7b (addR64R64Effect 0x120b7b 5 1) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 1] []) (.flag .CF)) #v[796, 798]
    (.letOp (n := 805) (.exec 0x120b7b (fun s => s.RIP = 0x120b7b) (addR64R64Effect 0x120b7b 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[796, 798]
    (.letOp (n := 806) (.out 0x120b7e (atFlags StatusFlags.CF (adcR64R64Effect 0x120b7e 12 2)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[801, 794, 804]
    (.letOp (n := 807) (.exec 0x120b7e (fun s => s.RIP = 0x120b7e) (atFlags StatusFlags.CF (adcR64R64Effect 0x120b7e 12 2)) (Reg.operands [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[801, 794, 804]
    (.letOp (n := 808) (.out 0x120b81 (addR64R64Effect 0x120b81 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[803, 722]
    (.letOp (n := 809) (.out 0x120b81 (addR64R64Effect 0x120b81 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[803, 722]
    (.letOp (n := 810) (.exec 0x120b81 (fun s => s.RIP = 0x120b81) (addR64R64Effect 0x120b81 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[803, 722]
    (.letOp (n := 811) (.out 0x120b84 (atFlags StatusFlags.CF (adcR64R64Effect 0x120b84 12 3)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[806, 739, 809]
    (.letOp (n := 812) (.exec 0x120b84 (fun s => s.RIP = 0x120b84) (atFlags StatusFlags.CF (adcR64R64Effect 0x120b84 12 3)) (Reg.operands [.gpr 12, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[806, 739, 809]
    (.letOp (n := 813) (.out 0x120b87 (movR64R64Effect 0x120b87 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[808]
    (.letOp (n := 814) (.exec 0x120b87 (fun s => s.RIP = 0x120b87) (movR64R64Effect 0x120b87 0 5) (Reg.operands [.gpr 5] [])) #v[808]
    (.letOp (n := 815) (.out 0x120b8a (movR64Imm64Effect 0x120b8a 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 816) (.exec 0x120b8a (fun s => s.RIP = 0x120b8a) (movR64Imm64Effect 0x120b8a 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 817) (.out 0x120b94 (andR64R64Effect 0x120b94 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[813, 815]
    (.letOp (n := 818) (.exec 0x120b94 (fun s => s.RIP = 0x120b94) (andR64R64Effect 0x120b94 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[813, 815]
    (.letOp (n := 819) (.out 0x120b97 (movR64Imm64Effect 0x120b97 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 820) (.exec 0x120b97 (fun s => s.RIP = 0x120b97) (movR64Imm64Effect 0x120b97 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 821) (.out 0x120ba1 (mulR64Effect 0x120ba1 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[819, 817]
    (.letOp (n := 822) (.out 0x120ba1 (mulR64Effect 0x120ba1 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[819, 817]
    (.letOp (n := 823) (.exec 0x120ba1 (fun s => s.RIP = 0x120ba1) (mulR64Effect 0x120ba1 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[819, 817]
    (.letOp (n := 824) (.out 0x120ba4 (addR64M64Effect 0x120ba4 11 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 4] []) (.reg (.gpr 11))) #v[762, 4]
    (.letOp (n := 825) (.out 0x120ba4 (addR64M64Effect 0x120ba4 11 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 4] []) (.flag .CF)) #v[762, 4]
    (.letOp (n := 826) (.exec 0x120ba4 (LoadPre 0x120ba4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x120ba4 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x120ba4 11 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[762, 4]
    (.letOp (n := 827) (.out 0x120ba9 (atFlags StatusFlags.CF (adcR64M64Effect 0x120ba9 13 (.sib 4 none 0 (.d8 0x18)))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 13))) #v[764, 4, 825]
    (.letOp (n := 828) (.exec 0x120ba9 (LoadPre 0x120ba9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120ba9 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x120ba9 13 (.sib 4 none 0 (.d8 0x18)))) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[764, 4, 825]
    (.letOp (n := 829) (.out 0x120bae (addR64R64Effect 0x120bae 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[824, 821]
    (.letOp (n := 830) (.out 0x120bae (addR64R64Effect 0x120bae 11 0) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 0] []) (.flag .CF)) #v[824, 821]
    (.letOp (n := 831) (.exec 0x120bae (fun s => s.RIP = 0x120bae) (addR64R64Effect 0x120bae 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[824, 821]
    (.letOp (n := 832) (.out 0x120bb1 (atFlags StatusFlags.CF (adcR64R64Effect 0x120bb1 13 2)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[827, 822, 830]
    (.letOp (n := 833) (.exec 0x120bb1 (fun s => s.RIP = 0x120bb1) (atFlags StatusFlags.CF (adcR64R64Effect 0x120bb1 13 2)) (Reg.operands [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[827, 822, 830]
    (b_l12065f_18)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_17 : List UInt8 :=
  [0x48, 0x89, 0xC1, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x7C, 0x24, 0x40, 0x48, 0xF7, 0xE7,
    0x48, 0x89, 0xC5, 0x4C, 0x01, 0xC9, 0x4D, 0x11, 0xC4, 0x48, 0x01, 0xCD, 0x49, 0x11, 0xD4, 0x4C,
    0x01, 0xFD, 0x49, 0x11, 0xDC, 0x48, 0x89, 0xE8, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x0F, 0x00, 0x48, 0x21, 0xC8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE2, 0x4C, 0x03, 0x5C, 0x24, 0x70, 0x4C, 0x13, 0x6C, 0x24, 0x18, 0x49, 0x01, 0xC3, 0x49,
    0x11, 0xD5] ++ bytes_l12065f_18

theorem code_l12065f_17 : ∀ x ∈ codeRange 0x120b62 bytes_l12065f_17, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20b62 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_18

def b_l12065f_16 : Block Op Label signature Reg.count 746 :=
  .letOp (n := 746) (.out 0x120b0d (shldR64R64Effect 0x120b0d 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[744, 741]
    (.letOp (n := 747) (.exec 0x120b0d (fun s => s.RIP = 0x120b0d) (shldR64R64Effect 0x120b0d 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[744, 741]
    (.letOp (n := 748) (.out 0x120b12 (movR64R64Effect 0x120b12 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[741]
    (.letOp (n := 749) (.exec 0x120b12 (fun s => s.RIP = 0x120b12) (movR64R64Effect 0x120b12 1 0) (Reg.operands [.gpr 0] [])) #v[741]
    (.letOp (n := 750) (.out 0x120b15 (movR64M64Effect 0x120b15 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 751) (.exec 0x120b15 (LoadPre 0x120b15 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120b15 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120b15 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 752) (.out 0x120b1a (mulR64Effect 0x120b1a 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[693, 750]
    (.letOp (n := 753) (.out 0x120b1a (mulR64Effect 0x120b1a 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[693, 750]
    (.letOp (n := 754) (.exec 0x120b1a (fun s => s.RIP = 0x120b1a) (mulR64Effect 0x120b1a 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[693, 750]
    (.letOp (n := 755) (.exec 0x120b1d (StorePre 0x120b1d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120b1d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120b1d 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[753, 4]
    (.letOp (n := 756) (.exec 0x120b22 (StorePre 0x120b22 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x120b22 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120b22 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[752, 4]
    (.letOp (n := 757) (.out 0x120b27 (movR64M64Effect 0x120b27 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 758) (.exec 0x120b27 (LoadPre 0x120b27 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120b27 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120b27 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 759) (.out 0x120b2c (mulM64Effect 0x120b2c 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[757, 4]
    (.letOp (n := 760) (.out 0x120b2c (mulM64Effect 0x120b2c 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[757, 4]
    (.letOp (n := 761) (.exec 0x120b2c (LoadPre 0x120b2c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x120b2c + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120b2c 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[757, 4]
    (.letOp (n := 762) (.out 0x120b31 (movR64R64Effect 0x120b31 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[759]
    (.letOp (n := 763) (.exec 0x120b31 (fun s => s.RIP = 0x120b31) (movR64R64Effect 0x120b31 11 0) (Reg.operands [.gpr 0] [])) #v[759]
    (.letOp (n := 764) (.out 0x120b34 (movR64R64Effect 0x120b34 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[760]
    (.letOp (n := 765) (.exec 0x120b34 (fun s => s.RIP = 0x120b34) (movR64R64Effect 0x120b34 13 2) (Reg.operands [.gpr 2] [])) #v[760]
    (.letOp (n := 766) (.out 0x120b37 (movR64Imm64Effect 0x120b37 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 767) (.exec 0x120b37 (fun s => s.RIP = 0x120b37) (movR64Imm64Effect 0x120b37 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 768) (.out 0x120b41 (andR64R64Effect 0x120b41 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[748, 766]
    (.letOp (n := 769) (.exec 0x120b41 (fun s => s.RIP = 0x120b41) (andR64R64Effect 0x120b41 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[748, 766]
    (.letOp (n := 770) (.exec 0x120b44 (StorePre 0x120b44 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x120b44 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120b44 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[768, 4]
    (.letOp (n := 771) (.out 0x120b49 (movR64R64Effect 0x120b49 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[669]
    (.letOp (n := 772) (.exec 0x120b49 (fun s => s.RIP = 0x120b49) (movR64R64Effect 0x120b49 0 10) (Reg.operands [.gpr 10] [])) #v[669]
    (.letOp (n := 773) (.out 0x120b4c (mulM64Effect 0x120b4c 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[771, 4]
    (.letOp (n := 774) (.out 0x120b4c (mulM64Effect 0x120b4c 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[771, 4]
    (.letOp (n := 775) (.exec 0x120b4c (LoadPre 0x120b4c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x120b4c + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120b4c 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[771, 4]
    (.letOp (n := 776) (.out 0x120b51 (movR64R64Effect 0x120b51 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[774]
    (.letOp (n := 777) (.exec 0x120b51 (fun s => s.RIP = 0x120b51) (movR64R64Effect 0x120b51 8 2) (Reg.operands [.gpr 2] [])) #v[774]
    (.letOp (n := 778) (.out 0x120b54 (movR64R64Effect 0x120b54 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[773]
    (.letOp (n := 779) (.exec 0x120b54 (fun s => s.RIP = 0x120b54) (movR64R64Effect 0x120b54 9 0) (Reg.operands [.gpr 0] [])) #v[773]
    (.letOp (n := 780) (.out 0x120b57 (movR64R64Effect 0x120b57 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[680]
    (.letOp (n := 781) (.exec 0x120b57 (fun s => s.RIP = 0x120b57) (movR64R64Effect 0x120b57 0 7) (Reg.operands [.gpr 7] [])) #v[680]
    (.letOp (n := 782) (.out 0x120b5a (mulM64Effect 0x120b5a 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[780, 4]
    (.letOp (n := 783) (.out 0x120b5a (mulM64Effect 0x120b5a 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[780, 4]
    (.letOp (n := 784) (.exec 0x120b5a (LoadPre 0x120b5a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x120b5a + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120b5a 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[780, 4]
    (.letOp (n := 785) (.out 0x120b5f (movR64R64Effect 0x120b5f 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[783]
    (.letOp (n := 786) (.exec 0x120b5f (fun s => s.RIP = 0x120b5f) (movR64R64Effect 0x120b5f 12 2) (Reg.operands [.gpr 2] [])) #v[783]
    (b_l12065f_17)))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_16 : List UInt8 :=
  [0x48, 0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0x89, 0xC1, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x49, 0xF7, 0xE0,
    0x48, 0x89, 0x54, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x70, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x48,
    0xF7, 0x64, 0x24, 0x50, 0x49, 0x89, 0xC3, 0x49, 0x89, 0xD5, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC1, 0x48, 0x89, 0x4C, 0x24, 0x38, 0x4C, 0x89, 0xD0, 0x48,
    0xF7, 0x64, 0x24, 0x48, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC1, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0x64,
    0x24, 0x30, 0x49, 0x89, 0xD4] ++ bytes_l12065f_17

theorem code_l12065f_16 : ∀ x ∈ codeRange 0x120b0d bytes_l12065f_16, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20b0d 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_17

def b_l12065f_15 : Block Op Label signature Reg.count 700 :=
  .letOp (n := 700) (.out 0x120abb (addR64R64Effect 0x120abb 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[678, 661]
    (.letOp (n := 701) (.out 0x120abb (addR64R64Effect 0x120abb 9 6) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 6] []) (.flag .CF)) #v[678, 661]
    (.letOp (n := 702) (.exec 0x120abb (fun s => s.RIP = 0x120abb) (addR64R64Effect 0x120abb 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[678, 661]
    (.letOp (n := 703) (.out 0x120abe (atFlags StatusFlags.CF (adcR64R64Effect 0x120abe 15 12)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[676, 663, 701]
    (.letOp (n := 704) (.exec 0x120abe (fun s => s.RIP = 0x120abe) (atFlags StatusFlags.CF (adcR64R64Effect 0x120abe 15 12)) (Reg.operands [.gpr 15, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[676, 663, 701]
    (.letOp (n := 705) (.out 0x120ac1 (addR64R64Effect 0x120ac1 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[700, 689]
    (.letOp (n := 706) (.out 0x120ac1 (addR64R64Effect 0x120ac1 9 5) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 5] []) (.flag .CF)) #v[700, 689]
    (.letOp (n := 707) (.exec 0x120ac1 (fun s => s.RIP = 0x120ac1) (addR64R64Effect 0x120ac1 9 5) (Reg.operands [.gpr 9, .gpr 5] [])) #v[700, 689]
    (.letOp (n := 708) (.out 0x120ac4 (atFlags StatusFlags.CF (adcR64R64Effect 0x120ac4 15 13)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[703, 687, 706]
    (.letOp (n := 709) (.exec 0x120ac4 (fun s => s.RIP = 0x120ac4) (atFlags StatusFlags.CF (adcR64R64Effect 0x120ac4 15 13)) (Reg.operands [.gpr 15, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[703, 687, 706]
    (.letOp (n := 710) (.out 0x120ac7 (addR64R64Effect 0x120ac7 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[695, 705]
    (.letOp (n := 711) (.out 0x120ac7 (addR64R64Effect 0x120ac7 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[695, 705]
    (.letOp (n := 712) (.exec 0x120ac7 (fun s => s.RIP = 0x120ac7) (addR64R64Effect 0x120ac7 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[695, 705]
    (.letOp (n := 713) (.out 0x120aca (atFlags StatusFlags.CF (adcR64R64Effect 0x120aca 15 2)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[708, 696, 711]
    (.letOp (n := 714) (.exec 0x120aca (fun s => s.RIP = 0x120aca) (atFlags StatusFlags.CF (adcR64R64Effect 0x120aca 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[708, 696, 711]
    (.letOp (n := 715) (.out 0x120acd (addR64R64Effect 0x120acd 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[710, 647]
    (.letOp (n := 716) (.out 0x120acd (addR64R64Effect 0x120acd 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[710, 647]
    (.letOp (n := 717) (.exec 0x120acd (fun s => s.RIP = 0x120acd) (addR64R64Effect 0x120acd 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[710, 647]
    (.letOp (n := 718) (.out 0x120ad0 (atFlags StatusFlags.CF (adcR64R64Effect 0x120ad0 15 1)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[713, 645, 716]
    (.letOp (n := 719) (.exec 0x120ad0 (fun s => s.RIP = 0x120ad0) (atFlags StatusFlags.CF (adcR64R64Effect 0x120ad0 15 1)) (Reg.operands [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[713, 645, 716]
    (.letOp (n := 720) (.out 0x120ad3 (movR64R64Effect 0x120ad3 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[718]
    (.letOp (n := 721) (.exec 0x120ad3 (fun s => s.RIP = 0x120ad3) (movR64R64Effect 0x120ad3 3 15) (Reg.operands [.gpr 15] [])) #v[718]
    (.letOp (n := 722) (.out 0x120ad6 (shldR64R64Effect 0x120ad6 5 15 0 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[718, 715]
    (.letOp (n := 723) (.exec 0x120ad6 (fun s => s.RIP = 0x120ad6) (shldR64R64Effect 0x120ad6 5 15 0 12) (Reg.operands [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[718, 715]
    (.letOp (n := 724) (.out 0x120adb (shlR64Effect 0x120adb 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[715]
    (.letOp (n := 725) (.exec 0x120adb (fun s => s.RIP = 0x120adb) (shlR64Effect 0x120adb 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[715]
    (.letOp (n := 726) (.out 0x120adf (movR64Imm64Effect 0x120adf 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 727) (.exec 0x120adf (fun s => s.RIP = 0x120adf) (movR64Imm64Effect 0x120adf 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 728) (.out 0x120ae9 (andR64R64Effect 0x120ae9 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[724, 726]
    (.letOp (n := 729) (.exec 0x120ae9 (fun s => s.RIP = 0x120ae9) (andR64R64Effect 0x120ae9 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[724, 726]
    (.letOp (n := 730) (.out 0x120aec (orR64R64Effect 0x120aec 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[728, 698]
    (.letOp (n := 731) (.exec 0x120aec (fun s => s.RIP = 0x120aec) (orR64R64Effect 0x120aec 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[728, 698]
    (.letOp (n := 732) (.out 0x120aef (movR64Imm64Effect 0x120aef 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 733) (.exec 0x120aef (fun s => s.RIP = 0x120aef) (movR64Imm64Effect 0x120aef 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 734) (.out 0x120af9 (mulR64Effect 0x120af9 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[732, 730]
    (.letOp (n := 735) (.out 0x120af9 (mulR64Effect 0x120af9 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[732, 730]
    (.letOp (n := 736) (.exec 0x120af9 (fun s => s.RIP = 0x120af9) (mulR64Effect 0x120af9 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[732, 730]
    (.letOp (n := 737) (.out 0x120afc (movR64R64Effect 0x120afc 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[735]
    (.letOp (n := 738) (.exec 0x120afc (fun s => s.RIP = 0x120afc) (movR64R64Effect 0x120afc 6 2) (Reg.operands [.gpr 2] [])) #v[735]
    (.letOp (n := 739) (.out 0x120aff (shrR64Effect 0x120aff 4 3 52) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[720]
    (.letOp (n := 740) (.exec 0x120aff (fun s => s.RIP = 0x120aff) (shrR64Effect 0x120aff 4 3 52) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[720]
    (.letOp (n := 741) (.out 0x120b03 (addR64M64Effect 0x120b03 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[734, 4]
    (.letOp (n := 742) (.out 0x120b03 (addR64M64Effect 0x120b03 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[734, 4]
    (.letOp (n := 743) (.exec 0x120b03 (LoadPre 0x120b03 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120b03 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x120b03 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[734, 4]
    (.letOp (n := 744) (.out 0x120b08 (atFlags StatusFlags.CF (adcR64M64Effect 0x120b08 6 (.sib 4 none 0 (.d8 0x38)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[737, 4, 742]
    (.letOp (n := 745) (.exec 0x120b08 (LoadPre 0x120b08 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x120b08 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x120b08 6 (.sib 4 none 0 (.d8 0x38)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[737, 4, 742]
    (b_l12065f_16))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_15 : List UInt8 :=
  [0x49, 0x01, 0xF1, 0x4D, 0x11, 0xE7, 0x49, 0x01, 0xE9, 0x4D, 0x11, 0xEF, 0x4C, 0x01, 0xC8, 0x49,
    0x11, 0xD7, 0x48, 0x01, 0xD8, 0x49, 0x11, 0xCF, 0x4C, 0x89, 0xFB, 0x49, 0x0F, 0xA4, 0xC7, 0x0C,
    0x48, 0xC1, 0xE0, 0x04, 0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21,
    0xC8, 0x4C, 0x09, 0xD8, 0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7,
    0xE1, 0x48, 0x89, 0xD6, 0x48, 0xC1, 0xEB, 0x34, 0x48, 0x03, 0x44, 0x24, 0x18, 0x48, 0x13, 0x74,
    0x24, 0x38] ++ bytes_l12065f_16

theorem code_l12065f_15 : ∀ x ∈ codeRange 0x120abb bytes_l12065f_15, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20abb 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_16

def b_l12065f_14 : Block Op Label signature Reg.count 656 :=
  .letOp (n := 656) (.out 0x120a6f (movR64R64Effect 0x120a6f 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[564]
    (.letOp (n := 657) (.exec 0x120a6f (fun s => s.RIP = 0x120a6f) (movR64R64Effect 0x120a6f 0 7) (Reg.operands [.gpr 7] [])) #v[564]
    (.letOp (n := 658) (.out 0x120a72 (mulM64Effect 0x120a72 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[656, 4]
    (.letOp (n := 659) (.out 0x120a72 (mulM64Effect 0x120a72 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[656, 4]
    (.letOp (n := 660) (.exec 0x120a72 (LoadPre 0x120a72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x120a72 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120a72 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[656, 4]
    (.letOp (n := 661) (.out 0x120a77 (movR64R64Effect 0x120a77 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[658]
    (.letOp (n := 662) (.exec 0x120a77 (fun s => s.RIP = 0x120a77) (movR64R64Effect 0x120a77 6 0) (Reg.operands [.gpr 0] [])) #v[658]
    (.letOp (n := 663) (.out 0x120a7a (movR64R64Effect 0x120a7a 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[659]
    (.letOp (n := 664) (.exec 0x120a7a (fun s => s.RIP = 0x120a7a) (movR64R64Effect 0x120a7a 12 2) (Reg.operands [.gpr 2] [])) #v[659]
    (.letOp (n := 665) (.out 0x120a7d (movR64R64Effect 0x120a7d 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 14] []) (.reg (.gpr 11))) #v[638]
    (.letOp (n := 666) (.exec 0x120a7d (fun s => s.RIP = 0x120a7d) (movR64R64Effect 0x120a7d 11 14) (Reg.operands [.gpr 14] [])) #v[638]
    (.letOp (n := 667) (.out 0x120a80 (shrR64Effect 0x120a80 4 11 48) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[665]
    (.letOp (n := 668) (.exec 0x120a80 (fun s => s.RIP = 0x120a80) (shrR64Effect 0x120a80 4 11 48) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[665]
    (.letOp (n := 669) (.out 0x120a84 (movR64M64Effect 0x120a84 10 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 670) (.exec 0x120a84 (LoadPre 0x120a84 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x120a84 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120a84 10 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 671) (.out 0x120a89 (movR64R64Effect 0x120a89 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[669]
    (.letOp (n := 672) (.exec 0x120a89 (fun s => s.RIP = 0x120a89) (movR64R64Effect 0x120a89 0 10) (Reg.operands [.gpr 10] [])) #v[669]
    (.letOp (n := 673) (.out 0x120a8c (mulM64Effect 0x120a8c 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[671, 4]
    (.letOp (n := 674) (.out 0x120a8c (mulM64Effect 0x120a8c 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[671, 4]
    (.letOp (n := 675) (.exec 0x120a8c (LoadPre 0x120a8c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x120a8c + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120a8c 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[671, 4]
    (.letOp (n := 676) (.out 0x120a91 (movR64R64Effect 0x120a91 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[674]
    (.letOp (n := 677) (.exec 0x120a91 (fun s => s.RIP = 0x120a91) (movR64R64Effect 0x120a91 15 2) (Reg.operands [.gpr 2] [])) #v[674]
    (.letOp (n := 678) (.out 0x120a94 (movR64R64Effect 0x120a94 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[673]
    (.letOp (n := 679) (.exec 0x120a94 (fun s => s.RIP = 0x120a94) (movR64R64Effect 0x120a94 9 0) (Reg.operands [.gpr 0] [])) #v[673]
    (.letOp (n := 680) (.out 0x120a97 (movR64M64Effect 0x120a97 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 681) (.exec 0x120a97 (LoadPre 0x120a97 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x120a97 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120a97 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 682) (.out 0x120a9c (movR64R64Effect 0x120a9c 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[680]
    (.letOp (n := 683) (.exec 0x120a9c (fun s => s.RIP = 0x120a9c) (movR64R64Effect 0x120a9c 0 7) (Reg.operands [.gpr 7] [])) #v[680]
    (.letOp (n := 684) (.out 0x120a9f (mulM64Effect 0x120a9f 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[682, 4]
    (.letOp (n := 685) (.out 0x120a9f (mulM64Effect 0x120a9f 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[682, 4]
    (.letOp (n := 686) (.exec 0x120a9f (LoadPre 0x120a9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x120a9f + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120a9f 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[682, 4]
    (.letOp (n := 687) (.out 0x120aa4 (movR64R64Effect 0x120aa4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[685]
    (.letOp (n := 688) (.exec 0x120aa4 (fun s => s.RIP = 0x120aa4) (movR64R64Effect 0x120aa4 13 2) (Reg.operands [.gpr 2] [])) #v[685]
    (.letOp (n := 689) (.out 0x120aa7 (movR64R64Effect 0x120aa7 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[684]
    (.letOp (n := 690) (.exec 0x120aa7 (fun s => s.RIP = 0x120aa7) (movR64R64Effect 0x120aa7 5 0) (Reg.operands [.gpr 0] [])) #v[684]
    (.letOp (n := 691) (.out 0x120aaa (movR64M64Effect 0x120aaa 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 692) (.exec 0x120aaa (LoadPre 0x120aaa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x120aaa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120aaa 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 693) (.out 0x120aaf (movR64M64Effect 0x120aaf 8 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 694) (.exec 0x120aaf (LoadPre 0x120aaf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x120aaf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120aaf 8 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 695) (.out 0x120ab4 (mulR64Effect 0x120ab4 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[693, 691]
    (.letOp (n := 696) (.out 0x120ab4 (mulR64Effect 0x120ab4 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[693, 691]
    (.letOp (n := 697) (.exec 0x120ab4 (fun s => s.RIP = 0x120ab4) (mulR64Effect 0x120ab4 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[693, 691]
    (.letOp (n := 698) (.out 0x120ab7 (andR32Imm8Effect 0x120ab7 4 11 0xf) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[667]
    (.letOp (n := 699) (.exec 0x120ab7 (fun s => s.RIP = 0x120ab7) (andR32Imm8Effect 0x120ab7 4 11 0xf) (Reg.operands [.gpr 11] [])) #v[667]
    (b_l12065f_15))))))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_14 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24, 0x48, 0x48, 0x89, 0xC6, 0x49, 0x89, 0xD4, 0x4D, 0x89,
    0xF3, 0x49, 0xC1, 0xEB, 0x30, 0x4C, 0x8B, 0x54, 0x24, 0x78, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0x64,
    0x24, 0x30, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC1, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x48, 0x89, 0xF8,
    0x48, 0xF7, 0x64, 0x24, 0x40, 0x49, 0x89, 0xD5, 0x48, 0x89, 0xC5, 0x48, 0x8B, 0x44, 0x24, 0x20,
    0x4C, 0x8B, 0x44, 0x24, 0x58, 0x49, 0xF7, 0xE0, 0x41, 0x83, 0xE3, 0x0F] ++ bytes_l12065f_15

theorem code_l12065f_14 : ∀ x ∈ codeRange 0x120a6f bytes_l12065f_14, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20a6f 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_15

def b_l12065f_13 : Block Op Label signature Reg.count 611 :=
  .letOp (n := 611) (.out 0x120a25 (shrR64Effect 0x120a25 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[553]
    (.letOp (n := 612) (.exec 0x120a25 (fun s => s.RIP = 0x120a25) (shrR64Effect 0x120a25 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[553]
    (.letOp (n := 613) (.out 0x120a29 (addR64M64Effect 0x120a29 14 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[573, 4]
    (.letOp (n := 614) (.out 0x120a29 (addR64M64Effect 0x120a29 14 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 4] []) (.flag .CF)) #v[573, 4]
    (.letOp (n := 615) (.exec 0x120a29 (LoadPre 0x120a29 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120a29 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x120a29 14 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[573, 4]
    (.letOp (n := 616) (.out 0x120a2e (atFlags StatusFlags.CF (adcR64M64Effect 0x120a2e 3 (.sib 4 none 0 (.d8 0x38)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[571, 4, 614]
    (.letOp (n := 617) (.exec 0x120a2e (LoadPre 0x120a2e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x120a2e + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x120a2e 3 (.sib 4 none 0 (.d8 0x38)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[571, 4, 614]
    (.letOp (n := 618) (.out 0x120a33 (addR64R64Effect 0x120a33 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[613, 582]
    (.letOp (n := 619) (.out 0x120a33 (addR64R64Effect 0x120a33 14 5) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 5] []) (.flag .CF)) #v[613, 582]
    (.letOp (n := 620) (.exec 0x120a33 (fun s => s.RIP = 0x120a33) (addR64R64Effect 0x120a33 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[613, 582]
    (.letOp (n := 621) (.out 0x120a36 (atFlags StatusFlags.CF (adcR64R64Effect 0x120a36 3 11)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[616, 580, 619]
    (.letOp (n := 622) (.exec 0x120a36 (fun s => s.RIP = 0x120a36) (atFlags StatusFlags.CF (adcR64R64Effect 0x120a36 3 11)) (Reg.operands [.gpr 3, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[616, 580, 619]
    (.letOp (n := 623) (.out 0x120a39 (addR64R64Effect 0x120a39 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[618, 591]
    (.letOp (n := 624) (.out 0x120a39 (addR64R64Effect 0x120a39 14 8) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 8] []) (.flag .CF)) #v[618, 591]
    (.letOp (n := 625) (.exec 0x120a39 (fun s => s.RIP = 0x120a39) (addR64R64Effect 0x120a39 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[618, 591]
    (.letOp (n := 626) (.out 0x120a3c (atFlags StatusFlags.CF (adcR64R64Effect 0x120a3c 3 15)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[621, 589, 624]
    (.letOp (n := 627) (.exec 0x120a3c (fun s => s.RIP = 0x120a3c) (atFlags StatusFlags.CF (adcR64R64Effect 0x120a3c 3 15)) (Reg.operands [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[621, 589, 624]
    (.letOp (n := 628) (.out 0x120a3f (addR64R64Effect 0x120a3f 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[623, 602]
    (.letOp (n := 629) (.out 0x120a3f (addR64R64Effect 0x120a3f 14 12) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 12] []) (.flag .CF)) #v[623, 602]
    (.letOp (n := 630) (.exec 0x120a3f (fun s => s.RIP = 0x120a3f) (addR64R64Effect 0x120a3f 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[623, 602]
    (.letOp (n := 631) (.out 0x120a42 (atFlags StatusFlags.CF (adcR64R64Effect 0x120a42 3 9)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[626, 600, 629]
    (.letOp (n := 632) (.exec 0x120a42 (fun s => s.RIP = 0x120a42) (atFlags StatusFlags.CF (adcR64R64Effect 0x120a42 3 9)) (Reg.operands [.gpr 3, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[626, 600, 629]
    (.letOp (n := 633) (.out 0x120a45 (addR64R64Effect 0x120a45 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[628, 608]
    (.letOp (n := 634) (.out 0x120a45 (addR64R64Effect 0x120a45 14 0) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 0] []) (.flag .CF)) #v[628, 608]
    (.letOp (n := 635) (.exec 0x120a45 (fun s => s.RIP = 0x120a45) (addR64R64Effect 0x120a45 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[628, 608]
    (.letOp (n := 636) (.out 0x120a48 (atFlags StatusFlags.CF (adcR64R64Effect 0x120a48 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[631, 609, 634]
    (.letOp (n := 637) (.exec 0x120a48 (fun s => s.RIP = 0x120a48) (atFlags StatusFlags.CF (adcR64R64Effect 0x120a48 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[631, 609, 634]
    (.letOp (n := 638) (.out 0x120a4b (addR64R64Effect 0x120a4b 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[633, 555]
    (.letOp (n := 639) (.out 0x120a4b (addR64R64Effect 0x120a4b 14 6) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 6] []) (.flag .CF)) #v[633, 555]
    (.letOp (n := 640) (.exec 0x120a4b (fun s => s.RIP = 0x120a4b) (addR64R64Effect 0x120a4b 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[633, 555]
    (.letOp (n := 641) (.out 0x120a4e (atFlags StatusFlags.CF (adcR64R64Effect 0x120a4e 3 1)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[636, 611, 639]
    (.letOp (n := 642) (.exec 0x120a4e (fun s => s.RIP = 0x120a4e) (atFlags StatusFlags.CF (adcR64R64Effect 0x120a4e 3 1)) (Reg.operands [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[636, 611, 639]
    (.letOp (n := 643) (.out 0x120a51 (movR64R64Effect 0x120a51 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[641]
    (.letOp (n := 644) (.exec 0x120a51 (fun s => s.RIP = 0x120a51) (movR64R64Effect 0x120a51 1 3) (Reg.operands [.gpr 3] [])) #v[641]
    (.letOp (n := 645) (.out 0x120a54 (shrR64Effect 0x120a54 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[643]
    (.letOp (n := 646) (.exec 0x120a54 (fun s => s.RIP = 0x120a54) (shrR64Effect 0x120a54 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[643]
    (.letOp (n := 647) (.out 0x120a58 (shldR64R64Effect 0x120a58 5 3 14 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[641, 638]
    (.letOp (n := 648) (.exec 0x120a58 (fun s => s.RIP = 0x120a58) (shldR64R64Effect 0x120a58 5 3 14 12) (Reg.operands [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[641, 638]
    (.letOp (n := 649) (.out 0x120a5d (movR64M64Effect 0x120a5d 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 650) (.exec 0x120a5d (LoadPre 0x120a5d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120a5d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120a5d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 651) (.out 0x120a62 (mulR64Effect 0x120a62 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[598, 649]
    (.letOp (n := 652) (.out 0x120a62 (mulR64Effect 0x120a62 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[598, 649]
    (.letOp (n := 653) (.exec 0x120a62 (fun s => s.RIP = 0x120a62) (mulR64Effect 0x120a62 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[598, 649]
    (.letOp (n := 654) (.exec 0x120a65 (StorePre 0x120a65 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x120a65 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120a65 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[652, 4]
    (.letOp (n := 655) (.exec 0x120a6a (StorePre 0x120a6a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120a6a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120a6a 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[651, 4]
    (b_l12065f_14)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_13 : List UInt8 :=
  [0x48, 0xC1, 0xE9, 0x34, 0x4C, 0x03, 0x74, 0x24, 0x18, 0x48, 0x13, 0x5C, 0x24, 0x38, 0x49, 0x01,
    0xEE, 0x4C, 0x11, 0xDB, 0x4D, 0x01, 0xC6, 0x4C, 0x11, 0xFB, 0x4D, 0x01, 0xE6, 0x4C, 0x11, 0xCB,
    0x49, 0x01, 0xC6, 0x48, 0x11, 0xD3, 0x49, 0x01, 0xF6, 0x48, 0x11, 0xCB, 0x48, 0x89, 0xD9, 0x48,
    0xC1, 0xE9, 0x34, 0x4C, 0x0F, 0xA4, 0xF3, 0x0C, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x49, 0xF7, 0xE2,
    0x48, 0x89, 0x54, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x18] ++ bytes_l12065f_14

theorem code_l12065f_13 : ∀ x ∈ codeRange 0x120a25 bytes_l12065f_13, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20a25 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_14

def b_l12065f_12 : Block Op Label signature Reg.count 566 :=
  .letOp (n := 566) (.out 0x1209e0 (movR64R64Effect 0x1209e0 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[564]
    (.letOp (n := 567) (.exec 0x1209e0 (fun s => s.RIP = 0x1209e0) (movR64R64Effect 0x1209e0 0 7) (Reg.operands [.gpr 7] [])) #v[564]
    (.letOp (n := 568) (.out 0x1209e3 (mulR64Effect 0x1209e3 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[465, 566]
    (.letOp (n := 569) (.out 0x1209e3 (mulR64Effect 0x1209e3 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[465, 566]
    (.letOp (n := 570) (.exec 0x1209e3 (fun s => s.RIP = 0x1209e3) (mulR64Effect 0x1209e3 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[465, 566]
    (.letOp (n := 571) (.out 0x1209e6 (movR64R64Effect 0x1209e6 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[569]
    (.letOp (n := 572) (.exec 0x1209e6 (fun s => s.RIP = 0x1209e6) (movR64R64Effect 0x1209e6 3 2) (Reg.operands [.gpr 2] [])) #v[569]
    (.letOp (n := 573) (.out 0x1209e9 (movR64R64Effect 0x1209e9 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[568]
    (.letOp (n := 574) (.exec 0x1209e9 (fun s => s.RIP = 0x1209e9) (movR64R64Effect 0x1209e9 14 0) (Reg.operands [.gpr 0] [])) #v[568]
    (.letOp (n := 575) (.out 0x1209ec (movR64R64Effect 0x1209ec 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[490]
    (.letOp (n := 576) (.exec 0x1209ec (fun s => s.RIP = 0x1209ec) (movR64R64Effect 0x1209ec 0 8) (Reg.operands [.gpr 8] [])) #v[490]
    (.letOp (n := 577) (.out 0x1209ef (mulM64Effect 0x1209ef 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[575, 4]
    (.letOp (n := 578) (.out 0x1209ef (mulM64Effect 0x1209ef 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[575, 4]
    (.letOp (n := 579) (.exec 0x1209ef (LoadPre 0x1209ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1209ef + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1209ef 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[575, 4]
    (.letOp (n := 580) (.out 0x1209f4 (movR64R64Effect 0x1209f4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[578]
    (.letOp (n := 581) (.exec 0x1209f4 (fun s => s.RIP = 0x1209f4) (movR64R64Effect 0x1209f4 11 2) (Reg.operands [.gpr 2] [])) #v[578]
    (.letOp (n := 582) (.out 0x1209f7 (movR64R64Effect 0x1209f7 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[577]
    (.letOp (n := 583) (.exec 0x1209f7 (fun s => s.RIP = 0x1209f7) (movR64R64Effect 0x1209f7 5 0) (Reg.operands [.gpr 0] [])) #v[577]
    (.letOp (n := 584) (.out 0x1209fa (movR64R64Effect 0x1209fa 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[460]
    (.letOp (n := 585) (.exec 0x1209fa (fun s => s.RIP = 0x1209fa) (movR64R64Effect 0x1209fa 0 10) (Reg.operands [.gpr 10] [])) #v[460]
    (.letOp (n := 586) (.out 0x1209fd (mulR64Effect 0x1209fd 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[493, 584]
    (.letOp (n := 587) (.out 0x1209fd (mulR64Effect 0x1209fd 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[493, 584]
    (.letOp (n := 588) (.exec 0x1209fd (fun s => s.RIP = 0x1209fd) (mulR64Effect 0x1209fd 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[493, 584]
    (.letOp (n := 589) (.out 0x120a00 (movR64R64Effect 0x120a00 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[587]
    (.letOp (n := 590) (.exec 0x120a00 (fun s => s.RIP = 0x120a00) (movR64R64Effect 0x120a00 15 2) (Reg.operands [.gpr 2] [])) #v[587]
    (.letOp (n := 591) (.out 0x120a03 (movR64R64Effect 0x120a03 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[586]
    (.letOp (n := 592) (.exec 0x120a03 (fun s => s.RIP = 0x120a03) (movR64R64Effect 0x120a03 8 0) (Reg.operands [.gpr 0] [])) #v[586]
    (.letOp (n := 593) (.out 0x120a06 (movR64R64Effect 0x120a06 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[524]
    (.letOp (n := 594) (.exec 0x120a06 (fun s => s.RIP = 0x120a06) (movR64R64Effect 0x120a06 0 9) (Reg.operands [.gpr 9] [])) #v[524]
    (.letOp (n := 595) (.out 0x120a09 (mulR64Effect 0x120a09 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[510, 593]
    (.letOp (n := 596) (.out 0x120a09 (mulR64Effect 0x120a09 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[510, 593]
    (.letOp (n := 597) (.exec 0x120a09 (fun s => s.RIP = 0x120a09) (mulR64Effect 0x120a09 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[510, 593]
    (.letOp (n := 598) (.out 0x120a0c (movR64R64Effect 0x120a0c 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 12] []) (.reg (.gpr 10))) #v[510]
    (.letOp (n := 599) (.exec 0x120a0c (fun s => s.RIP = 0x120a0c) (movR64R64Effect 0x120a0c 10 12) (Reg.operands [.gpr 12] [])) #v[510]
    (.letOp (n := 600) (.out 0x120a0f (movR64R64Effect 0x120a0f 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[596]
    (.letOp (n := 601) (.exec 0x120a0f (fun s => s.RIP = 0x120a0f) (movR64R64Effect 0x120a0f 9 2) (Reg.operands [.gpr 2] [])) #v[596]
    (.letOp (n := 602) (.out 0x120a12 (movR64R64Effect 0x120a12 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[595]
    (.letOp (n := 603) (.exec 0x120a12 (fun s => s.RIP = 0x120a12) (movR64R64Effect 0x120a12 12 0) (Reg.operands [.gpr 0] [])) #v[595]
    (.letOp (n := 604) (.out 0x120a15 (movR64R64Effect 0x120a15 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[536]
    (.letOp (n := 605) (.exec 0x120a15 (fun s => s.RIP = 0x120a15) (movR64R64Effect 0x120a15 0 13) (Reg.operands [.gpr 13] [])) #v[536]
    (.letOp (n := 606) (.out 0x120a18 (movR64Imm64Effect 0x120a18 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 607) (.exec 0x120a18 (fun s => s.RIP = 0x120a18) (movR64Imm64Effect 0x120a18 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 608) (.out 0x120a22 (mulR64Effect 0x120a22 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[606, 604]
    (.letOp (n := 609) (.out 0x120a22 (mulR64Effect 0x120a22 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[606, 604]
    (.letOp (n := 610) (.exec 0x120a22 (fun s => s.RIP = 0x120a22) (mulR64Effect 0x120a22 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[606, 604]
    (b_l12065f_13)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_12 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC6, 0x4C, 0x89, 0xC0, 0x48,
    0xF7, 0x64, 0x24, 0x40, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC5, 0x4C, 0x89, 0xD0, 0x49, 0xF7, 0xE7,
    0x49, 0x89, 0xD7, 0x49, 0x89, 0xC0, 0x4C, 0x89, 0xC8, 0x49, 0xF7, 0xE4, 0x4D, 0x89, 0xE2, 0x49,
    0x89, 0xD1, 0x49, 0x89, 0xC4, 0x4C, 0x89, 0xE8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00,
    0x00, 0x00, 0x48, 0xF7, 0xE2] ++ bytes_l12065f_13

theorem code_l12065f_12 : ∀ x ∈ codeRange 0x1209e0 bytes_l12065f_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x209e0 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_13

def b_l12065f_11 : Block Op Label signature Reg.count 526 :=
  .letOp (n := 526) (.exec 0x12098d (StorePre 0x12098d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x12098d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12098d 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[445, 4]
    (.letOp (n := 527) (.out 0x120992 (movR64R64Effect 0x120992 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[445]
    (.letOp (n := 528) (.exec 0x120992 (fun s => s.RIP = 0x120992) (movR64R64Effect 0x120992 0 13) (Reg.operands [.gpr 13] [])) #v[445]
    (.letOp (n := 529) (.out 0x120995 (movR64M64Effect 0x120995 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 530) (.exec 0x120995 (LoadPre 0x120995 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x120995 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120995 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 531) (.out 0x12099a (mulR64Effect 0x12099a 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[529, 527]
    (.letOp (n := 532) (.out 0x12099a (mulR64Effect 0x12099a 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[529, 527]
    (.letOp (n := 533) (.exec 0x12099a (fun s => s.RIP = 0x12099a) (mulR64Effect 0x12099a 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[529, 527]
    (.letOp (n := 534) (.out 0x12099d (movR64R64Effect 0x12099d 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[532]
    (.letOp (n := 535) (.exec 0x12099d (fun s => s.RIP = 0x12099d) (movR64R64Effect 0x12099d 13 2) (Reg.operands [.gpr 2] [])) #v[532]
    (.letOp (n := 536) (.out 0x1209a0 (shldR64R64Effect 0x1209a0 5 13 0 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[534, 531]
    (.letOp (n := 537) (.exec 0x1209a0 (fun s => s.RIP = 0x1209a0) (shldR64R64Effect 0x1209a0 5 13 0 12) (Reg.operands [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[534, 531]
    (.letOp (n := 538) (.out 0x1209a5 (andR64R64Effect 0x1209a5 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[531, 447]
    (.letOp (n := 539) (.exec 0x1209a5 (fun s => s.RIP = 0x1209a5) (andR64R64Effect 0x1209a5 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[531, 447]
    (.letOp (n := 540) (.out 0x1209a8 (movR64Imm64Effect 0x1209a8 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 541) (.exec 0x1209a8 (fun s => s.RIP = 0x1209a8) (movR64Imm64Effect 0x1209a8 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 542) (.out 0x1209b2 (mulR64Effect 0x1209b2 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[540, 538]
    (.letOp (n := 543) (.out 0x1209b2 (mulR64Effect 0x1209b2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[540, 538]
    (.letOp (n := 544) (.exec 0x1209b2 (fun s => s.RIP = 0x1209b2) (mulR64Effect 0x1209b2 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[540, 538]
    (.letOp (n := 545) (.out 0x1209b5 (movR64R64Effect 0x1209b5 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[543]
    (.letOp (n := 546) (.exec 0x1209b5 (fun s => s.RIP = 0x1209b5) (movR64R64Effect 0x1209b5 6 2) (Reg.operands [.gpr 2] [])) #v[543]
    (.letOp (n := 547) (.out 0x1209b8 (addR64R64Effect 0x1209b8 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[542, 519]
    (.letOp (n := 548) (.out 0x1209b8 (addR64R64Effect 0x1209b8 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[542, 519]
    (.letOp (n := 549) (.exec 0x1209b8 (fun s => s.RIP = 0x1209b8) (addR64R64Effect 0x1209b8 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[542, 519]
    (.letOp (n := 550) (.exec 0x1209bb (StorePre 0x1209bb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1209bb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1209bb 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[547, 4]
    (.letOp (n := 551) (.out 0x1209c0 (atFlags StatusFlags.CF (adcR64R64Effect 0x1209c0 6 11)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[545, 522, 548]
    (.letOp (n := 552) (.exec 0x1209c0 (fun s => s.RIP = 0x1209c0) (atFlags StatusFlags.CF (adcR64R64Effect 0x1209c0 6 11)) (Reg.operands [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[545, 522, 548]
    (.letOp (n := 553) (.out 0x1209c3 (movR64R64Effect 0x1209c3 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[551]
    (.letOp (n := 554) (.exec 0x1209c3 (fun s => s.RIP = 0x1209c3) (movR64R64Effect 0x1209c3 1 6) (Reg.operands [.gpr 6] [])) #v[551]
    (.letOp (n := 555) (.out 0x1209c6 (shldR64R64Effect 0x1209c6 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[551, 547]
    (.letOp (n := 556) (.exec 0x1209c6 (fun s => s.RIP = 0x1209c6) (shldR64R64Effect 0x1209c6 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[551, 547]
    (.letOp (n := 557) (.out 0x1209cb (movR64R64Effect 0x1209cb 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[451]
    (.letOp (n := 558) (.exec 0x1209cb (fun s => s.RIP = 0x1209cb) (movR64R64Effect 0x1209cb 0 14) (Reg.operands [.gpr 14] [])) #v[451]
    (.letOp (n := 559) (.out 0x1209ce (mulR64Effect 0x1209ce 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[529, 557]
    (.letOp (n := 560) (.out 0x1209ce (mulR64Effect 0x1209ce 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[529, 557]
    (.letOp (n := 561) (.exec 0x1209ce (fun s => s.RIP = 0x1209ce) (mulR64Effect 0x1209ce 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[529, 557]
    (.letOp (n := 562) (.exec 0x1209d1 (StorePre 0x1209d1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1209d1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1209d1 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[560, 4]
    (.letOp (n := 563) (.exec 0x1209d6 (StorePre 0x1209d6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1209d6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1209d6 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[559, 4]
    (.letOp (n := 564) (.out 0x1209db (movR64M64Effect 0x1209db 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 565) (.exec 0x1209db (LoadPre 0x1209db (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1209db + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1209db 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l12065f_12))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_11 : List UInt8 :=
  [0x4C, 0x89, 0x6C, 0x24, 0x20, 0x4C, 0x89, 0xE8, 0x48, 0x8B, 0x7C, 0x24, 0x48, 0x48, 0xF7, 0xE7,
    0x49, 0x89, 0xD5, 0x49, 0x0F, 0xA4, 0xC5, 0x0C, 0x48, 0x21, 0xC8, 0x48, 0xB9, 0x10, 0x3D, 0x00,
    0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD6, 0x48, 0x01, 0xD8, 0x48, 0x89,
    0x44, 0x24, 0x60, 0x4C, 0x11, 0xDE, 0x48, 0x89, 0xF1, 0x48, 0x0F, 0xA4, 0xC6, 0x0C, 0x4C, 0x89,
    0xF0, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0x54, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B,
    0x7C, 0x24, 0x08] ++ bytes_l12065f_12

theorem code_l12065f_11 : ∀ x ∈ codeRange 0x12098d bytes_l12065f_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2098d 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_12

def b_l12065f_10 : Block Op Label signature Reg.count 483 :=
  .letOp (n := 483) (.out 0x120949 (addR64R64Effect 0x120949 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[481, 472]
    (.letOp (n := 484) (.out 0x120949 (addR64R64Effect 0x120949 3 9) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 9] []) (.flag .CF)) #v[481, 472]
    (.letOp (n := 485) (.exec 0x120949 (fun s => s.RIP = 0x120949) (addR64R64Effect 0x120949 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[481, 472]
    (.letOp (n := 486) (.out 0x12094c (atFlags StatusFlags.CF (adcR64R64Effect 0x12094c 11 6)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[479, 470, 484]
    (.letOp (n := 487) (.exec 0x12094c (fun s => s.RIP = 0x12094c) (atFlags StatusFlags.CF (adcR64R64Effect 0x12094c 11 6)) (Reg.operands [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[479, 470, 484]
    (.letOp (n := 488) (.out 0x12094f (movR64R64Effect 0x12094f 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[458]
    (.letOp (n := 489) (.exec 0x12094f (fun s => s.RIP = 0x12094f) (movR64R64Effect 0x12094f 0 7) (Reg.operands [.gpr 7] [])) #v[458]
    (.letOp (n := 490) (.out 0x120952 (movR64R64Effect 0x120952 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[458]
    (.letOp (n := 491) (.exec 0x120952 (fun s => s.RIP = 0x120952) (movR64R64Effect 0x120952 8 7) (Reg.operands [.gpr 7] [])) #v[458]
    (.letOp (n := 492) (.exec 0x120955 (StorePre 0x120955 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x120955 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120955 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[458, 4]
    (.letOp (n := 493) (.out 0x12095a (movR64M64Effect 0x12095a 15 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 494) (.exec 0x12095a (LoadPre 0x12095a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12095a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12095a 15 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 495) (.out 0x12095f (mulR64Effect 0x12095f 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[493, 488]
    (.letOp (n := 496) (.out 0x12095f (mulR64Effect 0x12095f 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[493, 488]
    (.letOp (n := 497) (.exec 0x12095f (fun s => s.RIP = 0x12095f) (mulR64Effect 0x12095f 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[493, 488]
    (.letOp (n := 498) (.out 0x120962 (movR64R64Effect 0x120962 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[496]
    (.letOp (n := 499) (.exec 0x120962 (fun s => s.RIP = 0x120962) (movR64R64Effect 0x120962 6 2) (Reg.operands [.gpr 2] [])) #v[496]
    (.letOp (n := 500) (.out 0x120965 (movR64R64Effect 0x120965 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[495]
    (.letOp (n := 501) (.exec 0x120965 (fun s => s.RIP = 0x120965) (movR64R64Effect 0x120965 9 0) (Reg.operands [.gpr 0] [])) #v[495]
    (.letOp (n := 502) (.out 0x120968 (addR64R64Effect 0x120968 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[500, 483]
    (.letOp (n := 503) (.out 0x120968 (addR64R64Effect 0x120968 9 3) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 3] []) (.flag .CF)) #v[500, 483]
    (.letOp (n := 504) (.exec 0x120968 (fun s => s.RIP = 0x120968) (addR64R64Effect 0x120968 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[500, 483]
    (.letOp (n := 505) (.out 0x12096b (atFlags StatusFlags.CF (adcR64R64Effect 0x12096b 6 11)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[498, 486, 503]
    (.letOp (n := 506) (.exec 0x12096b (fun s => s.RIP = 0x12096b) (atFlags StatusFlags.CF (adcR64R64Effect 0x12096b 6 11)) (Reg.operands [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[498, 486, 503]
    (.letOp (n := 507) (.out 0x12096e (movR64R64Effect 0x12096e 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[460]
    (.letOp (n := 508) (.exec 0x12096e (fun s => s.RIP = 0x12096e) (movR64R64Effect 0x12096e 0 10) (Reg.operands [.gpr 10] [])) #v[460]
    (.letOp (n := 509) (.exec 0x120971 (StorePre 0x120971 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x120971 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120971 10 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[460, 4]
    (.letOp (n := 510) (.out 0x120976 (movR64M64Effect 0x120976 12 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 511) (.exec 0x120976 (LoadPre 0x120976 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x120976 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120976 12 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 512) (.out 0x12097b (mulR64Effect 0x12097b 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[510, 507]
    (.letOp (n := 513) (.out 0x12097b (mulR64Effect 0x12097b 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[510, 507]
    (.letOp (n := 514) (.exec 0x12097b (fun s => s.RIP = 0x12097b) (mulR64Effect 0x12097b 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[510, 507]
    (.letOp (n := 515) (.out 0x12097e (movR64R64Effect 0x12097e 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[513]
    (.letOp (n := 516) (.exec 0x12097e (fun s => s.RIP = 0x12097e) (movR64R64Effect 0x12097e 11 2) (Reg.operands [.gpr 2] [])) #v[513]
    (.letOp (n := 517) (.out 0x120981 (movR64R64Effect 0x120981 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[512]
    (.letOp (n := 518) (.exec 0x120981 (fun s => s.RIP = 0x120981) (movR64R64Effect 0x120981 3 0) (Reg.operands [.gpr 0] [])) #v[512]
    (.letOp (n := 519) (.out 0x120984 (addR64R64Effect 0x120984 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[517, 502]
    (.letOp (n := 520) (.out 0x120984 (addR64R64Effect 0x120984 3 9) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 9] []) (.flag .CF)) #v[517, 502]
    (.letOp (n := 521) (.exec 0x120984 (fun s => s.RIP = 0x120984) (addR64R64Effect 0x120984 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[517, 502]
    (.letOp (n := 522) (.out 0x120987 (atFlags StatusFlags.CF (adcR64R64Effect 0x120987 11 6)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[515, 505, 520]
    (.letOp (n := 523) (.exec 0x120987 (fun s => s.RIP = 0x120987) (atFlags StatusFlags.CF (adcR64R64Effect 0x120987 11 6)) (Reg.operands [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[515, 505, 520]
    (.letOp (n := 524) (.out 0x12098a (movR64R64Effect 0x12098a 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 13] []) (.reg (.gpr 9))) #v[445]
    (.letOp (n := 525) (.exec 0x12098a (fun s => s.RIP = 0x12098a) (movR64R64Effect 0x12098a 9 13) (Reg.operands [.gpr 13] [])) #v[445]
    (b_l12065f_11)))))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_10 : List UInt8 :=
  [0x4C, 0x01, 0xCB, 0x49, 0x11, 0xF3, 0x48, 0x89, 0xF8, 0x49, 0x89, 0xF8, 0x48, 0x89, 0x7C, 0x24,
    0x78, 0x4C, 0x8B, 0x7C, 0x24, 0x58, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC1, 0x49,
    0x01, 0xD9, 0x4C, 0x11, 0xDE, 0x4C, 0x89, 0xD0, 0x4C, 0x89, 0x54, 0x24, 0x28, 0x4C, 0x8B, 0x64,
    0x24, 0x50, 0x49, 0xF7, 0xE4, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC3, 0x4C, 0x01, 0xCB, 0x49, 0x11,
    0xF3, 0x4D, 0x89, 0xE9] ++ bytes_l12065f_11

theorem code_l12065f_10 : ∀ x ∈ codeRange 0x120949 bytes_l12065f_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20949 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_11

def b_l12065f_9 : Block Op Label signature Reg.count 443 :=
  .letOp (n := 443) (.out 0x1208fe (addR64R64Effect 0x1208fe 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[441, 435]
    (.letOp (n := 444) (.exec 0x1208fe (fun s => s.RIP = 0x1208fe) (addR64R64Effect 0x1208fe 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[441, 435]
    (.letOp (n := 445) (.out 0x120901 (movR64R64Effect 0x120901 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[443]
    (.letOp (n := 446) (.exec 0x120901 (fun s => s.RIP = 0x120901) (movR64R64Effect 0x120901 13 1) (Reg.operands [.gpr 1] [])) #v[443]
    (.letOp (n := 447) (.out 0x120904 (movR64Imm64Effect 0x120904 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 448) (.exec 0x120904 (fun s => s.RIP = 0x120904) (movR64Imm64Effect 0x120904 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 449) (.out 0x12090e (movR64M64Effect 0x12090e 14 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 450) (.exec 0x12090e (LoadPre 0x12090e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12090e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12090e 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 451) (.out 0x120913 (andR64R64Effect 0x120913 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[449, 447]
    (.letOp (n := 452) (.exec 0x120913 (fun s => s.RIP = 0x120913) (andR64R64Effect 0x120913 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[449, 447]
    (.letOp (n := 453) (.out 0x120916 (andR64R64Effect 0x120916 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[331, 447]
    (.letOp (n := 454) (.exec 0x120916 (fun s => s.RIP = 0x120916) (andR64R64Effect 0x120916 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[331, 447]
    (.letOp (n := 455) (.exec 0x120919 (StorePre 0x120919 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120919 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120919 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[453, 4]
    (.letOp (n := 456) (.out 0x12091e (movR64R64Effect 0x12091e 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9] []) (.reg (.gpr 7))) #v[402]
    (.letOp (n := 457) (.exec 0x12091e (fun s => s.RIP = 0x12091e) (movR64R64Effect 0x12091e 7 9) (Reg.operands [.gpr 9] [])) #v[402]
    (.letOp (n := 458) (.out 0x120921 (andR64R64Effect 0x120921 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[456, 447]
    (.letOp (n := 459) (.exec 0x120921 (fun s => s.RIP = 0x120921) (andR64R64Effect 0x120921 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[456, 447]
    (.letOp (n := 460) (.out 0x120924 (andR64R64Effect 0x120924 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[430, 447]
    (.letOp (n := 461) (.exec 0x120924 (fun s => s.RIP = 0x120924) (andR64R64Effect 0x120924 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[430, 447]
    (.letOp (n := 462) (.out 0x120927 (movR64R64Effect 0x120927 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[451]
    (.letOp (n := 463) (.exec 0x120927 (fun s => s.RIP = 0x120927) (movR64R64Effect 0x120927 0 14) (Reg.operands [.gpr 14] [])) #v[451]
    (.letOp (n := 464) (.exec 0x12092a (StorePre 0x12092a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12092a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12092a 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[451, 4]
    (.letOp (n := 465) (.out 0x12092f (movR64M64Effect 0x12092f 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 466) (.exec 0x12092f (LoadPre 0x12092f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x12092f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12092f 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 467) (.out 0x120934 (mulR64Effect 0x120934 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[465, 462]
    (.letOp (n := 468) (.out 0x120934 (mulR64Effect 0x120934 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[465, 462]
    (.letOp (n := 469) (.exec 0x120934 (fun s => s.RIP = 0x120934) (mulR64Effect 0x120934 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[465, 462]
    (.letOp (n := 470) (.out 0x120937 (movR64R64Effect 0x120937 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[468]
    (.letOp (n := 471) (.exec 0x120937 (fun s => s.RIP = 0x120937) (movR64R64Effect 0x120937 6 2) (Reg.operands [.gpr 2] [])) #v[468]
    (.letOp (n := 472) (.out 0x12093a (movR64R64Effect 0x12093a 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[467]
    (.letOp (n := 473) (.exec 0x12093a (fun s => s.RIP = 0x12093a) (movR64R64Effect 0x12093a 9 0) (Reg.operands [.gpr 0] [])) #v[467]
    (.letOp (n := 474) (.out 0x12093d (movR64R64Effect 0x12093d 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[453]
    (.letOp (n := 475) (.exec 0x12093d (fun s => s.RIP = 0x12093d) (movR64R64Effect 0x12093d 0 8) (Reg.operands [.gpr 8] [])) #v[453]
    (.letOp (n := 476) (.out 0x120940 (mulR64Effect 0x120940 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[387, 474]
    (.letOp (n := 477) (.out 0x120940 (mulR64Effect 0x120940 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[387, 474]
    (.letOp (n := 478) (.exec 0x120940 (fun s => s.RIP = 0x120940) (mulR64Effect 0x120940 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[387, 474]
    (.letOp (n := 479) (.out 0x120943 (movR64R64Effect 0x120943 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[477]
    (.letOp (n := 480) (.exec 0x120943 (fun s => s.RIP = 0x120943) (movR64R64Effect 0x120943 11 2) (Reg.operands [.gpr 2] [])) #v[477]
    (.letOp (n := 481) (.out 0x120946 (movR64R64Effect 0x120946 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[476]
    (.letOp (n := 482) (.exec 0x120946 (fun s => s.RIP = 0x120946) (movR64R64Effect 0x120946 3 0) (Reg.operands [.gpr 0] [])) #v[476]
    (b_l12065f_10))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_9 : List UInt8 :=
  [0x48, 0x01, 0xF9, 0x49, 0x89, 0xCD, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x4C, 0x8B, 0x74, 0x24, 0x10, 0x49, 0x21, 0xCE, 0x49, 0x21, 0xC8, 0x4C, 0x89, 0x44, 0x24, 0x08,
    0x4C, 0x89, 0xCF, 0x48, 0x21, 0xCF, 0x49, 0x21, 0xCA, 0x4C, 0x89, 0xF0, 0x4C, 0x89, 0x74, 0x24,
    0x10, 0x48, 0x8B, 0x6C, 0x24, 0x30, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC1, 0x4C,
    0x89, 0xC0, 0x49, 0xF7, 0xE3, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC3] ++ bytes_l12065f_10

theorem code_l12065f_9 : ∀ x ∈ codeRange 0x1208fe bytes_l12065f_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x208fe 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_10

def b_l12065f_8 : Block Op Label signature Reg.count 399 :=
  .letOp (n := 399) (.out 0x1208a8 (addR64R64Effect 0x1208a8 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[394, 345]
    (.letOp (n := 400) (.out 0x1208a8 (addR64R64Effect 0x1208a8 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[394, 345]
    (.letOp (n := 401) (.exec 0x1208a8 (fun s => s.RIP = 0x1208a8) (addR64R64Effect 0x1208a8 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[394, 345]
    (.letOp (n := 402) (.out 0x1208ab (movR64R64Effect 0x1208ab 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[399]
    (.letOp (n := 403) (.exec 0x1208ab (fun s => s.RIP = 0x1208ab) (movR64R64Effect 0x1208ab 9 0) (Reg.operands [.gpr 0] [])) #v[399]
    (.letOp (n := 404) (.out 0x1208ae (atFlags StatusFlags.CF (adcR64R64Effect 0x1208ae 3 1)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[397, 343, 400]
    (.letOp (n := 405) (.exec 0x1208ae (fun s => s.RIP = 0x1208ae) (atFlags StatusFlags.CF (adcR64R64Effect 0x1208ae 3 1)) (Reg.operands [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[397, 343, 400]
    (.letOp (n := 406) (.out 0x1208b1 (shldR64R64Effect 0x1208b1 5 6 15 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[367, 364]
    (.letOp (n := 407) (.exec 0x1208b1 (fun s => s.RIP = 0x1208b1) (shldR64R64Effect 0x1208b1 5 6 15 12) (Reg.operands [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[367, 364]
    (.letOp (n := 408) (.out 0x1208b6 (movR64Imm64Effect 0x1208b6 1 0xffffffffffffe) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 409) (.exec 0x1208b6 (fun s => s.RIP = 0x1208b6) (movR64Imm64Effect 0x1208b6 1 0xffffffffffffe) (Reg.operands [] [])) #v[]
    (.letOp (n := 410) (.out 0x1208c0 (andR64M64Effect 0x1208c0 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[408, 4]
    (.letOp (n := 411) (.exec 0x1208c0 (LoadPre 0x1208c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1208c0 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x1208c0 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[408, 4]
    (.letOp (n := 412) (.out 0x1208c5 (movR64R64Effect 0x1208c5 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[404]
    (.letOp (n := 413) (.exec 0x1208c5 (fun s => s.RIP = 0x1208c5) (movR64R64Effect 0x1208c5 7 3) (Reg.operands [.gpr 3] [])) #v[404]
    (.letOp (n := 414) (.out 0x1208c8 (shrR64Effect 0x1208c8 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[412]
    (.letOp (n := 415) (.exec 0x1208c8 (fun s => s.RIP = 0x1208c8) (shrR64Effect 0x1208c8 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[412]
    (.letOp (n := 416) (.out 0x1208cc (shldR64R64Effect 0x1208cc 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[404, 399]
    (.letOp (n := 417) (.exec 0x1208cc (fun s => s.RIP = 0x1208cc) (shldR64R64Effect 0x1208cc 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[404, 399]
    (.letOp (n := 418) (.out 0x1208d1 (movR64R64Effect 0x1208d1 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[406]
    (.letOp (n := 419) (.exec 0x1208d1 (fun s => s.RIP = 0x1208d1) (movR64R64Effect 0x1208d1 0 6) (Reg.operands [.gpr 6] [])) #v[406]
    (.letOp (n := 420) (.out 0x1208d4 (mulR64Effect 0x1208d4 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[376, 418]
    (.letOp (n := 421) (.out 0x1208d4 (mulR64Effect 0x1208d4 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[376, 418]
    (.letOp (n := 422) (.exec 0x1208d4 (fun s => s.RIP = 0x1208d4) (mulR64Effect 0x1208d4 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[376, 418]
    (.letOp (n := 423) (.out 0x1208d7 (movR64R64Effect 0x1208d7 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[420]
    (.letOp (n := 424) (.exec 0x1208d7 (fun s => s.RIP = 0x1208d7) (movR64R64Effect 0x1208d7 10 0) (Reg.operands [.gpr 0] [])) #v[420]
    (.letOp (n := 425) (.out 0x1208da (addR64R64Effect 0x1208da 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[423, 410]
    (.letOp (n := 426) (.out 0x1208da (addR64R64Effect 0x1208da 10 1) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 1] []) (.flag .CF)) #v[423, 410]
    (.letOp (n := 427) (.exec 0x1208da (fun s => s.RIP = 0x1208da) (addR64R64Effect 0x1208da 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[423, 410]
    (.letOp (n := 428) (.out 0x1208dd (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1208dd 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[421, 426]
    (.letOp (n := 429) (.exec 0x1208dd (fun s => s.RIP = 0x1208dd) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1208dd 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[421, 426]
    (.letOp (n := 430) (.out 0x1208e1 (addR64R64Effect 0x1208e1 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[425, 416]
    (.letOp (n := 431) (.out 0x1208e1 (addR64R64Effect 0x1208e1 10 3) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 3] []) (.flag .CF)) #v[425, 416]
    (.letOp (n := 432) (.exec 0x1208e1 (fun s => s.RIP = 0x1208e1) (addR64R64Effect 0x1208e1 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[425, 416]
    (.letOp (n := 433) (.out 0x1208e4 (atFlags StatusFlags.CF (adcR64R64Effect 0x1208e4 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[414, 428, 431]
    (.letOp (n := 434) (.exec 0x1208e4 (fun s => s.RIP = 0x1208e4) (atFlags StatusFlags.CF (adcR64R64Effect 0x1208e4 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[414, 428, 431]
    (.letOp (n := 435) (.out 0x1208e7 (shldR64R64Effect 0x1208e7 5 7 10 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[433, 430]
    (.letOp (n := 436) (.exec 0x1208e7 (fun s => s.RIP = 0x1208e7) (shldR64R64Effect 0x1208e7 5 7 10 12) (Reg.operands [.gpr 7, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[433, 430]
    (.letOp (n := 437) (.out 0x1208ec (movR64Imm64Effect 0x1208ec 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 438) (.exec 0x1208ec (fun s => s.RIP = 0x1208ec) (movR64Imm64Effect 0x1208ec 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 439) (.out 0x1208f6 (movR64M64Effect 0x1208f6 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 440) (.exec 0x1208f6 (LoadPre 0x1208f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1208f6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1208f6 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 441) (.out 0x1208fb (andR64R64Effect 0x1208fb 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[439, 437]
    (.letOp (n := 442) (.exec 0x1208fb (fun s => s.RIP = 0x1208fb) (andR64R64Effect 0x1208fb 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[439, 437]
    (b_l12065f_9))))))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_8 : List UInt8 :=
  [0x4C, 0x01, 0xD0, 0x49, 0x89, 0xC1, 0x48, 0x11, 0xCB, 0x4C, 0x0F, 0xA4, 0xFE, 0x0C, 0x48, 0xB9,
    0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x23, 0x4C, 0x24, 0x08, 0x48, 0x89, 0xDF,
    0x48, 0xC1, 0xEF, 0x34, 0x48, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0xE5, 0x49,
    0x89, 0xC2, 0x49, 0x01, 0xCA, 0x48, 0x83, 0xD2, 0x00, 0x49, 0x01, 0xDA, 0x48, 0x11, 0xD7, 0x4C,
    0x0F, 0xA4, 0xD7, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x8B,
    0x4C, 0x24, 0x20, 0x48, 0x21, 0xC1] ++ bytes_l12065f_9

theorem code_l12065f_8 : ∀ x ∈ codeRange 0x1208a8 bytes_l12065f_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x208a8 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_9

def b_l12065f_7 : Block Op Label signature Reg.count 353 :=
  .letOp (n := 353) (.out 0x12086a (movR64R64Effect 0x12086a 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[351]
    (.letOp (n := 354) (.exec 0x12086a (fun s => s.RIP = 0x12086a) (movR64R64Effect 0x12086a 3 2) (Reg.operands [.gpr 2] [])) #v[351]
    (.letOp (n := 355) (.out 0x12086d (movR64R64Effect 0x12086d 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[350]
    (.letOp (n := 356) (.exec 0x12086d (fun s => s.RIP = 0x12086d) (movR64R64Effect 0x12086d 12 0) (Reg.operands [.gpr 0] [])) #v[350]
    (.letOp (n := 357) (.out 0x120870 (movR64R64Effect 0x120870 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[293]
    (.letOp (n := 358) (.exec 0x120870 (fun s => s.RIP = 0x120870) (movR64R64Effect 0x120870 0 15) (Reg.operands [.gpr 15] [])) #v[293]
    (.letOp (n := 359) (.out 0x120873 (mulR64Effect 0x120873 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[282, 357]
    (.letOp (n := 360) (.out 0x120873 (mulR64Effect 0x120873 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[282, 357]
    (.letOp (n := 361) (.exec 0x120873 (fun s => s.RIP = 0x120873) (mulR64Effect 0x120873 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[282, 357]
    (.letOp (n := 362) (.out 0x120876 (movR64R64Effect 0x120876 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[359]
    (.letOp (n := 363) (.exec 0x120876 (fun s => s.RIP = 0x120876) (movR64R64Effect 0x120876 15 0) (Reg.operands [.gpr 0] [])) #v[359]
    (.letOp (n := 364) (.out 0x120879 (addR64R64Effect 0x120879 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[362, 337]
    (.letOp (n := 365) (.out 0x120879 (addR64R64Effect 0x120879 15 14) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 14] []) (.flag .CF)) #v[362, 337]
    (.letOp (n := 366) (.exec 0x120879 (fun s => s.RIP = 0x120879) (addR64R64Effect 0x120879 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[362, 337]
    (.letOp (n := 367) (.out 0x12087c (atFlags StatusFlags.CF (adcR64R64Effect 0x12087c 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[339, 360, 365]
    (.letOp (n := 368) (.exec 0x12087c (fun s => s.RIP = 0x12087c) (atFlags StatusFlags.CF (adcR64R64Effect 0x12087c 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[339, 360, 365]
    (.letOp (n := 369) (.out 0x12087f (movR64R64Effect 0x12087f 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[364]
    (.letOp (n := 370) (.exec 0x12087f (fun s => s.RIP = 0x12087f) (movR64R64Effect 0x12087f 0 15) (Reg.operands [.gpr 15] [])) #v[364]
    (.letOp (n := 371) (.out 0x120882 (andR64R64Effect 0x120882 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[369, 314]
    (.letOp (n := 372) (.exec 0x120882 (fun s => s.RIP = 0x120882) (andR64R64Effect 0x120882 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[369, 314]
    (.letOp (n := 373) (.out 0x120885 (mulR64Effect 0x120885 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[318, 371]
    (.letOp (n := 374) (.out 0x120885 (mulR64Effect 0x120885 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[318, 371]
    (.letOp (n := 375) (.exec 0x120885 (fun s => s.RIP = 0x120885) (mulR64Effect 0x120885 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[318, 371]
    (.letOp (n := 376) (.out 0x120888 (movR64R64Effect 0x120888 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 7] []) (.reg (.gpr 5))) #v[318]
    (.letOp (n := 377) (.exec 0x120888 (fun s => s.RIP = 0x120888) (movR64R64Effect 0x120888 5 7) (Reg.operands [.gpr 7] [])) #v[318]
    (.letOp (n := 378) (.out 0x12088b (movR64R64Effect 0x12088b 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[374]
    (.letOp (n := 379) (.exec 0x12088b (fun s => s.RIP = 0x12088b) (movR64R64Effect 0x12088b 14 2) (Reg.operands [.gpr 2] [])) #v[374]
    (.letOp (n := 380) (.out 0x12088e (movR64R64Effect 0x12088e 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[373]
    (.letOp (n := 381) (.exec 0x12088e (fun s => s.RIP = 0x12088e) (movR64R64Effect 0x12088e 13 0) (Reg.operands [.gpr 0] [])) #v[373]
    (.letOp (n := 382) (.out 0x120891 (movR64M64Effect 0x120891 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 383) (.exec 0x120891 (LoadPre 0x120891 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x120891 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120891 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 384) (.out 0x120896 (mulR64Effect 0x120896 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[216, 382]
    (.letOp (n := 385) (.out 0x120896 (mulR64Effect 0x120896 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[216, 382]
    (.letOp (n := 386) (.exec 0x120896 (fun s => s.RIP = 0x120896) (mulR64Effect 0x120896 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[216, 382]
    (.letOp (n := 387) (.out 0x120899 (movR64R64Effect 0x120899 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[216]
    (.letOp (n := 388) (.exec 0x120899 (fun s => s.RIP = 0x120899) (movR64R64Effect 0x120899 11 9) (Reg.operands [.gpr 9] [])) #v[216]
    (.letOp (n := 389) (.out 0x12089c (addR64R64Effect 0x12089c 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[384, 355]
    (.letOp (n := 390) (.out 0x12089c (addR64R64Effect 0x12089c 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[384, 355]
    (.letOp (n := 391) (.exec 0x12089c (fun s => s.RIP = 0x12089c) (addR64R64Effect 0x12089c 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[384, 355]
    (.letOp (n := 392) (.out 0x12089f (atFlags StatusFlags.CF (adcR64R64Effect 0x12089f 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[353, 385, 390]
    (.letOp (n := 393) (.exec 0x12089f (fun s => s.RIP = 0x12089f) (atFlags StatusFlags.CF (adcR64R64Effect 0x12089f 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[353, 385, 390]
    (.letOp (n := 394) (.out 0x1208a2 (addR64R64Effect 0x1208a2 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[389, 380]
    (.letOp (n := 395) (.out 0x1208a2 (addR64R64Effect 0x1208a2 0 13) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 13] []) (.flag .CF)) #v[389, 380]
    (.letOp (n := 396) (.exec 0x1208a2 (fun s => s.RIP = 0x1208a2) (addR64R64Effect 0x1208a2 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[389, 380]
    (.letOp (n := 397) (.out 0x1208a5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1208a5 3 14)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[392, 378, 395]
    (.letOp (n := 398) (.exec 0x1208a5 (fun s => s.RIP = 0x1208a5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1208a5 3 14)) (Reg.operands [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[392, 378, 395]
    (b_l12065f_8))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_7 : List UInt8 :=
  [0x48, 0x89, 0xD3, 0x49, 0x89, 0xC4, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE3, 0x49, 0x89, 0xC7, 0x4D,
    0x01, 0xF7, 0x48, 0x11, 0xD6, 0x4C, 0x89, 0xF8, 0x48, 0x21, 0xE8, 0x48, 0xF7, 0xE7, 0x48, 0x89,
    0xFD, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC5, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x49, 0xF7, 0xE1, 0x4D,
    0x89, 0xCB, 0x4C, 0x01, 0xE0, 0x48, 0x11, 0xD3, 0x4C, 0x01, 0xE8, 0x4C, 0x11, 0xF3] ++ bytes_l12065f_8

theorem code_l12065f_7 : ∀ x ∈ codeRange 0x12086a bytes_l12065f_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2086a 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_8

def b_l12065f_6 : Block Op Label signature Reg.count 310 :=
  .letOp (n := 310) (.out 0x120817 (atFlags StatusFlags.CF (adcR64R64Effect 0x120817 14 1)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[305, 247, 308]
    (.letOp (n := 311) (.exec 0x120817 (fun s => s.RIP = 0x120817) (atFlags StatusFlags.CF (adcR64R64Effect 0x120817 14 1)) (Reg.operands [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[305, 247, 308]
    (.letOp (n := 312) (.out 0x12081a (movR64R64Effect 0x12081a 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[307]
    (.letOp (n := 313) (.exec 0x12081a (fun s => s.RIP = 0x12081a) (movR64R64Effect 0x12081a 0 12) (Reg.operands [.gpr 12] [])) #v[307]
    (.letOp (n := 314) (.out 0x12081d (movR64Imm64Effect 0x12081d 5 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 315) (.exec 0x12081d (fun s => s.RIP = 0x12081d) (movR64Imm64Effect 0x12081d 5 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 316) (.out 0x120827 (andR64R64Effect 0x120827 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[312, 314]
    (.letOp (n := 317) (.exec 0x120827 (fun s => s.RIP = 0x120827) (andR64R64Effect 0x120827 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[312, 314]
    (.letOp (n := 318) (.out 0x12082a (movR64Imm64Effect 0x12082a 7 0x1000003d10) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 319) (.exec 0x12082a (fun s => s.RIP = 0x12082a) (movR64Imm64Effect 0x12082a 7 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 320) (.out 0x120834 (mulR64Effect 0x120834 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[318, 316]
    (.letOp (n := 321) (.out 0x120834 (mulR64Effect 0x120834 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[318, 316]
    (.letOp (n := 322) (.exec 0x120834 (fun s => s.RIP = 0x120834) (mulR64Effect 0x120834 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[318, 316]
    (.letOp (n := 323) (.out 0x120837 (addR64R64Effect 0x120837 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[320, 280]
    (.letOp (n := 324) (.out 0x120837 (addR64R64Effect 0x120837 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[320, 280]
    (.letOp (n := 325) (.exec 0x120837 (fun s => s.RIP = 0x120837) (addR64R64Effect 0x120837 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[320, 280]
    (.letOp (n := 326) (.out 0x12083a (atFlags StatusFlags.CF (adcR64R64Effect 0x12083a 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[278, 321, 324]
    (.letOp (n := 327) (.exec 0x12083a (fun s => s.RIP = 0x12083a) (atFlags StatusFlags.CF (adcR64R64Effect 0x12083a 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[278, 321, 324]
    (.letOp (n := 328) (.out 0x12083d (addR64R64Effect 0x12083d 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[323, 270]
    (.letOp (n := 329) (.out 0x12083d (addR64R64Effect 0x12083d 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[323, 270]
    (.letOp (n := 330) (.exec 0x12083d (fun s => s.RIP = 0x12083d) (addR64R64Effect 0x12083d 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[323, 270]
    (.letOp (n := 331) (.out 0x120840 (movR64R64Effect 0x120840 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[328]
    (.letOp (n := 332) (.exec 0x120840 (fun s => s.RIP = 0x120840) (movR64R64Effect 0x120840 8 0) (Reg.operands [.gpr 0] [])) #v[328]
    (.letOp (n := 333) (.out 0x120843 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x120843 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[326, 329]
    (.letOp (n := 334) (.exec 0x120843 (fun s => s.RIP = 0x120843) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x120843 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[326, 329]
    (.letOp (n := 335) (.out 0x120847 (movR64R64Effect 0x120847 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[310]
    (.letOp (n := 336) (.exec 0x120847 (fun s => s.RIP = 0x120847) (movR64R64Effect 0x120847 6 14) (Reg.operands [.gpr 14] [])) #v[310]
    (.letOp (n := 337) (.out 0x12084a (shldR64R64Effect 0x12084a 5 14 12 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[310, 307]
    (.letOp (n := 338) (.exec 0x12084a (fun s => s.RIP = 0x12084a) (shldR64R64Effect 0x12084a 5 14 12 12) (Reg.operands [.gpr 14, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[310, 307]
    (.letOp (n := 339) (.out 0x12084f (shrR64Effect 0x12084f 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[335]
    (.letOp (n := 340) (.exec 0x12084f (fun s => s.RIP = 0x12084f) (shrR64Effect 0x12084f 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[335]
    (.letOp (n := 341) (.out 0x120853 (movR64R64Effect 0x120853 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[333]
    (.letOp (n := 342) (.exec 0x120853 (fun s => s.RIP = 0x120853) (movR64R64Effect 0x120853 1 10) (Reg.operands [.gpr 10] [])) #v[333]
    (.letOp (n := 343) (.out 0x120856 (shrR64Effect 0x120856 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[341]
    (.letOp (n := 344) (.exec 0x120856 (fun s => s.RIP = 0x120856) (shrR64Effect 0x120856 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[341]
    (.letOp (n := 345) (.out 0x12085a (shldR64R64Effect 0x12085a 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[333, 328]
    (.letOp (n := 346) (.exec 0x12085a (fun s => s.RIP = 0x12085a) (shldR64R64Effect 0x12085a 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[333, 328]
    (.letOp (n := 347) (.out 0x12085f (movR64R64Effect 0x12085f 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[60]
    (.letOp (n := 348) (.exec 0x12085f (fun s => s.RIP = 0x12085f) (movR64R64Effect 0x12085f 0 13) (Reg.operands [.gpr 13] [])) #v[60]
    (.letOp (n := 349) (.exec 0x120862 (StorePre 0x120862 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x120862 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120862 13 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 350) (.out 0x120867 (mulR64Effect 0x120867 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[347, 347]
    (.letOp (n := 351) (.out 0x120867 (mulR64Effect 0x120867 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 0] []) (.reg (.gpr 2))) #v[347, 347]
    (.letOp (n := 352) (.exec 0x120867 (fun s => s.RIP = 0x120867) (mulR64Effect 0x120867 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[347, 347]
    (b_l12065f_7)))))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_6 : List UInt8 :=
  [0x49, 0x11, 0xCE, 0x4C, 0x89, 0xE0, 0x48, 0xBD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x48, 0x21, 0xE8, 0x48, 0xBF, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7,
    0x48, 0x01, 0xD8, 0x49, 0x11, 0xD2, 0x4C, 0x01, 0xC0, 0x49, 0x89, 0xC0, 0x49, 0x83, 0xD2, 0x00,
    0x4C, 0x89, 0xF6, 0x4D, 0x0F, 0xA4, 0xE6, 0x0C, 0x48, 0xC1, 0xEE, 0x34, 0x4C, 0x89, 0xD1, 0x48,
    0xC1, 0xE9, 0x34, 0x49, 0x0F, 0xA4, 0xC2, 0x0C, 0x4C, 0x89, 0xE8, 0x4C, 0x89, 0x6C, 0x24, 0x58,
    0x48, 0xF7, 0xE0] ++ bytes_l12065f_7

theorem code_l12065f_6 : ∀ x ∈ codeRange 0x120817 bytes_l12065f_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20817 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_7

def b_l12065f_5 : Block Op Label signature Reg.count 267 :=
  .letOp (n := 267) (.exec 0x1207cf (StorePre 0x1207cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1207cf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1207cf 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[264, 4]
    (.letOp (n := 268) (.out 0x1207d4 (atFlags StatusFlags.CF (adcR64R64Effect 0x1207d4 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[208, 262, 265]
    (.letOp (n := 269) (.exec 0x1207d4 (fun s => s.RIP = 0x1207d4) (atFlags StatusFlags.CF (adcR64R64Effect 0x1207d4 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[208, 262, 265]
    (.letOp (n := 270) (.out 0x1207d7 (shldR64R64Effect 0x1207d7 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[268, 264]
    (.letOp (n := 271) (.exec 0x1207d7 (fun s => s.RIP = 0x1207d7) (shldR64R64Effect 0x1207d7 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[268, 264]
    (.letOp (n := 272) (.out 0x1207dc (leaR64Effect 0x1207dc 0 (.sib 14 (some 14) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 14] []) (.reg (.gpr 0))) #v[203, 203]
    (.letOp (n := 273) (.exec 0x1207dc (fun s => s.RIP = 0x1207dc) (leaR64Effect 0x1207dc 0 (.sib 14 (some 14) 0 .none)) (Reg.operands [.gpr 14, .gpr 14] [])) #v[203, 203]
    (.letOp (n := 274) (.exec 0x1207e0 (StorePre 0x1207e0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1207e0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1207e0 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[272, 4]
    (.letOp (n := 275) (.out 0x1207e5 (mulR64Effect 0x1207e5 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[60, 272]
    (.letOp (n := 276) (.out 0x1207e5 (mulR64Effect 0x1207e5 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[60, 272]
    (.letOp (n := 277) (.exec 0x1207e5 (fun s => s.RIP = 0x1207e5) (mulR64Effect 0x1207e5 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[60, 272]
    (.letOp (n := 278) (.out 0x1207e8 (movR64R64Effect 0x1207e8 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[276]
    (.letOp (n := 279) (.exec 0x1207e8 (fun s => s.RIP = 0x1207e8) (movR64R64Effect 0x1207e8 10 2) (Reg.operands [.gpr 2] [])) #v[276]
    (.letOp (n := 280) (.out 0x1207eb (movR64R64Effect 0x1207eb 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[275]
    (.letOp (n := 281) (.exec 0x1207eb (fun s => s.RIP = 0x1207eb) (movR64R64Effect 0x1207eb 3 0) (Reg.operands [.gpr 0] [])) #v[275]
    (.letOp (n := 282) (.out 0x1207ee (movR64R64Effect 0x1207ee 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 12] []) (.reg (.gpr 11))) #v[212]
    (.letOp (n := 283) (.exec 0x1207ee (fun s => s.RIP = 0x1207ee) (movR64R64Effect 0x1207ee 11 12) (Reg.operands [.gpr 12] [])) #v[212]
    (.letOp (n := 284) (.out 0x1207f1 (movR64R64Effect 0x1207f1 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[212]
    (.letOp (n := 285) (.exec 0x1207f1 (fun s => s.RIP = 0x1207f1) (movR64R64Effect 0x1207f1 0 12) (Reg.operands [.gpr 12] [])) #v[212]
    (.letOp (n := 286) (.out 0x1207f4 (mulR64Effect 0x1207f4 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[212, 284]
    (.letOp (n := 287) (.out 0x1207f4 (mulR64Effect 0x1207f4 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[212, 284]
    (.letOp (n := 288) (.exec 0x1207f4 (fun s => s.RIP = 0x1207f4) (mulR64Effect 0x1207f4 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[212, 284]
    (.letOp (n := 289) (.out 0x1207f7 (movR64R64Effect 0x1207f7 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[286]
    (.letOp (n := 290) (.exec 0x1207f7 (fun s => s.RIP = 0x1207f7) (movR64R64Effect 0x1207f7 7 0) (Reg.operands [.gpr 0] [])) #v[286]
    (.letOp (n := 291) (.out 0x1207fa (movR64R64Effect 0x1207fa 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[287]
    (.letOp (n := 292) (.exec 0x1207fa (fun s => s.RIP = 0x1207fa) (movR64R64Effect 0x1207fa 14 2) (Reg.operands [.gpr 2] [])) #v[287]
    (.letOp (n := 293) (.out 0x1207fd (leaR64Effect 0x1207fd 15 (.abs (some 5) 1 0x0)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 5] []) (.reg (.gpr 15))) #v[97]
    (.letOp (n := 294) (.exec 0x1207fd (fun s => s.RIP = 0x1207fd) (leaR64Effect 0x1207fd 15 (.abs (some 5) 1 0x0)) (Reg.operands [.gpr 5] [])) #v[97]
    (.letOp (n := 295) (.out 0x120805 (movR64R64Effect 0x120805 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[293]
    (.letOp (n := 296) (.exec 0x120805 (fun s => s.RIP = 0x120805) (movR64R64Effect 0x120805 0 15) (Reg.operands [.gpr 15] [])) #v[293]
    (.letOp (n := 297) (.out 0x120808 (mulR64Effect 0x120808 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[216, 295]
    (.letOp (n := 298) (.out 0x120808 (mulR64Effect 0x120808 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[216, 295]
    (.letOp (n := 299) (.exec 0x120808 (fun s => s.RIP = 0x120808) (mulR64Effect 0x120808 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[216, 295]
    (.letOp (n := 300) (.out 0x12080b (movR64R64Effect 0x12080b 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[297]
    (.letOp (n := 301) (.exec 0x12080b (fun s => s.RIP = 0x12080b) (movR64R64Effect 0x12080b 12 0) (Reg.operands [.gpr 0] [])) #v[297]
    (.letOp (n := 302) (.out 0x12080e (addR64R64Effect 0x12080e 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 7] []) (.reg (.gpr 12))) #v[300, 289]
    (.letOp (n := 303) (.out 0x12080e (addR64R64Effect 0x12080e 12 7) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 7] []) (.flag .CF)) #v[300, 289]
    (.letOp (n := 304) (.exec 0x12080e (fun s => s.RIP = 0x12080e) (addR64R64Effect 0x12080e 12 7) (Reg.operands [.gpr 12, .gpr 7] [])) #v[300, 289]
    (.letOp (n := 305) (.out 0x120811 (atFlags StatusFlags.CF (adcR64R64Effect 0x120811 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[291, 298, 303]
    (.letOp (n := 306) (.exec 0x120811 (fun s => s.RIP = 0x120811) (atFlags StatusFlags.CF (adcR64R64Effect 0x120811 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[291, 298, 303]
    (.letOp (n := 307) (.out 0x120814 (addR64R64Effect 0x120814 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[302, 249]
    (.letOp (n := 308) (.out 0x120814 (addR64R64Effect 0x120814 12 6) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 6] []) (.flag .CF)) #v[302, 249]
    (.letOp (n := 309) (.exec 0x120814 (fun s => s.RIP = 0x120814) (addR64R64Effect 0x120814 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[302, 249]
    (b_l12065f_6)))))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_5 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x10, 0x49, 0x11, 0xD0, 0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x4B, 0x8D, 0x04,
    0x36, 0x48, 0x89, 0x44, 0x24, 0x28, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xD2, 0x48, 0x89, 0xC3, 0x4D,
    0x89, 0xE3, 0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE4, 0x48, 0x89, 0xC7, 0x49, 0x89, 0xD6, 0x4C, 0x8D,
    0x3C, 0x6D, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE1, 0x49, 0x89, 0xC4, 0x49,
    0x01, 0xFC, 0x49, 0x11, 0xD6, 0x49, 0x01, 0xF4] ++ bytes_l12065f_6

theorem code_l12065f_5 : ∀ x ∈ codeRange 0x1207cf bytes_l12065f_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x207cf 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_6

def b_l12065f_4 : Block Op Label signature Reg.count 223 :=
  .letOp (n := 223) (.out 0x12077d (movR64R64Effect 0x12077d 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[218]
    (.letOp (n := 224) (.exec 0x12077d (fun s => s.RIP = 0x12077d) (movR64R64Effect 0x12077d 11 0) (Reg.operands [.gpr 0] [])) #v[218]
    (.letOp (n := 225) (.exec 0x120780 (StorePre 0x120780 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x120780 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120780 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[97, 4]
    (.letOp (n := 226) (.out 0x120785 (movR64R64Effect 0x120785 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[97]
    (.letOp (n := 227) (.exec 0x120785 (fun s => s.RIP = 0x120785) (movR64R64Effect 0x120785 0 5) (Reg.operands [.gpr 5] [])) #v[97]
    (.letOp (n := 228) (.out 0x120788 (mulR64Effect 0x120788 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[60, 226]
    (.letOp (n := 229) (.out 0x120788 (mulR64Effect 0x120788 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[60, 226]
    (.letOp (n := 230) (.exec 0x120788 (fun s => s.RIP = 0x120788) (mulR64Effect 0x120788 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[60, 226]
    (.letOp (n := 231) (.out 0x12078b (addR64R64Effect 0x12078b 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[228, 223]
    (.letOp (n := 232) (.out 0x12078b (addR64R64Effect 0x12078b 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[228, 223]
    (.letOp (n := 233) (.exec 0x12078b (fun s => s.RIP = 0x12078b) (addR64R64Effect 0x12078b 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[228, 223]
    (.letOp (n := 234) (.out 0x12078e (atFlags StatusFlags.CF (adcR64R64Effect 0x12078e 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[221, 229, 232]
    (.letOp (n := 235) (.exec 0x12078e (fun s => s.RIP = 0x12078e) (atFlags StatusFlags.CF (adcR64R64Effect 0x12078e 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[221, 229, 232]
    (.letOp (n := 236) (.out 0x120791 (shldR64R64Effect 0x120791 5 6 0 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[234, 231]
    (.letOp (n := 237) (.exec 0x120791 (fun s => s.RIP = 0x120791) (shldR64R64Effect 0x120791 5 6 0 1) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[234, 231]
    (.letOp (n := 238) (.out 0x120796 (addR64R64Effect 0x120796 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[231, 231]
    (.letOp (n := 239) (.exec 0x120796 (fun s => s.RIP = 0x120796) (addR64R64Effect 0x120796 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[231, 231]
    (.letOp (n := 240) (.out 0x120799 (addR64R64Effect 0x120799 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[238, 192]
    (.letOp (n := 241) (.out 0x120799 (addR64R64Effect 0x120799 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[238, 192]
    (.letOp (n := 242) (.exec 0x120799 (fun s => s.RIP = 0x120799) (addR64R64Effect 0x120799 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[238, 192]
    (.letOp (n := 243) (.out 0x12079c (atFlags StatusFlags.CF (adcR64R64Effect 0x12079c 6 1)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[236, 190, 241]
    (.letOp (n := 244) (.exec 0x12079c (fun s => s.RIP = 0x12079c) (atFlags StatusFlags.CF (adcR64R64Effect 0x12079c 6 1)) (Reg.operands [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[236, 190, 241]
    (.letOp (n := 245) (.out 0x12079f (movR64R64Effect 0x12079f 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[243]
    (.letOp (n := 246) (.exec 0x12079f (fun s => s.RIP = 0x12079f) (movR64R64Effect 0x12079f 1 6) (Reg.operands [.gpr 6] [])) #v[243]
    (.letOp (n := 247) (.out 0x1207a2 (shrR64Effect 0x1207a2 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[245]
    (.letOp (n := 248) (.exec 0x1207a2 (fun s => s.RIP = 0x1207a2) (shrR64Effect 0x1207a2 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[245]
    (.letOp (n := 249) (.out 0x1207a6 (shldR64R64Effect 0x1207a6 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[243, 240]
    (.letOp (n := 250) (.exec 0x1207a6 (fun s => s.RIP = 0x1207a6) (shldR64R64Effect 0x1207a6 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[243, 240]
    (.letOp (n := 251) (.out 0x1207ab (shlR64Effect 0x1207ab 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[240]
    (.letOp (n := 252) (.exec 0x1207ab (fun s => s.RIP = 0x1207ab) (shlR64Effect 0x1207ab 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[240]
    (.letOp (n := 253) (.out 0x1207af (movR64Imm64Effect 0x1207af 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 254) (.exec 0x1207af (fun s => s.RIP = 0x1207af) (movR64Imm64Effect 0x1207af 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 255) (.out 0x1207b9 (andR64R64Effect 0x1207b9 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[251, 253]
    (.letOp (n := 256) (.exec 0x1207b9 (fun s => s.RIP = 0x1207b9) (andR64R64Effect 0x1207b9 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[251, 253]
    (.letOp (n := 257) (.out 0x1207bc (orR64R64Effect 0x1207bc 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[255, 210]
    (.letOp (n := 258) (.exec 0x1207bc (fun s => s.RIP = 0x1207bc) (orR64R64Effect 0x1207bc 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[255, 210]
    (.letOp (n := 259) (.out 0x1207bf (movR64Imm64Effect 0x1207bf 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 260) (.exec 0x1207bf (fun s => s.RIP = 0x1207bf) (movR64Imm64Effect 0x1207bf 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 261) (.out 0x1207c9 (mulR64Effect 0x1207c9 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[259, 257]
    (.letOp (n := 262) (.out 0x1207c9 (mulR64Effect 0x1207c9 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[259, 257]
    (.letOp (n := 263) (.exec 0x1207c9 (fun s => s.RIP = 0x1207c9) (mulR64Effect 0x1207c9 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[259, 257]
    (.letOp (n := 264) (.out 0x1207cc (addR64R64Effect 0x1207cc 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[261, 206]
    (.letOp (n := 265) (.out 0x1207cc (addR64R64Effect 0x1207cc 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[261, 206]
    (.letOp (n := 266) (.exec 0x1207cc (fun s => s.RIP = 0x1207cc) (addR64R64Effect 0x1207cc 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[261, 206]
    (b_l12065f_5))))))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_4 : List UInt8 :=
  [0x49, 0x89, 0xC3, 0x48, 0x89, 0x6C, 0x24, 0x48, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE5, 0x4C, 0x01,
    0xD8, 0x48, 0x11, 0xD6, 0x48, 0x0F, 0xA4, 0xC6, 0x01, 0x48, 0x01, 0xC0, 0x48, 0x01, 0xF8, 0x48,
    0x11, 0xCE, 0x48, 0x89, 0xF1, 0x48, 0xC1, 0xE9, 0x34, 0x48, 0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0xC1,
    0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0, 0x48,
    0x09, 0xD8, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C,
    0x01, 0xD0] ++ bytes_l12065f_5

theorem code_l12065f_4 : ∀ x ∈ codeRange 0x12077d bytes_l12065f_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2077d 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_5

def b_l12065f_3 : Block Op Label signature Reg.count 182 :=
  .letOp (n := 182) (.out 0x120737 (addR64R64Effect 0x120737 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[177, 124]
    (.letOp (n := 183) (.out 0x120737 (addR64R64Effect 0x120737 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[177, 124]
    (.letOp (n := 184) (.exec 0x120737 (fun s => s.RIP = 0x120737) (addR64R64Effect 0x120737 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[177, 124]
    (.letOp (n := 185) (.exec 0x12073a (StorePre 0x12073a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x12073a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12073a 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[182, 4]
    (.letOp (n := 186) (.out 0x12073f (atFlags StatusFlags.CF (adcR64R64Effect 0x12073f 7 15)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[180, 161, 183]
    (.letOp (n := 187) (.exec 0x12073f (fun s => s.RIP = 0x12073f) (atFlags StatusFlags.CF (adcR64R64Effect 0x12073f 7 15)) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[180, 161, 183]
    (.letOp (n := 188) (.out 0x120742 (movR64R64Effect 0x120742 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[186]
    (.letOp (n := 189) (.exec 0x120742 (fun s => s.RIP = 0x120742) (movR64R64Effect 0x120742 1 7) (Reg.operands [.gpr 7] [])) #v[186]
    (.letOp (n := 190) (.out 0x120745 (shrR64Effect 0x120745 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[188]
    (.letOp (n := 191) (.exec 0x120745 (fun s => s.RIP = 0x120745) (shrR64Effect 0x120745 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[188]
    (.letOp (n := 192) (.out 0x120749 (shldR64R64Effect 0x120749 5 7 0 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[186, 182]
    (.letOp (n := 193) (.exec 0x120749 (fun s => s.RIP = 0x120749) (shldR64R64Effect 0x120749 5 7 0 12) (Reg.operands [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[186, 182]
    (.letOp (n := 194) (.out 0x12074e (movR64R64Effect 0x12074e 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[182]
    (.letOp (n := 195) (.exec 0x12074e (fun s => s.RIP = 0x12074e) (movR64R64Effect 0x12074e 3 0) (Reg.operands [.gpr 0] [])) #v[182]
    (.letOp (n := 196) (.out 0x120751 (shrR64Effect 0x120751 4 3 48) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[194]
    (.letOp (n := 197) (.exec 0x120751 (fun s => s.RIP = 0x120751) (shrR64Effect 0x120751 4 3 48) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[194]
    (.letOp (n := 198) (.out 0x120755 (movR64R64Effect 0x120755 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[58]
    (.letOp (n := 199) (.exec 0x120755 (fun s => s.RIP = 0x120755) (movR64R64Effect 0x120755 0 12) (Reg.operands [.gpr 12] [])) #v[58]
    (.letOp (n := 200) (.out 0x120758 (mulR64Effect 0x120758 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[58, 198]
    (.letOp (n := 201) (.out 0x120758 (mulR64Effect 0x120758 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[58, 198]
    (.letOp (n := 202) (.exec 0x120758 (fun s => s.RIP = 0x120758) (mulR64Effect 0x120758 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[58, 198]
    (.letOp (n := 203) (.out 0x12075b (movR64R64Effect 0x12075b 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 12] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 204) (.exec 0x12075b (fun s => s.RIP = 0x12075b) (movR64R64Effect 0x12075b 14 12) (Reg.operands [.gpr 12] [])) #v[58]
    (.letOp (n := 205) (.exec 0x12075e (StorePre 0x12075e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x12075e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12075e 12 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 206) (.out 0x120763 (movR64R64Effect 0x120763 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[200]
    (.letOp (n := 207) (.exec 0x120763 (fun s => s.RIP = 0x120763) (movR64R64Effect 0x120763 10 0) (Reg.operands [.gpr 0] [])) #v[200]
    (.letOp (n := 208) (.out 0x120766 (movR64R64Effect 0x120766 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[201]
    (.letOp (n := 209) (.exec 0x120766 (fun s => s.RIP = 0x120766) (movR64R64Effect 0x120766 8 2) (Reg.operands [.gpr 2] [])) #v[201]
    (.letOp (n := 210) (.out 0x120769 (andR32Imm8Effect 0x120769 3 3 0xf) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[196]
    (.letOp (n := 211) (.exec 0x120769 (fun s => s.RIP = 0x120769) (andR32Imm8Effect 0x120769 3 3 0xf) (Reg.operands [.gpr 3] [])) #v[196]
    (.letOp (n := 212) (.out 0x12076c (movR64R64Effect 0x12076c 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 9] []) (.reg (.gpr 12))) #v[154]
    (.letOp (n := 213) (.exec 0x12076c (fun s => s.RIP = 0x12076c) (movR64R64Effect 0x12076c 12 9) (Reg.operands [.gpr 9] [])) #v[154]
    (.letOp (n := 214) (.out 0x12076f (movR64R64Effect 0x12076f 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[154]
    (.letOp (n := 215) (.exec 0x12076f (fun s => s.RIP = 0x12076f) (movR64R64Effect 0x12076f 0 9) (Reg.operands [.gpr 9] [])) #v[154]
    (.letOp (n := 216) (.out 0x120772 (movR64M64Effect 0x120772 9 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 217) (.exec 0x120772 (LoadPre 0x120772 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x120772 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120772 9 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 218) (.out 0x120777 (mulR64Effect 0x120777 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[216, 214]
    (.letOp (n := 219) (.out 0x120777 (mulR64Effect 0x120777 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[216, 214]
    (.letOp (n := 220) (.exec 0x120777 (fun s => s.RIP = 0x120777) (mulR64Effect 0x120777 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[216, 214]
    (.letOp (n := 221) (.out 0x12077a (movR64R64Effect 0x12077a 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[219]
    (.letOp (n := 222) (.exec 0x12077a (fun s => s.RIP = 0x12077a) (movR64R64Effect 0x12077a 6 2) (Reg.operands [.gpr 2] [])) #v[219]
    (b_l12065f_4)))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_3 : List UInt8 :=
  [0x48, 0x01, 0xF0, 0x48, 0x89, 0x44, 0x24, 0x20, 0x4C, 0x11, 0xFF, 0x48, 0x89, 0xF9, 0x48, 0xC1,
    0xE9, 0x34, 0x48, 0x0F, 0xA4, 0xC7, 0x0C, 0x48, 0x89, 0xC3, 0x48, 0xC1, 0xEB, 0x30, 0x4C, 0x89,
    0xE0, 0x49, 0xF7, 0xE4, 0x4D, 0x89, 0xE6, 0x4C, 0x89, 0x64, 0x24, 0x50, 0x49, 0x89, 0xC2, 0x49,
    0x89, 0xD0, 0x83, 0xE3, 0x0F, 0x4D, 0x89, 0xCC, 0x4C, 0x89, 0xC8, 0x4C, 0x8B, 0x4C, 0x24, 0x40,
    0x49, 0xF7, 0xE1, 0x48, 0x89, 0xD6] ++ bytes_l12065f_4

theorem code_l12065f_3 : ∀ x ∈ codeRange 0x120737 bytes_l12065f_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20737 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_4

def b_l12065f_2 : Block Op Label signature Reg.count 136 :=
  .letOp (n := 136) (.out 0x1206f6 (movR64R64Effect 0x1206f6 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[120]
    (.letOp (n := 137) (.exec 0x1206f6 (fun s => s.RIP = 0x1206f6) (movR64R64Effect 0x1206f6 0 1) (Reg.operands [.gpr 1] [])) #v[120]
    (.letOp (n := 138) (.out 0x1206f9 (mulR64Effect 0x1206f9 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[107, 136]
    (.letOp (n := 139) (.out 0x1206f9 (mulR64Effect 0x1206f9 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[107, 136]
    (.letOp (n := 140) (.exec 0x1206f9 (fun s => s.RIP = 0x1206f9) (mulR64Effect 0x1206f9 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[107, 136]
    (.letOp (n := 141) (.out 0x1206fc (movR64R64Effect 0x1206fc 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[139]
    (.letOp (n := 142) (.exec 0x1206fc (fun s => s.RIP = 0x1206fc) (movR64R64Effect 0x1206fc 7 2) (Reg.operands [.gpr 2] [])) #v[139]
    (.letOp (n := 143) (.out 0x1206ff (movR64R64Effect 0x1206ff 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[138]
    (.letOp (n := 144) (.exec 0x1206ff (fun s => s.RIP = 0x1206ff) (movR64R64Effect 0x1206ff 11 0) (Reg.operands [.gpr 0] [])) #v[138]
    (.letOp (n := 145) (.out 0x120702 (movR64R64Effect 0x120702 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[97]
    (.letOp (n := 146) (.exec 0x120702 (fun s => s.RIP = 0x120702) (movR64R64Effect 0x120702 0 5) (Reg.operands [.gpr 5] [])) #v[97]
    (.letOp (n := 147) (.out 0x120705 (mulR64Effect 0x120705 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[58, 145]
    (.letOp (n := 148) (.out 0x120705 (mulR64Effect 0x120705 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[58, 145]
    (.letOp (n := 149) (.exec 0x120705 (fun s => s.RIP = 0x120705) (mulR64Effect 0x120705 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[58, 145]
    (.letOp (n := 150) (.out 0x120708 (movR64R64Effect 0x120708 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[148]
    (.letOp (n := 151) (.exec 0x120708 (fun s => s.RIP = 0x120708) (movR64R64Effect 0x120708 3 2) (Reg.operands [.gpr 2] [])) #v[148]
    (.letOp (n := 152) (.out 0x12070b (movR64R64Effect 0x12070b 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[147]
    (.letOp (n := 153) (.exec 0x12070b (fun s => s.RIP = 0x12070b) (movR64R64Effect 0x12070b 14 0) (Reg.operands [.gpr 0] [])) #v[147]
    (.letOp (n := 154) (.out 0x12070e (movR64M64Effect 0x12070e 9 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 155) (.exec 0x12070e (LoadPre 0x12070e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x12070e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12070e 9 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 156) (.out 0x120713 (movR64R64Effect 0x120713 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[154]
    (.letOp (n := 157) (.exec 0x120713 (fun s => s.RIP = 0x120713) (movR64R64Effect 0x120713 0 9) (Reg.operands [.gpr 9] [])) #v[154]
    (.letOp (n := 158) (.out 0x120716 (mulR64Effect 0x120716 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[60, 156]
    (.letOp (n := 159) (.out 0x120716 (mulR64Effect 0x120716 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[60, 156]
    (.letOp (n := 160) (.exec 0x120716 (fun s => s.RIP = 0x120716) (mulR64Effect 0x120716 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[60, 156]
    (.letOp (n := 161) (.out 0x120719 (shrR64Effect 0x120719 4 15 52) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[122]
    (.letOp (n := 162) (.exec 0x120719 (fun s => s.RIP = 0x120719) (shrR64Effect 0x120719 4 15 52) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[122]
    (.letOp (n := 163) (.out 0x12071d (addR64R64Effect 0x12071d 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[158, 152]
    (.letOp (n := 164) (.out 0x12071d (addR64R64Effect 0x12071d 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[158, 152]
    (.letOp (n := 165) (.exec 0x12071d (fun s => s.RIP = 0x12071d) (addR64R64Effect 0x12071d 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[158, 152]
    (.letOp (n := 166) (.out 0x120720 (atFlags StatusFlags.CF (adcR64R64Effect 0x120720 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[150, 159, 164]
    (.letOp (n := 167) (.exec 0x120720 (fun s => s.RIP = 0x120720) (atFlags StatusFlags.CF (adcR64R64Effect 0x120720 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[150, 159, 164]
    (.letOp (n := 168) (.out 0x120723 (shldR64R64Effect 0x120723 5 3 0 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[166, 163]
    (.letOp (n := 169) (.exec 0x120723 (fun s => s.RIP = 0x120723) (shldR64R64Effect 0x120723 5 3 0 1) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[166, 163]
    (.letOp (n := 170) (.out 0x120728 (addR64R64Effect 0x120728 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[163, 163]
    (.letOp (n := 171) (.exec 0x120728 (fun s => s.RIP = 0x120728) (addR64R64Effect 0x120728 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[163, 163]
    (.letOp (n := 172) (.out 0x12072b (addR64R64Effect 0x12072b 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[143, 134]
    (.letOp (n := 173) (.out 0x12072b (addR64R64Effect 0x12072b 11 10) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 10] []) (.flag .CF)) #v[143, 134]
    (.letOp (n := 174) (.exec 0x12072b (fun s => s.RIP = 0x12072b) (addR64R64Effect 0x12072b 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[143, 134]
    (.letOp (n := 175) (.out 0x12072e (atFlags StatusFlags.CF (adcR64R64Effect 0x12072e 7 8)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[141, 132, 173]
    (.letOp (n := 176) (.exec 0x12072e (fun s => s.RIP = 0x12072e) (atFlags StatusFlags.CF (adcR64R64Effect 0x12072e 7 8)) (Reg.operands [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[141, 132, 173]
    (.letOp (n := 177) (.out 0x120731 (addR64R64Effect 0x120731 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[170, 172]
    (.letOp (n := 178) (.out 0x120731 (addR64R64Effect 0x120731 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[170, 172]
    (.letOp (n := 179) (.exec 0x120731 (fun s => s.RIP = 0x120731) (addR64R64Effect 0x120731 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[170, 172]
    (.letOp (n := 180) (.out 0x120734 (atFlags StatusFlags.CF (adcR64R64Effect 0x120734 7 3)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[175, 168, 178]
    (.letOp (n := 181) (.exec 0x120734 (fun s => s.RIP = 0x120734) (atFlags StatusFlags.CF (adcR64R64Effect 0x120734 7 3)) (Reg.operands [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[175, 168, 178]
    (b_l12065f_3))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_2 : List UInt8 :=
  [0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE3, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC3, 0x48, 0x89, 0xE8, 0x49,
    0xF7, 0xE4, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC6, 0x4C, 0x8B, 0x4C, 0x24, 0x30, 0x4C, 0x89, 0xC8,
    0x49, 0xF7, 0xE5, 0x49, 0xC1, 0xEF, 0x34, 0x4C, 0x01, 0xF0, 0x48, 0x11, 0xD3, 0x48, 0x0F, 0xA4,
    0xC3, 0x01, 0x48, 0x01, 0xC0, 0x4D, 0x01, 0xD3, 0x4C, 0x11, 0xC7, 0x4C, 0x01, 0xD8, 0x48, 0x11,
    0xDF] ++ bytes_l12065f_3

theorem code_l12065f_2 : ∀ x ∈ codeRange 0x1206f6 bytes_l12065f_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x206f6 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_3

def b_l12065f_1 : Block Op Label signature Reg.count 94 :=
  .letOp (n := 94) (.out 0x1206a4 (mulR64Effect 0x1206a4 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[62, 92]
    (.letOp (n := 95) (.out 0x1206a4 (mulR64Effect 0x1206a4 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[62, 92]
    (.letOp (n := 96) (.exec 0x1206a4 (fun s => s.RIP = 0x1206a4) (mulR64Effect 0x1206a4 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[62, 92]
    (.letOp (n := 97) (.out 0x1206a7 (movR64R64Effect 0x1206a7 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 15] []) (.reg (.gpr 5))) #v[62]
    (.letOp (n := 98) (.exec 0x1206a7 (fun s => s.RIP = 0x1206a7) (movR64R64Effect 0x1206a7 5 15) (Reg.operands [.gpr 15] [])) #v[62]
    (.letOp (n := 99) (.out 0x1206aa (movR64R64Effect 0x1206aa 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[94]
    (.letOp (n := 100) (.exec 0x1206aa (fun s => s.RIP = 0x1206aa) (movR64R64Effect 0x1206aa 8 0) (Reg.operands [.gpr 0] [])) #v[94]
    (.letOp (n := 101) (.out 0x1206ad (movR64R64Effect 0x1206ad 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 102) (.exec 0x1206ad (fun s => s.RIP = 0x1206ad) (movR64R64Effect 0x1206ad 1 2) (Reg.operands [.gpr 2] [])) #v[95]
    (.letOp (n := 103) (.out 0x1206b0 (movR64Imm64Effect 0x1206b0 0 0xffffffffffffd) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 104) (.exec 0x1206b0 (fun s => s.RIP = 0x1206b0) (movR64Imm64Effect 0x1206b0 0 0xffffffffffffd) (Reg.operands [] [])) #v[]
    (.letOp (n := 105) (.out 0x1206ba (andR64R64Effect 0x1206ba 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[103, 99]
    (.letOp (n := 106) (.exec 0x1206ba (fun s => s.RIP = 0x1206ba) (andR64R64Effect 0x1206ba 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[103, 99]
    (.letOp (n := 107) (.out 0x1206bd (movR64Imm64Effect 0x1206bd 11 0x1000003d10) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 108) (.exec 0x1206bd (fun s => s.RIP = 0x1206bd) (movR64Imm64Effect 0x1206bd 11 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 109) (.out 0x1206c7 (mulR64Effect 0x1206c7 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[107, 105]
    (.letOp (n := 110) (.out 0x1206c7 (mulR64Effect 0x1206c7 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[107, 105]
    (.letOp (n := 111) (.exec 0x1206c7 (fun s => s.RIP = 0x1206c7) (mulR64Effect 0x1206c7 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[107, 105]
    (.letOp (n := 112) (.out 0x1206ca (addR64R64Effect 0x1206ca 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[85, 85]
    (.letOp (n := 113) (.exec 0x1206ca (fun s => s.RIP = 0x1206ca) (addR64R64Effect 0x1206ca 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[85, 85]
    (.letOp (n := 114) (.out 0x1206cd (addR64R64Effect 0x1206cd 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[109, 112]
    (.letOp (n := 115) (.out 0x1206cd (addR64R64Effect 0x1206cd 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[109, 112]
    (.letOp (n := 116) (.exec 0x1206cd (fun s => s.RIP = 0x1206cd) (addR64R64Effect 0x1206cd 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[109, 112]
    (.letOp (n := 117) (.exec 0x1206d0 (StorePre 0x1206d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1206d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1206d0 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[114, 4]
    (.letOp (n := 118) (.out 0x1206d5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1206d5 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[90, 110, 115]
    (.letOp (n := 119) (.exec 0x1206d5 (fun s => s.RIP = 0x1206d5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1206d5 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[90, 110, 115]
    (.letOp (n := 120) (.out 0x1206d8 (shldR64R64Effect 0x1206d8 5 1 8 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[101, 99]
    (.letOp (n := 121) (.exec 0x1206d8 (fun s => s.RIP = 0x1206d8) (shldR64R64Effect 0x1206d8 5 1 8 12) (Reg.operands [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[101, 99]
    (.letOp (n := 122) (.out 0x1206dd (movR64R64Effect 0x1206dd 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[118]
    (.letOp (n := 123) (.exec 0x1206dd (fun s => s.RIP = 0x1206dd) (movR64R64Effect 0x1206dd 15 6) (Reg.operands [.gpr 6] [])) #v[118]
    (.letOp (n := 124) (.out 0x1206e0 (shldR64R64Effect 0x1206e0 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[118, 114]
    (.letOp (n := 125) (.exec 0x1206e0 (fun s => s.RIP = 0x1206e0) (shldR64R64Effect 0x1206e0 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[118, 114]
    (.letOp (n := 126) (.exec 0x1206e5 (StorePre 0x1206e5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1206e5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1206e5 14 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 127) (.out 0x1206ea (movR64R64Effect 0x1206ea 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[66]
    (.letOp (n := 128) (.exec 0x1206ea (fun s => s.RIP = 0x1206ea) (movR64R64Effect 0x1206ea 0 14) (Reg.operands [.gpr 14] [])) #v[66]
    (.letOp (n := 129) (.out 0x1206ed (mulR64Effect 0x1206ed 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[66, 127]
    (.letOp (n := 130) (.out 0x1206ed (mulR64Effect 0x1206ed 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[66, 127]
    (.letOp (n := 131) (.exec 0x1206ed (fun s => s.RIP = 0x1206ed) (mulR64Effect 0x1206ed 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[66, 127]
    (.letOp (n := 132) (.out 0x1206f0 (movR64R64Effect 0x1206f0 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[130]
    (.letOp (n := 133) (.exec 0x1206f0 (fun s => s.RIP = 0x1206f0) (movR64R64Effect 0x1206f0 8 2) (Reg.operands [.gpr 2] [])) #v[130]
    (.letOp (n := 134) (.out 0x1206f3 (movR64R64Effect 0x1206f3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[129]
    (.letOp (n := 135) (.exec 0x1206f3 (fun s => s.RIP = 0x1206f3) (movR64R64Effect 0x1206f3 10 0) (Reg.operands [.gpr 0] [])) #v[129]
    (b_l12065f_2))))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f_1 : List UInt8 :=
  [0x49, 0xF7, 0xE7, 0x4C, 0x89, 0xFD, 0x49, 0x89, 0xC0, 0x48, 0x89, 0xD1, 0x48, 0xB8, 0xFD, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xC0, 0x49, 0xBB, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x49, 0xF7, 0xE3, 0x48, 0x01, 0xFF, 0x48, 0x01, 0xF8, 0x48, 0x89, 0x44, 0x24,
    0x08, 0x48, 0x11, 0xD6, 0x4C, 0x0F, 0xA4, 0xC1, 0x0C, 0x49, 0x89, 0xF7, 0x48, 0x0F, 0xA4, 0xC6,
    0x0C, 0x4C, 0x89, 0x74, 0x24, 0x40, 0x4C, 0x89, 0xF0, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xD0, 0x49,
    0x89, 0xC2] ++ bytes_l12065f_2

theorem code_l12065f_1 : ∀ x ∈ codeRange 0x1206a4 bytes_l12065f_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x206a4 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_2

def b_l12065f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12065f (movzxR32R8Effect 0x12065f 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x12065f (fun s => s.RIP = 0x12065f) (movzxR32R8Effect 0x12065f 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.exec 0x120662 (StorePre 0x120662 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x120662 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120662 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x12066a (negR64Effect 0x12066a 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 57) (.exec 0x12066a (fun s => s.RIP = 0x12066a) (negR64Effect 0x12066a 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 58) (.out 0x12066d (andR64R64Effect 0x12066d 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[12, 56]
    (.letOp (n := 59) (.exec 0x12066d (fun s => s.RIP = 0x12066d) (andR64R64Effect 0x12066d 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[12, 56]
    (.letOp (n := 60) (.out 0x120670 (andR64R64Effect 0x120670 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[13, 56]
    (.letOp (n := 61) (.exec 0x120670 (fun s => s.RIP = 0x120670) (andR64R64Effect 0x120670 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[13, 56]
    (.letOp (n := 62) (.out 0x120673 (andR64R64Effect 0x120673 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[15, 56]
    (.letOp (n := 63) (.exec 0x120673 (fun s => s.RIP = 0x120673) (andR64R64Effect 0x120673 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[15, 56]
    (.letOp (n := 64) (.out 0x120676 (andR64R64Effect 0x120676 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[56, 5]
    (.letOp (n := 65) (.exec 0x120676 (fun s => s.RIP = 0x120676) (andR64R64Effect 0x120676 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[56, 5]
    (.letOp (n := 66) (.out 0x120679 (andR64R64Effect 0x120679 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[14, 64]
    (.letOp (n := 67) (.exec 0x120679 (fun s => s.RIP = 0x120679) (andR64R64Effect 0x120679 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[14, 64]
    (.letOp (n := 68) (.out 0x12067c (andR64R64Effect 0x12067c 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[64, 3]
    (.letOp (n := 69) (.exec 0x12067c (fun s => s.RIP = 0x12067c) (andR64R64Effect 0x12067c 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[64, 3]
    (.letOp (n := 70) (.exec 0x12067f (StorePre 0x12067f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x12067f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12067f 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x120684 (mulR64Effect 0x120684 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[58, 68]
    (.letOp (n := 72) (.out 0x120684 (mulR64Effect 0x120684 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[58, 68]
    (.letOp (n := 73) (.exec 0x120684 (fun s => s.RIP = 0x120684) (mulR64Effect 0x120684 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[58, 68]
    (.letOp (n := 74) (.out 0x120687 (movR64R64Effect 0x120687 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[72]
    (.letOp (n := 75) (.exec 0x120687 (fun s => s.RIP = 0x120687) (movR64R64Effect 0x120687 6 2) (Reg.operands [.gpr 2] [])) #v[72]
    (.letOp (n := 76) (.out 0x12068a (movR64R64Effect 0x12068a 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[71]
    (.letOp (n := 77) (.exec 0x12068a (fun s => s.RIP = 0x12068a) (movR64R64Effect 0x12068a 1 0) (Reg.operands [.gpr 0] [])) #v[71]
    (.letOp (n := 78) (.out 0x12068d (movR64R64Effect 0x12068d 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[66]
    (.letOp (n := 79) (.exec 0x12068d (fun s => s.RIP = 0x12068d) (movR64R64Effect 0x12068d 0 14) (Reg.operands [.gpr 14] [])) #v[66]
    (.letOp (n := 80) (.out 0x120690 (mulR64Effect 0x120690 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[60, 78]
    (.letOp (n := 81) (.out 0x120690 (mulR64Effect 0x120690 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[60, 78]
    (.letOp (n := 82) (.exec 0x120690 (fun s => s.RIP = 0x120690) (mulR64Effect 0x120690 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[60, 78]
    (.letOp (n := 83) (.out 0x120693 (movR64R64Effect 0x120693 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[80]
    (.letOp (n := 84) (.exec 0x120693 (fun s => s.RIP = 0x120693) (movR64R64Effect 0x120693 7 0) (Reg.operands [.gpr 0] [])) #v[80]
    (.letOp (n := 85) (.out 0x120696 (addR64R64Effect 0x120696 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[83, 76]
    (.letOp (n := 86) (.out 0x120696 (addR64R64Effect 0x120696 7 1) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 1] []) (.flag .CF)) #v[83, 76]
    (.letOp (n := 87) (.exec 0x120696 (fun s => s.RIP = 0x120696) (addR64R64Effect 0x120696 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[83, 76]
    (.letOp (n := 88) (.out 0x120699 (atFlags StatusFlags.CF (adcR64R64Effect 0x120699 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[74, 81, 86]
    (.letOp (n := 89) (.exec 0x120699 (fun s => s.RIP = 0x120699) (atFlags StatusFlags.CF (adcR64R64Effect 0x120699 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[74, 81, 86]
    (.letOp (n := 90) (.out 0x12069c (shldR64R64Effect 0x12069c 5 6 7 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[88, 85]
    (.letOp (n := 91) (.exec 0x12069c (fun s => s.RIP = 0x12069c) (shldR64R64Effect 0x12069c 5 6 7 1) (Reg.operands [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[88, 85]
    (.letOp (n := 92) (.out 0x1206a1 (movR64R64Effect 0x1206a1 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[62]
    (.letOp (n := 93) (.exec 0x1206a1 (fun s => s.RIP = 0x1206a1) (movR64R64Effect 0x1206a1 0 15) (Reg.operands [.gpr 15] [])) #v[62]
    (b_l12065f_1)))))))))))))))))))))))))))))))))))))))))

def bytes_l12065f : List UInt8 :=
  [0x0F, 0xB6, 0xC0, 0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xD8, 0x49, 0x21,
    0xC4, 0x49, 0x21, 0xC5, 0x49, 0x21, 0xC7, 0x48, 0x21, 0xE8, 0x49, 0x21, 0xC6, 0x48, 0x21, 0xD8,
    0x48, 0x89, 0x44, 0x24, 0x30, 0x49, 0xF7, 0xE4, 0x48, 0x89, 0xD6, 0x48, 0x89, 0xC1, 0x4C, 0x89,
    0xF0, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0xC7, 0x48, 0x01, 0xCF, 0x48, 0x11, 0xD6, 0x48, 0x0F, 0xA4,
    0xFE, 0x01, 0x4C, 0x89, 0xF8] ++ bytes_l12065f_1

theorem code_l12065f : ∀ x ∈ codeRange 0x12065f bytes_l12065f, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2065f 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12065f_1

@[cfg_block] def b_l120d03 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x120d03 (movzxR32M8Effect 0x120d03 8 0 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x120d03 (LoadPre 0x120d03 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x120d03 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x120d03 8 0 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x120d0b (StorePre 0x120d0b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x120d0b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x120d0b 4 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x120d0f (negR64Effect 0x120d0f 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 57) (.exec 0x120d0f (fun s => s.RIP = 0x120d0f) (negR64Effect 0x120d0f 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 58) (.out 0x120d12 (movR64M64Effect 0x120d12 1 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x120d12 (LoadPre 0x120d12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x120d12 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120d12 1 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x120d1a (andR64R64Effect 0x120d1a 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[58, 56]
    (.letOp (n := 61) (.exec 0x120d1a (fun s => s.RIP = 0x120d1a) (andR64R64Effect 0x120d1a 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[58, 56]
    (.letOp (n := 62) (.out 0x120d1d (movR64M64Effect 0x120d1d 2 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 63) (.exec 0x120d1d (LoadPre 0x120d1d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x120d1d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120d1d 2 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x120d25 (andR64R64Effect 0x120d25 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[62, 56]
    (.letOp (n := 65) (.exec 0x120d25 (fun s => s.RIP = 0x120d25) (andR64R64Effect 0x120d25 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[62, 56]
    (.letOp (n := 66) (.out 0x120d28 (movR64M64Effect 0x120d28 6 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 67) (.exec 0x120d28 (LoadPre 0x120d28 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x120d28 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120d28 6 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x120d30 (andR64R64Effect 0x120d30 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[66, 56]
    (.letOp (n := 69) (.exec 0x120d30 (fun s => s.RIP = 0x120d30) (andR64R64Effect 0x120d30 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[66, 56]
    (.letOp (n := 70) (.out 0x120d33 (movR64M64Effect 0x120d33 7 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 71) (.exec 0x120d33 (LoadPre 0x120d33 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x120d33 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120d33 7 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x120d3b (andR64R64Effect 0x120d3b 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[70, 56]
    (.letOp (n := 73) (.exec 0x120d3b (fun s => s.RIP = 0x120d3b) (andR64R64Effect 0x120d3b 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[70, 56]
    (.letOp (n := 74) (.out 0x120d3e (andR64M64Effect 0x120d3e 0 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[56, 4]
    (.letOp (n := 75) (.exec 0x120d3e (LoadPre 0x120d3e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x120d3e + BitVec.ofNat 64 8)) 8) (andR64M64Effect 0x120d3e 0 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 76) (.exec 0x120d46 (StorePre 0x120d46 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x120d46 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120d46 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 77) (.exec 0x120d4e (StorePre 0x120d4e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x120d4e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120d4e 2 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 78) (.exec 0x120d56 (StorePre 0x120d56 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x120d56 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120d56 6 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 79) (.exec 0x120d5e (StorePre 0x120d5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x120d5e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120d5e 7 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 80) (.exec 0x120d66 (StorePre 0x120d66 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x120d66 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120d66 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 81) (.out 0x120d6e (leaR64Effect 0x120d6e 7 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 82) (.exec 0x120d6e (fun s => s.RIP = 0x120d6e) (leaR64Effect 0x120d6e 7 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x120d76 (leaR64Effect 0x120d76 6 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 84) (.exec 0x120d76 (fun s => s.RIP = 0x120d76) (leaR64Effect 0x120d76 6 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x120d7e (callEffect (fun _ => 0x114930) 0x120d83) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 86) (.exec 0x120d7e (PushPre 0x120d7e 5) (callEffect (fun _ => 0x114930) 0x120d83) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.const ⟨64, 0x120d83⟩) #v[]
    (.terminate (.call ⟨.l114930, RegMap.args [(0, 74), (1, 60), (2, 64), (3, 3), (4, 85), (5, 5), (6, 83), (7, 81), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 88⟩ { target := .l120d83, kept := #v[], arity := rfl, guard := some (Fin.last 87) }))))))))))))))))))))))))))))))))))))

def bytes_l120d03 : List UInt8 :=
  [0x0F, 0xB6, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24, 0x20, 0x48, 0xF7, 0xD8, 0x48,
    0x8B, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00, 0x48, 0x21, 0xC1, 0x48, 0x8B, 0x94, 0x24, 0x38, 0x01,
    0x00, 0x00, 0x48, 0x21, 0xC2, 0x48, 0x8B, 0xB4, 0x24, 0x40, 0x01, 0x00, 0x00, 0x48, 0x21, 0xC6,
    0x48, 0x8B, 0xBC, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0x21, 0xC7, 0x48, 0x23, 0x84, 0x24, 0x50,
    0x01, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0xC0,
    0x00, 0x00, 0x00, 0x48, 0x89, 0xB4, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24, 0xD0,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0xE0,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0xB8, 0x00, 0x00, 0x00, 0xE8, 0xAD, 0x3B, 0xFF, 0xFF]

theorem code_l120d03 : ∀ x ∈ codeRange 0x120d03 bytes_l120d03, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x20d03 128 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l120d83_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.out 0x120df5 (andAlImm8Effect 0x120df5 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[87]
    (.letOp (n := 90) (.exec 0x120df5 (fun s => s.RIP = 0x120df5) (andAlImm8Effect 0x120df5 0x1) (Reg.operands [.gpr 0] [])) #v[87]
    (.letOp (n := 91) (.out 0x120df7 (movzxR32R8Effect 0x120df7 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[89]
    (.letOp (n := 92) (.exec 0x120df7 (fun s => s.RIP = 0x120df7) (movzxR32R8Effect 0x120df7 3 7 0) (Reg.operands [.gpr 0] [])) #v[89]
    (.letOp (n := 93) (.out 0x120dfa (callEffect (fun _ => 0x127d50) 0x120dff) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 94) (.exec 0x120dfa (PushPre 0x120dfa 5) (callEffect (fun _ => 0x127d50) 0x120dff) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.const ⟨64, 0x120dff⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 89), (1, 1), (2, 2), (3, 78), (4, 93), (5, 80), (6, 6), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 76), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 96⟩ { target := .l120dff, kept := #v[], arity := rfl, guard := some (Fin.last 95) }))))))))

def bytes_l120d83_1 : List UInt8 :=
  [0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x51, 0x6F, 0x00, 0x00]

theorem code_l120d83_1 : ∀ x ∈ codeRange 0x120df5 bytes_l120d83_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x20df5 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l120d83 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x120d83 (movR64M64Effect 0x120d83 14 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x120d83 (LoadPre 0x120d83 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x120d83 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120d83 14 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x120d8b (movR64M64Effect 0x120d8b 15 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 56) (.exec 0x120d8b (LoadPre 0x120d8b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x120d8b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120d8b 15 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x120d93 (movR64Imm64Effect 0x120d93 0 0x3ffffbfffff0bc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 58) (.exec 0x120d93 (fun s => s.RIP = 0x120d93) (movR64Imm64Effect 0x120d93 0 0x3ffffbfffff0bc) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x120d9d (subR64R64Effect 0x120d9d 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[57, 53]
    (.letOp (n := 60) (.exec 0x120d9d (fun s => s.RIP = 0x120d9d) (subR64R64Effect 0x120d9d 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[57, 53]
    (.letOp (n := 61) (.exec 0x120da0 (StorePre 0x120da0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x120da0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120da0 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x120da5 (movR64Imm64Effect 0x120da5 3 0x3ffffffffffffc) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 63) (.exec 0x120da5 (fun s => s.RIP = 0x120da5) (movR64Imm64Effect 0x120da5 3 0x3ffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x120daf (movR64R64Effect 0x120daf 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[62]
    (.letOp (n := 65) (.exec 0x120daf (fun s => s.RIP = 0x120daf) (movR64R64Effect 0x120daf 0 3) (Reg.operands [.gpr 3] [])) #v[62]
    (.letOp (n := 66) (.out 0x120db2 (subR64R64Effect 0x120db2 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[64, 55]
    (.letOp (n := 67) (.exec 0x120db2 (fun s => s.RIP = 0x120db2) (subR64R64Effect 0x120db2 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[64, 55]
    (.letOp (n := 68) (.exec 0x120db5 (StorePre 0x120db5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x120db5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120db5 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.out 0x120dba (movR64M64Effect 0x120dba 12 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 70) (.exec 0x120dba (LoadPre 0x120dba (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x120dba + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120dba 12 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x120dc2 (movR64R64Effect 0x120dc2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[62]
    (.letOp (n := 72) (.exec 0x120dc2 (fun s => s.RIP = 0x120dc2) (movR64R64Effect 0x120dc2 0 3) (Reg.operands [.gpr 3] [])) #v[62]
    (.letOp (n := 73) (.out 0x120dc5 (subR64R64Effect 0x120dc5 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[71, 69]
    (.letOp (n := 74) (.exec 0x120dc5 (fun s => s.RIP = 0x120dc5) (subR64R64Effect 0x120dc5 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[71, 69]
    (.letOp (n := 75) (.exec 0x120dc8 (StorePre 0x120dc8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120dc8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120dc8 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x120dcd (movR64M64Effect 0x120dcd 13 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 77) (.exec 0x120dcd (LoadPre 0x120dcd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x120dcd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120dcd 13 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x120dd5 (subR64R64Effect 0x120dd5 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[62, 76]
    (.letOp (n := 79) (.exec 0x120dd5 (fun s => s.RIP = 0x120dd5) (subR64R64Effect 0x120dd5 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[62, 76]
    (.letOp (n := 80) (.out 0x120dd8 (movR64M64Effect 0x120dd8 5 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 81) (.exec 0x120dd8 (LoadPre 0x120dd8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x120dd8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120dd8 5 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.out 0x120de0 (movR64Imm64Effect 0x120de0 0 0x3fffffffffffc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 83) (.exec 0x120de0 (fun s => s.RIP = 0x120de0) (movR64Imm64Effect 0x120de0 0 0x3fffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 84) (.out 0x120dea (subR64R64Effect 0x120dea 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[82, 80]
    (.letOp (n := 85) (.exec 0x120dea (fun s => s.RIP = 0x120dea) (subR64R64Effect 0x120dea 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[82, 80]
    (.letOp (n := 86) (.exec 0x120ded (StorePre 0x120ded 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120ded + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120ded 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 87) (.out 0x120df2 (movR32R32Effect 0x120df2 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 88) (.exec 0x120df2 (fun s => s.RIP = 0x120df2) (movR32R32Effect 0x120df2 3 0 14) (Reg.operands [.gpr 14] [])) #v[53]
    (b_l120d83_1))))))))))))))))))))))))))))))))))))

def bytes_l120d83 : List UInt8 :=
  [0x4C, 0x8B, 0xB4, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0xBC, 0x24, 0xE8, 0x00, 0x00, 0x00,
    0x48, 0xB8, 0xBC, 0xF0, 0xFF, 0xFF, 0xFB, 0xFF, 0x3F, 0x00, 0x4C, 0x29, 0xF0, 0x48, 0x89, 0x44,
    0x24, 0x60, 0x48, 0xBB, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00, 0x48, 0x89, 0xD8, 0x4C,
    0x29, 0xF8, 0x48, 0x89, 0x44, 0x24, 0x28, 0x4C, 0x8B, 0xA4, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48,
    0x89, 0xD8, 0x4C, 0x29, 0xE0, 0x48, 0x89, 0x44, 0x24, 0x08, 0x4C, 0x8B, 0xAC, 0x24, 0xF8, 0x00,
    0x00, 0x00, 0x4C, 0x29, 0xEB, 0x48, 0x8B, 0xAC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0xB8, 0xFC,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x00, 0x48, 0x29, 0xE8, 0x48, 0x89, 0x44, 0x24, 0x10, 0x44,
    0x89, 0xF0] ++ bytes_l120d83_1

theorem code_l120d83 : ∀ x ∈ codeRange 0x120d83 bytes_l120d83, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20d83 114 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l120d83_1

@[cfg_block] def b_l120dff : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x120dff (xorR8M8Effect 0x120dff 4 0 (.sib 4 none 0 (.d8 0x6c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[0, 4]
    (.letOp (n := 54) (.exec 0x120dff (LoadPre 0x120dff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x120dff + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x120dff 4 0 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 55) (.out 0x120e03 (movzxR32R8Effect 0x120e03 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x120e03 (fun s => s.RIP = 0x120e03) (movzxR32R8Effect 0x120e03 3 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x120e06 (callEffect (fun _ => 0x127d50) 0x120e0b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x120e06 (PushPre 0x120e06 5) (callEffect (fun _ => 0x127d50) 0x120e0b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x120e0b⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l120e0b, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l120dff : List UInt8 :=
  [0x32, 0x44, 0x24, 0x6C, 0x0F, 0xB6, 0xF8, 0xE8, 0x45, 0x6F, 0x00, 0x00]

theorem code_l120dff : ∀ x ∈ codeRange 0x120dff bytes_l120dff, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x20dff 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l120e0b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x120e0b (notR8Effect 0x120e0b 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x120e0b (fun s => s.RIP = 0x120e0b) (notR8Effect 0x120e0b 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x120e0d (andAlImm8Effect 0x120e0d 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x120e0d (fun s => s.RIP = 0x120e0d) (andAlImm8Effect 0x120e0d 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x120e0f (movzxR32R8Effect 0x120e0f 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x120e0f (fun s => s.RIP = 0x120e0f) (movzxR32R8Effect 0x120e0f 3 7 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x120e12 (callEffect (fun _ => 0x127d50) 0x120e17) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x120e12 (PushPre 0x120e12 5) (callEffect (fun _ => 0x127d50) 0x120e17) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x120e17⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l120e17, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l120e0b : List UInt8 :=
  [0xF6, 0xD0, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x39, 0x6F, 0x00, 0x00]

theorem code_l120e0b : ∀ x ∈ codeRange 0x120e0b bytes_l120e0b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x20e0b 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l120e17_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x120e5b (xorR64R64Effect 0x120e5b 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[91, 87]
    (.letOp (n := 94) (.exec 0x120e5b (fun s => s.RIP = 0x120e5b) (xorR64R64Effect 0x120e5b 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[91, 87]
    (.letOp (n := 95) (.exec 0x120e5e (StorePre 0x120e5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x120e5e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120e5e 14 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 96) (.exec 0x120e66 (StorePre 0x120e66 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x120e66 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120e66 15 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 97) (.exec 0x120e6e (StorePre 0x120e6e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x120e6e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120e6e 12 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 98) (.exec 0x120e76 (StorePre 0x120e76 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x120e76 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120e76 13 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 99) (.exec 0x120e7e (StorePre 0x120e7e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x120e7e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120e7e 5 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[93, 4]
    (.letOp (n := 100) (.out 0x120e86 (leaR64Effect 0x120e86 7 (.sib 4 none 0 (.d32 0x188))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 101) (.exec 0x120e86 (fun s => s.RIP = 0x120e86) (leaR64Effect 0x120e86 7 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 102) (.out 0x120e8e (leaR64Effect 0x120e8e 6 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 103) (.exec 0x120e8e (fun s => s.RIP = 0x120e8e) (leaR64Effect 0x120e8e 6 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 104) (.out 0x120e96 (callEffect (fun _ => 0x114930) 0x120e9b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 105) (.exec 0x120e96 (PushPre 0x120e96 5) (callEffect (fun _ => 0x114930) 0x120e9b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.const ⟨64, 0x120e9b⟩) #v[]
    (.terminate (.call ⟨.l114930, RegMap.args [(0, 55), (1, 87), (3, 3), (4, 104), (5, 93), (6, 102), (7, 100), (10, 10), (11, 11), (12, 79), (13, 85), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 107⟩ { target := .l120e9b, kept := #v[], arity := rfl, guard := some (Fin.last 106) })))))))))))))))

def bytes_l120e17_1 : List UInt8 :=
  [0x48, 0x31, 0xCD, 0x4C, 0x89, 0xB4, 0x24, 0x08, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xBC, 0x24, 0x10,
    0x01, 0x00, 0x00, 0x4C, 0x89, 0xA4, 0x24, 0x18, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xAC, 0x24, 0x20,
    0x01, 0x00, 0x00, 0x48, 0x89, 0xAC, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x88,
    0x01, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0x08, 0x01, 0x00, 0x00, 0xE8, 0x95, 0x3A, 0xFF, 0xFF]

theorem code_l120e17_1 : ∀ x ∈ codeRange 0x120e5b bytes_l120e17_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x20e5b 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l120e17 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x120e17 (movzxR32R8Effect 0x120e17 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x120e17 (fun s => s.RIP = 0x120e17) (movzxR32R8Effect 0x120e17 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x120e1a (negR64Effect 0x120e1a 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x120e1a (fun s => s.RIP = 0x120e1a) (negR64Effect 0x120e1a 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x120e1d (movR64M64Effect 0x120e1d 1 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x120e1d (LoadPre 0x120e1d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x120e1d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120e1d 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x120e22 (xorR64R64Effect 0x120e22 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[14, 57]
    (.letOp (n := 60) (.exec 0x120e22 (fun s => s.RIP = 0x120e22) (xorR64R64Effect 0x120e22 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[14, 57]
    (.letOp (n := 61) (.out 0x120e25 (andR64R64Effect 0x120e25 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[59, 55]
    (.letOp (n := 62) (.exec 0x120e25 (fun s => s.RIP = 0x120e25) (andR64R64Effect 0x120e25 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[59, 55]
    (.letOp (n := 63) (.out 0x120e28 (xorR64R64Effect 0x120e28 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[61, 57]
    (.letOp (n := 64) (.exec 0x120e28 (fun s => s.RIP = 0x120e28) (xorR64R64Effect 0x120e28 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[61, 57]
    (.letOp (n := 65) (.out 0x120e2b (movR64M64Effect 0x120e2b 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 66) (.exec 0x120e2b (LoadPre 0x120e2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x120e2b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120e2b 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x120e30 (xorR64R64Effect 0x120e30 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[15, 65]
    (.letOp (n := 68) (.exec 0x120e30 (fun s => s.RIP = 0x120e30) (xorR64R64Effect 0x120e30 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[15, 65]
    (.letOp (n := 69) (.out 0x120e33 (andR64R64Effect 0x120e33 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[67, 55]
    (.letOp (n := 70) (.exec 0x120e33 (fun s => s.RIP = 0x120e33) (andR64R64Effect 0x120e33 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[67, 55]
    (.letOp (n := 71) (.out 0x120e36 (xorR64R64Effect 0x120e36 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[69, 65]
    (.letOp (n := 72) (.exec 0x120e36 (fun s => s.RIP = 0x120e36) (xorR64R64Effect 0x120e36 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[69, 65]
    (.letOp (n := 73) (.out 0x120e39 (movR64M64Effect 0x120e39 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 74) (.exec 0x120e39 (LoadPre 0x120e39 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120e39 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120e39 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x120e3e (xorR64R64Effect 0x120e3e 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[12, 73]
    (.letOp (n := 76) (.exec 0x120e3e (fun s => s.RIP = 0x120e3e) (xorR64R64Effect 0x120e3e 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[12, 73]
    (.letOp (n := 77) (.out 0x120e41 (andR64R64Effect 0x120e41 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[75, 55]
    (.letOp (n := 78) (.exec 0x120e41 (fun s => s.RIP = 0x120e41) (andR64R64Effect 0x120e41 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[75, 55]
    (.letOp (n := 79) (.out 0x120e44 (xorR64R64Effect 0x120e44 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[77, 73]
    (.letOp (n := 80) (.exec 0x120e44 (fun s => s.RIP = 0x120e44) (xorR64R64Effect 0x120e44 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[77, 73]
    (.letOp (n := 81) (.out 0x120e47 (xorR64R64Effect 0x120e47 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[13, 3]
    (.letOp (n := 82) (.exec 0x120e47 (fun s => s.RIP = 0x120e47) (xorR64R64Effect 0x120e47 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[13, 3]
    (.letOp (n := 83) (.out 0x120e4a (andR64R64Effect 0x120e4a 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[81, 55]
    (.letOp (n := 84) (.exec 0x120e4a (fun s => s.RIP = 0x120e4a) (andR64R64Effect 0x120e4a 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[81, 55]
    (.letOp (n := 85) (.out 0x120e4d (xorR64R64Effect 0x120e4d 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[83, 3]
    (.letOp (n := 86) (.exec 0x120e4d (fun s => s.RIP = 0x120e4d) (xorR64R64Effect 0x120e4d 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[83, 3]
    (.letOp (n := 87) (.out 0x120e50 (movR64M64Effect 0x120e50 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 88) (.exec 0x120e50 (LoadPre 0x120e50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120e50 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120e50 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.out 0x120e55 (xorR64R64Effect 0x120e55 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[5, 87]
    (.letOp (n := 90) (.exec 0x120e55 (fun s => s.RIP = 0x120e55) (xorR64R64Effect 0x120e55 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[5, 87]
    (.letOp (n := 91) (.out 0x120e58 (andR64R64Effect 0x120e58 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[89, 55]
    (.letOp (n := 92) (.exec 0x120e58 (fun s => s.RIP = 0x120e58) (andR64R64Effect 0x120e58 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[89, 55]
    (b_l120e17_1))))))))))))))))))))))))))))))))))))))))

def bytes_l120e17 : List UInt8 :=
  [0x0F, 0xB6, 0xC0, 0x48, 0xF7, 0xD8, 0x48, 0x8B, 0x4C, 0x24, 0x60, 0x49, 0x31, 0xCE, 0x49, 0x21,
    0xC6, 0x49, 0x31, 0xCE, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x49, 0x31, 0xCF, 0x49, 0x21, 0xC7, 0x49,
    0x31, 0xCF, 0x48, 0x8B, 0x4C, 0x24, 0x08, 0x49, 0x31, 0xCC, 0x49, 0x21, 0xC4, 0x49, 0x31, 0xCC,
    0x49, 0x31, 0xDD, 0x49, 0x21, 0xC5, 0x49, 0x31, 0xDD, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x31,
    0xCD, 0x48, 0x21, 0xC5] ++ bytes_l120e17_1

theorem code_l120e17 : ∀ x ∈ codeRange 0x120e17 bytes_l120e17, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20e17 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l120e17_1

@[cfg_block] def b_l120e9b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x120e9b (movR64M64Effect 0x120e9b 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x120e9b (LoadPre 0x120e9b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x120e9b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120e9b 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x120ea0 (StorePre 0x120ea0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x120ea0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120ea0 0 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x120ea8 (movR64M64Effect 0x120ea8 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x120ea8 (LoadPre 0x120ea8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x120ea8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120ea8 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x120ead (StorePre 0x120ead 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x120ead + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120ead 0 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x120eb5 (movR64M64Effect 0x120eb5 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x120eb5 (LoadPre 0x120eb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x120eb5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120eb5 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x120eba (StorePre 0x120eba 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x120eba + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120eba 0 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x120ec2 (movR64M64Effect 0x120ec2 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x120ec2 (LoadPre 0x120ec2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x120ec2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120ec2 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x120ec7 (StorePre 0x120ec7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x120ec7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120ec7 0 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x120ecf (movR64M64Effect 0x120ecf 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x120ecf (LoadPre 0x120ecf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x120ecf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120ecf 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x120ed4 (StorePre 0x120ed4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x120ed4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120ed4 0 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.exec 0x120edc (StorePre 0x120edc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x120edc + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x120edc (.sib 4 none 0 (.d32 0x1b0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x120ee4 (leaR64Effect 0x120ee4 6 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 70) (.exec 0x120ee4 (fun s => s.RIP = 0x120ee4) (leaR64Effect 0x120ee4 6 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x120eec (movR32Imm32Effect 0x120eec 5 1 0xb) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 72) (.exec 0x120eec (fun s => s.RIP = 0x120eec) (movR32Imm32Effect 0x120eec 5 1 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x120ef1 (movR64M64Effect 0x120ef1 3 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 74) (.exec 0x120ef1 (LoadPre 0x120ef1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x120ef1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120ef1 3 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x120ef9 (movR64R64Effect 0x120ef9 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[73]
    (.letOp (n := 76) (.exec 0x120ef9 (fun s => s.RIP = 0x120ef9) (movR64R64Effect 0x120ef9 7 3) (Reg.operands [.gpr 3] [])) #v[73]
    (.letOp (n := 77) (.out 0x120efc (repMovsqEffect 0x120efc) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[69, 75, 71, 22]
    (.letOp (n := 78) (.out 0x120efc (repMovsqEffect 0x120efc) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[69, 75, 71, 22]
    (.letOp (n := 79) (.exec 0x120efc (RepPre 0x120efc (RepMovsqPre 0x120efc)) (repMovsqEffect 0x120efc) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[69, 75, 71, 22]
    (.letOp (n := 80) (.out 0x120eff (movR64M64Effect 0x120eff 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 81) (.exec 0x120eff (LoadPre 0x120eff (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x120eff + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120eff 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.out 0x120f07 (andR8M8Effect 0x120f07 4 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[80, 4]
    (.letOp (n := 83) (.exec 0x120f07 (LoadPre 0x120f07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x120f07 + BitVec.ofNat 64 4)) 1) (andR8M8Effect 0x120f07 4 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 84) (.out 0x120f0b (movzxR32R8Effect 0x120f0b 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[82]
    (.letOp (n := 85) (.exec 0x120f0b (fun s => s.RIP = 0x120f0b) (movzxR32R8Effect 0x120f0b 3 7 0) (Reg.operands [.gpr 0] [])) #v[82]
    (.letOp (n := 86) (.out 0x120f0e (callEffect (fun _ => 0x127d50) 0x120f13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 87) (.exec 0x120f0e (PushPre 0x120f0e 5) (callEffect (fun _ => 0x127d50) 0x120f13) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 88) (.const ⟨64, 0x120f13⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 82), (1, 78), (2, 2), (3, 73), (4, 86), (5, 5), (6, 77), (7, 84), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 89⟩ { target := .l120f13, kept := #v[], arity := rfl, guard := some (Fin.last 88) })))))))))))))))))))))))))))))))))))))

def bytes_l120e9b : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0x89, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44,
    0x24, 0x58, 0x48, 0x89, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24,
    0x78, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x84, 0x24, 0x80, 0x01, 0x00,
    0x00, 0xC6, 0x84, 0x24, 0xB0, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0x60, 0x01, 0x00,
    0x00, 0xB9, 0x0B, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89,
    0xDF, 0xF3, 0x48, 0xA5, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x22, 0x44, 0x24, 0x20,
    0x0F, 0xB6, 0xF8, 0xE8, 0x3D, 0x6E, 0x00, 0x00]

theorem code_l120e9b : ∀ x ∈ codeRange 0x120e9b bytes_l120e9b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x20e9b 120 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l120f13 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x120f13 (StorePre 0x120f13 3 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x120f13 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x120f13 3 0 (.base 3 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 54) (.out 0x120f16 (movR64R64Effect 0x120f16 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 55) (.exec 0x120f16 (fun s => s.RIP = 0x120f16) (movR64R64Effect 0x120f16 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 56) (.out 0x120f19 (addR64Imm32Effect 0x120f19 4 0x1b8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x120f19 (fun s => s.RIP = 0x120f19) (addR64Imm32Effect 0x120f19 4 0x1b8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x120f20 (popR64Effect 0x120f20 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[56]
    (.letOp (n := 59) (.out 0x120f20 (popR64Effect 0x120f20 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x120f20 (PopPre 0x120f20) (popR64Effect 0x120f20 1 3) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x120f21 (popR64Effect 0x120f21 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[59]
    (.letOp (n := 62) (.out 0x120f21 (popR64Effect 0x120f21 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x120f21 (PopPre 0x120f21) (popR64Effect 0x120f21 2 12) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x120f23 (popR64Effect 0x120f23 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[62]
    (.letOp (n := 65) (.out 0x120f23 (popR64Effect 0x120f23 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x120f23 (PopPre 0x120f23) (popR64Effect 0x120f23 2 13) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x120f25 (popR64Effect 0x120f25 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 68) (.out 0x120f25 (popR64Effect 0x120f25 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x120f25 (PopPre 0x120f25) (popR64Effect 0x120f25 2 14) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x120f27 (popR64Effect 0x120f27 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[68]
    (.letOp (n := 71) (.out 0x120f27 (popR64Effect 0x120f27 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x120f27 (PopPre 0x120f27) (popR64Effect 0x120f27 2 15) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x120f29 (popR64Effect 0x120f29 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[71]
    (.letOp (n := 74) (.out 0x120f29 (popR64Effect 0x120f29 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x120f29 (PopPre 0x120f29) (popR64Effect 0x120f29 1 5) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x120f2a (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[74]
    (.letOp (n := 77) (.out 0x120f2a (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x120f2a (RetPre 0x120f2a) (retEffect) (Reg.operands [.gpr 4] [])) #v[74]
    (.terminate (.ret (RegMap.args [(0, 54), (1, 1), (2, 2), (3, 58), (4, 77), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 79) (some ⟨76, by decide⟩))))))))))))))))))))))))))))

def bytes_l120f13 : List UInt8 :=
  [0x88, 0x43, 0x58, 0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xB8, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C,
    0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l120f13 : ∀ x ∈ codeRange 0x120f13 bytes_l120f13, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x20f13 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l121480 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x121480 (pushR64Effect 0x121480 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x121480 (PushPre 0x121480 1) (pushR64Effect 0x121480 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x121481 (pushR64Effect 0x121481 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x121481 (PushPre 0x121481 2) (pushR64Effect 0x121481 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x121483 (pushR64Effect 0x121483 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x121483 (PushPre 0x121483 2) (pushR64Effect 0x121483 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x121485 (pushR64Effect 0x121485 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x121485 (PushPre 0x121485 2) (pushR64Effect 0x121485 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x121487 (pushR64Effect 0x121487 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x121487 (PushPre 0x121487 1) (pushR64Effect 0x121487 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x121488 (subR64Imm8Effect 0x121488 4 0x60) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x121488 (fun s => s.RIP = 0x121488) (subR64Imm8Effect 0x121488 4 0x60) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x12148c (movR64R64Effect 0x12148c 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 66) (.exec 0x12148c (fun s => s.RIP = 0x12148c) (movR64R64Effect 0x12148c 2 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 67) (.out 0x12148f (movR64R64Effect 0x12148f 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x12148f (fun s => s.RIP = 0x12148f) (movR64R64Effect 0x12148f 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x121492 (movzxR32M8Effect 0x121492 3 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 70) (.exec 0x121492 (LoadPre 0x121492 (fun s => AddrMode.addr (.base 6 .none) s (0x121492 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x121492 3 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x121495 (movzxR32R8Effect 0x121495 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[69]
    (.letOp (n := 72) (.exec 0x121495 (fun s => s.RIP = 0x121495) (movzxR32R8Effect 0x121495 3 1 0) (Reg.operands [.gpr 0] [])) #v[69]
    (.letOp (n := 73) (.out 0x121498 (leaR32Effect 0x121498 3 6 (.base 1 (.d8 0xfe))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 74) (.exec 0x121498 (fun s => s.RIP = 0x121498) (leaR32Effect 0x121498 3 6 (.base 1 (.d8 0xfe))) (Reg.operands [.gpr 1] [])) #v[71]
    (.letOp (n := 75) (.out 0x12149b (cmpR32Imm8Effect 0x12149b 3 6 0x4) (EffectPart.reads (.flag .CF) [.gpr 6] []) (.flag .CF)) #v[73]
    (.letOp (n := 76) (.exec 0x12149b (fun s => s.RIP = 0x12149b) (cmpR32Imm8Effect 0x12149b 3 6 0x4) (Reg.operands [.gpr 6] [])) #v[73]
    (.letOp (n := 77) (.pure (condOp 3)) #v[75]
    (.terminate (.condBr (Fin.last 77) ⟨.l1214d0, RegMap.args [(0, 69), (1, 71), (2, 65), (3, 67), (4, 63), (5, 5), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ ⟨.l1214a0, RegMap.args [(0, 69), (1, 71), (2, 65), (3, 67), (4, 63), (5, 5), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l121480 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x60, 0x48, 0x89, 0xF2, 0x48,
    0x89, 0xFB, 0x0F, 0xB6, 0x06, 0x0F, 0xB6, 0xC8, 0x8D, 0x71, 0xFE, 0x83, 0xFE, 0x04, 0x73, 0x30]

theorem code_l121480 : ∀ x ∈ codeRange 0x121480 bytes_l121480, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x21480 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1214a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1214a0 (leaR64Effect 0x1214a0 14 (.base 2 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 54) (.exec 0x1214a0 (fun s => s.RIP = 0x1214a0) (leaR64Effect 0x1214a0 14 (.base 2 (.d8 0x1))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x1214a4 (movR32R32Effect 0x1214a4 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 56) (.exec 0x1214a4 (fun s => s.RIP = 0x1214a4) (movR32R32Effect 0x1214a4 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x1214a6 (andR8Imm8Effect 0x1214a6 3 1 0x6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.exec 0x1214a6 (fun s => s.RIP = 0x1214a6) (andR8Imm8Effect 0x1214a6 3 1 0x6) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 59) (.out 0x1214a9 (cmpR8Imm8Effect 0x1214a9 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[57]
    (.letOp (n := 60) (.exec 0x1214a9 (fun s => s.RIP = 0x1214a9) (cmpR8Imm8Effect 0x1214a9 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l1214b5, RegMap.args [(0, 0), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l1214ae, RegMap.args [(0, 0), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l1214a0 : List UInt8 :=
  [0x4C, 0x8D, 0x72, 0x01, 0x89, 0xC1, 0x80, 0xE1, 0x06, 0x80, 0xF9, 0x02, 0x75, 0x07]

theorem code_l1214a0 : ∀ x ∈ codeRange 0x1214a0 bytes_l1214a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x214a0 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1214ae : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1214ae (andAlImm8Effect 0x1214ae 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x1214ae (fun s => s.RIP = 0x1214ae) (andAlImm8Effect 0x1214ae 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x1214b0 (movzxR32R8Effect 0x1214b0 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x1214b0 (fun s => s.RIP = 0x1214b0) (movzxR32R8Effect 0x1214b0 3 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.terminate (.br ⟨.l1214bb, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1214ae : List UInt8 :=
  [0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xEB, 0x06]

theorem code_l1214ae : ∀ x ∈ codeRange 0x1214ae bytes_l1214ae, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x214ae 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1214b5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1214b5 (cmpAlImm8Effect 0x1214b5 0x5) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x1214b5 (fun s => s.RIP = 0x1214b5) (cmpAlImm8Effect 0x1214b5 0x5) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1214f3, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1214b9, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1214b5 : List UInt8 :=
  [0x3C, 0x05, 0x75, 0x3A]

theorem code_l1214b5 : ∀ x ∈ codeRange 0x1214b5 bytes_l1214b5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x214b5 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1214b9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1214b9 (xorR32R32Effect 0x1214b9 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x1214b9 (fun s => s.RIP = 0x1214b9) (xorR32R32Effect 0x1214b9 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l1214bb, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1214b9 : List UInt8 :=
  [0x31, 0xFF]

theorem code_l1214b9 : ∀ x ∈ codeRange 0x1214b9 bytes_l1214b9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x214b9 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1214bb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1214bb (callEffect (fun _ => 0x127d50) 0x1214c0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x1214bb (PushPre 0x1214bb 5) (callEffect (fun _ => 0x127d50) 0x1214c0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.const ⟨64, 0x1214c0⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ { target := .l1214c0, kept := #v[], arity := rfl, guard := some (Fin.last 55) }))))

def bytes_l1214bb : List UInt8 :=
  [0xE8, 0x90, 0x68, 0x00, 0x00]

theorem code_l1214bb : ∀ x ∈ codeRange 0x1214bb bytes_l1214bb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x214bb 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1214c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1214c0 (movzxR32R8Effect 0x1214c0 3 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[0]
    (.letOp (n := 54) (.exec 0x1214c0 (fun s => s.RIP = 0x1214c0) (movzxR32R8Effect 0x1214c0 3 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x1214c3 (movR64R64Effect 0x1214c3 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x1214c3 (fun s => s.RIP = 0x1214c3) (movR64R64Effect 0x1214c3 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1214c6 (movR64R64Effect 0x1214c6 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x1214c6 (fun s => s.RIP = 0x1214c6) (movR64R64Effect 0x1214c6 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x1214c9 (callEffect (fun _ => 0x1205b0) 0x1214ce) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1214c9 (PushPre 0x1214c9 5) (callEffect (fun _ => 0x1205b0) 0x1214ce) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1214ce⟩) #v[]
    (.terminate (.call ⟨.l1205b0, RegMap.args [(0, 0), (2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1214ce, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1214c0 : List UInt8 :=
  [0x0F, 0xB6, 0xD0, 0x48, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0xE8, 0xE2, 0xF0, 0xFF, 0xFF]

theorem code_l1214c0 : ∀ x ∈ codeRange 0x1214c0 bytes_l1214c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x214c0 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1214ce : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l121502, RegMap.args (entryMap (live .l1214ce)) 53⟩)

def bytes_l1214ce : List UInt8 :=
  [0xEB, 0x32]

theorem code_l1214ce : ∀ x ∈ codeRange 0x1214ce bytes_l1214ce, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x214ce 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1214d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1214d0 (testR32R32Effect 0x1214d0 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[1, 1]
    (.letOp (n := 54) (.exec 0x1214d0 (fun s => s.RIP = 0x1214d0) (testR32R32Effect 0x1214d0 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1215a9, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1214d8, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1214d0 : List UInt8 :=
  [0x85, 0xC9, 0x0F, 0x85, 0xD1, 0x00, 0x00, 0x00]

theorem code_l1214d0 : ∀ x ∈ codeRange 0x1214d0 bytes_l1214d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x214d0 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1214d8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1214d8 (movR32Imm32Effect 0x1214d8 5 1 0xb) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x1214d8 (fun s => s.RIP = 0x1214d8) (movR32Imm32Effect 0x1214d8 5 1 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1214dd (movR64R64Effect 0x1214dd 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 56) (.exec 0x1214dd (fun s => s.RIP = 0x1214dd) (movR64R64Effect 0x1214dd 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x1214e0 (movR64Imm32Effect 0x1214e0 6 0x2033a8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x1214e0 (fun s => s.RIP = 0x1214e0) (movR64Imm32Effect 0x1214e0 6 0x2033a8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1214e7 (repMovsqEffect 0x1214e7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x1214e7 (repMovsqEffect 0x1214e7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[57, 55, 53, 22]
    (.letOp (n := 61) (.out 0x1214e7 (repMovsqEffect 0x1214e7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[57, 55, 53, 22]
    (.letOp (n := 62) (.exec 0x1214e7 (RepPre 0x1214e7 (RepMovsqPre 0x1214e7)) (repMovsqEffect 0x1214e7) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 63) (.exec 0x1214ea (StorePre 0x1214ea 4 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x1214ea + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1214ea (.base 3 (.d8 0x58)) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l121599, RegMap.args [(1, 61), (2, 2), (3, 3), (4, 4), (6, 59), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l1214d8 : List UInt8 :=
  [0xB9, 0x0B, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDF, 0x48, 0xC7, 0xC6, 0xA8, 0x33, 0x20, 0x00, 0xF3,
    0x48, 0xA5, 0xC6, 0x43, 0x58, 0x01, 0xE9, 0xA6, 0x00, 0x00, 0x00]

theorem code_l1214d8 : ∀ x ∈ codeRange 0x1214d8 bytes_l1214d8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x214d8 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1214f3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1214f3 (addR64Imm8Effect 0x1214f3 2 0x21) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 54) (.exec 0x1214f3 (fun s => s.RIP = 0x1214f3) (addR64Imm8Effect 0x1214f3 2 0x21) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x1214f7 (movR64R64Effect 0x1214f7 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x1214f7 (fun s => s.RIP = 0x1214f7) (movR64R64Effect 0x1214f7 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1214fa (movR64R64Effect 0x1214fa 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x1214fa (fun s => s.RIP = 0x1214fa) (movR64R64Effect 0x1214fa 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x1214fd (callEffect (fun _ => 0x11f780) 0x121502) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1214fd (PushPre 0x1214fd 5) (callEffect (fun _ => 0x11f780) 0x121502) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x121502⟩) #v[]
    (.terminate (.call ⟨.l11f780, RegMap.args [(2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l121502, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1214f3 : List UInt8 :=
  [0x48, 0x83, 0xC2, 0x21, 0x48, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0xE8, 0x7E, 0xE2, 0xFF, 0xFF]

theorem code_l1214f3 : ∀ x ∈ codeRange 0x1214f3 bytes_l1214f3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x214f3 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l121502_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x121551 (movR64M64Effect 0x121551 12 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 94) (.exec 0x121551 (LoadPre 0x121551 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x121551 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121551 12 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x121556 (andR64R64Effect 0x121556 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[93, 59]
    (.letOp (n := 96) (.exec 0x121556 (fun s => s.RIP = 0x121556) (andR64R64Effect 0x121556 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[93, 59]
    (.letOp (n := 97) (.out 0x121559 (andR64M64Effect 0x121559 2 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[59, 4]
    (.letOp (n := 98) (.exec 0x121559 (LoadPre 0x121559 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x121559 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x121559 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 99) (.out 0x12155e (movR32R32Effect 0x12155e 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 100) (.exec 0x12155e (fun s => s.RIP = 0x12155e) (movR32R32Effect 0x12155e 2 5 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 101) (.out 0x121560 (negR8Effect 0x121560 3 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[99]
    (.letOp (n := 102) (.exec 0x121560 (fun s => s.RIP = 0x121560) (negR8Effect 0x121560 3 5) (Reg.operands [.gpr 5] [])) #v[99]
    (.letOp (n := 103) (.out 0x121563 (xorR8Imm8Effect 0x121563 3 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 104) (.exec 0x121563 (fun s => s.RIP = 0x121563) (xorR8Imm8Effect 0x121563 3 1 0x1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 105) (.out 0x121566 (andR8R8Effect 0x121566 3 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[103, 101]
    (.letOp (n := 106) (.exec 0x121566 (fun s => s.RIP = 0x121566) (andR8R8Effect 0x121566 3 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[103, 101]
    (.letOp (n := 107) (.out 0x121569 (xorR8Imm8Effect 0x121569 3 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[105]
    (.letOp (n := 108) (.exec 0x121569 (fun s => s.RIP = 0x121569) (xorR8Imm8Effect 0x121569 3 1 0x1) (Reg.operands [.gpr 1] [])) #v[105]
    (.letOp (n := 109) (.exec 0x12156c (StorePre 0x12156c 3 (fun s => AddrMode.addr (.base 3 .none) s (0x12156c + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x12156c 6 (.base 3 .none)) (Reg.operands [.gpr 6, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 110) (.exec 0x12156f (StorePre 0x12156f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12156f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12156f 7 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[67, 3]
    (.letOp (n := 111) (.exec 0x121573 (StorePre 0x121573 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x121573 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x121573 8 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[71, 3]
    (.letOp (n := 112) (.exec 0x121577 (StorePre 0x121577 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x121577 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x121577 9 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[75, 3]
    (.letOp (n := 113) (.exec 0x12157b (StorePre 0x12157b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x12157b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12157b 10 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[79, 3]
    (.letOp (n := 114) (.exec 0x12157f (StorePre 0x12157f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x12157f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12157f 11 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 11, .gpr 3] [])) #v[83, 3]
    (.letOp (n := 115) (.exec 0x121583 (StorePre 0x121583 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x121583 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x121583 14 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 14, .gpr 3] [])) #v[87, 3]
    (.letOp (n := 116) (.exec 0x121587 (StorePre 0x121587 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x121587 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x121587 15 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[91, 3]
    (.letOp (n := 117) (.exec 0x12158b (StorePre 0x12158b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x12158b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12158b 12 (.base 3 (.d8 0x40))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[95, 3]
    (.letOp (n := 118) (.exec 0x12158f (StorePre 0x12158f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x12158f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12158f 2 (.base 3 (.d8 0x48))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[97, 3]
    (.letOp (n := 119) (.exec 0x121593 (StorePre 0x121593 3 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x121593 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x121593 3 1 (.base 3 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[107, 3]
    (.letOp (n := 120) (.exec 0x121596 (StorePre 0x121596 3 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x121596 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x121596 3 0 (.base 3 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 3]
    (.terminate (.br ⟨.l121599, RegMap.args [(0, 53), (1, 107), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 121⟩)))))))))))))))))))))))))))))

def bytes_l121502_1 : List UInt8 :=
  [0x4C, 0x8B, 0x64, 0x24, 0x40, 0x49, 0x21, 0xD4, 0x48, 0x23, 0x54, 0x24, 0x48, 0x89, 0xC5, 0x40,
    0xF6, 0xDD, 0x80, 0xF1, 0x01, 0x40, 0x20, 0xE9, 0x80, 0xF1, 0x01, 0x48, 0x89, 0x33, 0x48, 0x89,
    0x7B, 0x08, 0x4C, 0x89, 0x43, 0x10, 0x4C, 0x89, 0x4B, 0x18, 0x4C, 0x89, 0x53, 0x20, 0x4C, 0x89,
    0x5B, 0x28, 0x4C, 0x89, 0x73, 0x30, 0x4C, 0x89, 0x7B, 0x38, 0x4C, 0x89, 0x63, 0x40, 0x48, 0x89,
    0x53, 0x48, 0x88, 0x4B, 0x50, 0x88, 0x43, 0x58]

theorem code_l121502_1 : ∀ x ∈ codeRange 0x121551 bytes_l121502_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x21551 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l121502 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x121502 (movzxR32M8Effect 0x121502 5 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x121502 (LoadPre 0x121502 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x121502 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x121502 5 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x121507 (movzxR32M8Effect 0x121507 5 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x121507 (LoadPre 0x121507 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x121507 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x121507 5 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x12150c (movR64R64Effect 0x12150c 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 58) (.exec 0x12150c (fun s => s.RIP = 0x12150c) (movR64R64Effect 0x12150c 2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.out 0x12150f (negR64Effect 0x12150f 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 60) (.exec 0x12150f (fun s => s.RIP = 0x12150f) (negR64Effect 0x12150f 2) (Reg.operands [.gpr 2] [])) #v[57]
    (.letOp (n := 61) (.out 0x121512 (movR64M64Effect 0x121512 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x121512 (LoadPre 0x121512 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x121512 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x121512 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x121516 (andR64R64Effect 0x121516 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x121516 (fun s => s.RIP = 0x121516) (andR64R64Effect 0x121516 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x121519 (movR64M64Effect 0x121519 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x121519 (LoadPre 0x121519 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x121519 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121519 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x12151e (andR64R64Effect 0x12151e 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[65, 59]
    (.letOp (n := 68) (.exec 0x12151e (fun s => s.RIP = 0x12151e) (andR64R64Effect 0x12151e 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[65, 59]
    (.letOp (n := 69) (.out 0x121521 (movR64M64Effect 0x121521 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 70) (.exec 0x121521 (LoadPre 0x121521 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x121521 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121521 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x121526 (andR64R64Effect 0x121526 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[69, 59]
    (.letOp (n := 72) (.exec 0x121526 (fun s => s.RIP = 0x121526) (andR64R64Effect 0x121526 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[69, 59]
    (.letOp (n := 73) (.out 0x121529 (movR64M64Effect 0x121529 9 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 74) (.exec 0x121529 (LoadPre 0x121529 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121529 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121529 9 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x12152e (andR64R64Effect 0x12152e 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[73, 59]
    (.letOp (n := 76) (.exec 0x12152e (fun s => s.RIP = 0x12152e) (andR64R64Effect 0x12152e 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[73, 59]
    (.letOp (n := 77) (.out 0x121531 (movR64M64Effect 0x121531 10 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 78) (.exec 0x121531 (LoadPre 0x121531 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x121531 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121531 10 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x121536 (andR64R64Effect 0x121536 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[77, 59]
    (.letOp (n := 80) (.exec 0x121536 (fun s => s.RIP = 0x121536) (andR64R64Effect 0x121536 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[77, 59]
    (.letOp (n := 81) (.out 0x121539 (movR64M64Effect 0x121539 11 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 82) (.exec 0x121539 (LoadPre 0x121539 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x121539 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121539 11 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x12153e (andR64R64Effect 0x12153e 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[81, 59]
    (.letOp (n := 84) (.exec 0x12153e (fun s => s.RIP = 0x12153e) (andR64R64Effect 0x12153e 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[81, 59]
    (.letOp (n := 85) (.out 0x121541 (movR64M64Effect 0x121541 14 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 86) (.exec 0x121541 (LoadPre 0x121541 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x121541 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121541 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x121546 (andR64R64Effect 0x121546 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[85, 59]
    (.letOp (n := 88) (.exec 0x121546 (fun s => s.RIP = 0x121546) (andR64R64Effect 0x121546 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[85, 59]
    (.letOp (n := 89) (.out 0x121549 (movR64M64Effect 0x121549 15 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 90) (.exec 0x121549 (LoadPre 0x121549 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x121549 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121549 15 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.out 0x12154e (andR64R64Effect 0x12154e 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[89, 59]
    (.letOp (n := 92) (.exec 0x12154e (fun s => s.RIP = 0x12154e) (andR64R64Effect 0x12154e 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[89, 59]
    (b_l121502_1))))))))))))))))))))))))))))))))))))))))

def bytes_l121502 : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x58, 0x0F, 0xB6, 0x4C, 0x24, 0x50, 0x48, 0x89, 0xC2, 0x48, 0xF7, 0xDA,
    0x48, 0x8B, 0x34, 0x24, 0x48, 0x21, 0xD6, 0x48, 0x8B, 0x7C, 0x24, 0x08, 0x48, 0x21, 0xD7, 0x4C,
    0x8B, 0x44, 0x24, 0x10, 0x49, 0x21, 0xD0, 0x4C, 0x8B, 0x4C, 0x24, 0x18, 0x49, 0x21, 0xD1, 0x4C,
    0x8B, 0x54, 0x24, 0x20, 0x49, 0x21, 0xD2, 0x4C, 0x8B, 0x5C, 0x24, 0x28, 0x49, 0x21, 0xD3, 0x4C,
    0x8B, 0x74, 0x24, 0x30, 0x49, 0x21, 0xD6, 0x4C, 0x8B, 0x7C, 0x24, 0x38, 0x49, 0x21, 0xD7] ++ bytes_l121502_1

theorem code_l121502 : ∀ x ∈ codeRange 0x121502 bytes_l121502, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21502 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121502_1

@[cfg_block] def b_l121599 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x121599 (movR64R64Effect 0x121599 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x121599 (fun s => s.RIP = 0x121599) (movR64R64Effect 0x121599 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x12159c (addR64Imm8Effect 0x12159c 4 0x60) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x12159c (fun s => s.RIP = 0x12159c) (addR64Imm8Effect 0x12159c 4 0x60) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1215a0 (popR64Effect 0x1215a0 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x1215a0 (popR64Effect 0x1215a0 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x1215a0 (PopPre 0x1215a0) (popR64Effect 0x1215a0 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x1215a1 (popR64Effect 0x1215a1 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x1215a1 (popR64Effect 0x1215a1 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x1215a1 (PopPre 0x1215a1) (popR64Effect 0x1215a1 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x1215a3 (popR64Effect 0x1215a3 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[61]
    (.letOp (n := 64) (.out 0x1215a3 (popR64Effect 0x1215a3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x1215a3 (PopPre 0x1215a3) (popR64Effect 0x1215a3 2 14) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x1215a5 (popR64Effect 0x1215a5 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[64]
    (.letOp (n := 67) (.out 0x1215a5 (popR64Effect 0x1215a5 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x1215a5 (PopPre 0x1215a5) (popR64Effect 0x1215a5 2 15) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x1215a7 (popR64Effect 0x1215a7 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[67]
    (.letOp (n := 70) (.out 0x1215a7 (popR64Effect 0x1215a7 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x1215a7 (PopPre 0x1215a7) (popR64Effect 0x1215a7 1 5) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x1215a8 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[70]
    (.letOp (n := 73) (.out 0x1215a8 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x1215a8 (RetPre 0x1215a8) (retEffect) (Reg.operands [.gpr 4] [])) #v[70]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 63), (15, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 75) (some ⟨72, by decide⟩))))))))))))))))))))))))

def bytes_l121599 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x60, 0x5B, 0x41, 0x5C, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l121599 : ∀ x ∈ codeRange 0x121599 bytes_l121599, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x21599 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1215a9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1215a9 (StorePre 0x1215a9 7 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1215a9 + BitVec.ofNat 64 7)) 4) (movM32Imm32Effect 0x1215a9 7 (.sib 4 none 0 .none) 0x3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x1215b0 (movR64R64Effect 0x1215b0 2 4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 55) (.exec 0x1215b0 (fun s => s.RIP = 0x1215b0) (movR64R64Effect 0x1215b0 2 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1215b3 (movR32Imm32Effect 0x1215b3 5 6 0xb) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 57) (.exec 0x1215b3 (fun s => s.RIP = 0x1215b3) (movR32Imm32Effect 0x1215b3 5 6 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x1215b8 (movR64Imm32Effect 0x1215b8 7 0x202e30) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 59) (.exec 0x1215b8 (fun s => s.RIP = 0x1215b8) (movR64Imm32Effect 0x1215b8 7 0x202e30) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x1215bf (movR64Imm32Effect 0x1215bf 1 0x202e10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x1215bf (fun s => s.RIP = 0x1215bf) (movR64Imm32Effect 0x1215bf 1 0x202e10) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x1215c6 (movR64Imm32Effect 0x1215c6 8 0x202e40) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 63) (.exec 0x1215c6 (fun s => s.RIP = 0x1215c6) (movR64Imm32Effect 0x1215c6 8 0x202e40) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x1215cd (callEffect (fun _ => 0x1295a0) 0x1215d2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x1215cd (PushPre 0x1215cd 5) (callEffect (fun _ => 0x1295a0) 0x1215d2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x1215d2⟩) #v[]
    (.terminate (.call ⟨.l1295a0, RegMap.args [(1, 60), (2, 54), (4, 64), (5, 5), (6, 56), (7, 58), (8, 62)] 67⟩ { target := .l1215d2, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l1215a9 : List UInt8 :=
  [0xC7, 0x04, 0x24, 0x03, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE2, 0xBE, 0x0B, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0xC7, 0x30, 0x2E, 0x20, 0x00, 0x48, 0xC7, 0xC1, 0x10, 0x2E, 0x20, 0x00, 0x49, 0xC7, 0xC0,
    0x40, 0x2E, 0x20, 0x00, 0xE8, 0xCE, 0x7F, 0x00, 0x00]

theorem code_l1215a9 : ∀ x ∈ codeRange 0x1215a9 bytes_l1215a9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x215a9 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1215d2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1215d2 (fun s => s.RIP = 0x1215d2) (fun _ => nopEffect 0x1215d2 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x1215dc (fun s => s.RIP = 0x1215dc) (fun _ => nopEffect 0x1215dc 4) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1215e0, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1215d2 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0F, 0x1F, 0x40, 0x00]

theorem code_l1215d2 : ∀ x ∈ codeRange 0x1215d2 bytes_l1215d2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x215d2 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1215e0_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.out 0x12162b (movR64R64Effect 0x12162b 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[84]
    (.letOp (n := 89) (.exec 0x12162b (fun s => s.RIP = 0x12162b) (movR64R64Effect 0x12162b 7 15) (Reg.operands [.gpr 15] [])) #v[84]
    (.letOp (n := 90) (.out 0x12162e (callEffect (fun _ => 0x114930) 0x121633) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 91) (.exec 0x12162e (PushPre 0x12162e 5) (callEffect (fun _ => 0x114930) 0x121633) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 92) (.const ⟨64, 0x121633⟩) #v[]
    (.terminate (.call ⟨.l114930, RegMap.args [(0, 78), (1, 80), (2, 2), (3, 67), (4, 90), (5, 63), (6, 86), (7, 88), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩ { target := .l121633, kept := #v[], arity := rfl, guard := some (Fin.last 92) }))))))

def bytes_l1215e0_1 : List UInt8 :=
  [0x4C, 0x89, 0xFF, 0xE8, 0xFD, 0x32, 0xFF, 0xFF]

theorem code_l1215e0_1 : ∀ x ∈ codeRange 0x12162b bytes_l1215e0_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2162b 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1215e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1215e0 (pushR64Effect 0x1215e0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1215e0 (PushPre 0x1215e0 1) (pushR64Effect 0x1215e0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1215e1 (pushR64Effect 0x1215e1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1215e1 (PushPre 0x1215e1 2) (pushR64Effect 0x1215e1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1215e3 (pushR64Effect 0x1215e3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1215e3 (PushPre 0x1215e3 2) (pushR64Effect 0x1215e3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1215e5 (pushR64Effect 0x1215e5 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[57, 3]
    (.letOp (n := 60) (.exec 0x1215e5 (PushPre 0x1215e5 1) (pushR64Effect 0x1215e5 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 61) (.out 0x1215e6 (subR64Imm32Effect 0x1215e6 4 0x118) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x1215e6 (fun s => s.RIP = 0x1215e6) (subR64Imm32Effect 0x1215e6 4 0x118) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.out 0x1215ed (movR32R32Effect 0x1215ed 2 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 64) (.exec 0x1215ed (fun s => s.RIP = 0x1215ed) (movR32R32Effect 0x1215ed 2 5 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 65) (.out 0x1215ef (movR64R64Effect 0x1215ef 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 66) (.exec 0x1215ef (fun s => s.RIP = 0x1215ef) (movR64R64Effect 0x1215ef 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 67) (.out 0x1215f2 (movR64R64Effect 0x1215f2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x1215f2 (fun s => s.RIP = 0x1215f2) (movR64R64Effect 0x1215f2 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x1215f5 (movR64M64Effect 0x1215f5 0 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 70) (.exec 0x1215f5 (LoadPre 0x1215f5 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1215f5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1215f5 0 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.exec 0x1215f9 (StorePre 0x1215f9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1215f9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1215f9 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 61]
    (.letOp (n := 72) (.out 0x1215fe (movR64M64Effect 0x1215fe 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 73) (.exec 0x1215fe (LoadPre 0x1215fe (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1215fe + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1215fe 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 74) (.exec 0x121602 (StorePre 0x121602 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x121602 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121602 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 61]
    (.letOp (n := 75) (.out 0x121607 (movR64M64Effect 0x121607 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 76) (.exec 0x121607 (LoadPre 0x121607 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x121607 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x121607 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.exec 0x12160b (StorePre 0x12160b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12160b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12160b 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 61]
    (.letOp (n := 78) (.out 0x121610 (movR64M64Effect 0x121610 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 79) (.exec 0x121610 (LoadPre 0x121610 (fun s => AddrMode.addr (.base 6 .none) s (0x121610 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x121610 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 80) (.out 0x121613 (movR64M64Effect 0x121613 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 81) (.exec 0x121613 (LoadPre 0x121613 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x121613 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x121613 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 82) (.exec 0x121617 (StorePre 0x121617 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x121617 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121617 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[80, 61]
    (.letOp (n := 83) (.exec 0x12161c (StorePre 0x12161c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12161c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12161c 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 61]
    (.letOp (n := 84) (.out 0x121621 (leaR64Effect 0x121621 15 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[61]
    (.letOp (n := 85) (.exec 0x121621 (fun s => s.RIP = 0x121621) (leaR64Effect 0x121621 15 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 86) (.out 0x121626 (leaR64Effect 0x121626 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[61]
    (.letOp (n := 87) (.exec 0x121626 (fun s => s.RIP = 0x121626) (leaR64Effect 0x121626 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[61]
    (b_l1215e0_1)))))))))))))))))))))))))))))))))))

def bytes_l1215e0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x53, 0x48, 0x81, 0xEC, 0x18, 0x01, 0x00, 0x00, 0x89, 0xD5, 0x49,
    0x89, 0xF6, 0x48, 0x89, 0xFB, 0x48, 0x8B, 0x46, 0x20, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8B,
    0x46, 0x18, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x44, 0x24, 0x18,
    0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24,
    0x08, 0x4C, 0x8D, 0x7C, 0x24, 0x50, 0x48, 0x8D, 0x74, 0x24, 0x08] ++ bytes_l1215e0_1

theorem code_l1215e0 : ∀ x ∈ codeRange 0x1215e0 bytes_l1215e0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x215e0 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1215e0_1

@[cfg_block] def b_l121633 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x121633 (leaR64Effect 0x121633 7 (.sib 4 none 0 (.d32 0x97))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x121633 (fun s => s.RIP = 0x121633) (leaR64Effect 0x121633 7 (.sib 4 none 0 (.d32 0x97))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12163b (movR64R64Effect 0x12163b 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 56) (.exec 0x12163b (fun s => s.RIP = 0x12163b) (movR64R64Effect 0x12163b 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x12163e (callEffect (fun _ => 0x1148d0) 0x121643) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x12163e (PushPre 0x12163e 5) (callEffect (fun _ => 0x1148d0) 0x121643) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x121643⟩) #v[]
    (.terminate (.call ⟨.l1148d0, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l121643, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l121633 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x97, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFE, 0xE8, 0x8D, 0x32, 0xFF, 0xFF]

theorem code_l121633 : ∀ x ∈ codeRange 0x121633 bytes_l121633, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x21633 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l121643 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x121643 (movR64M64Effect 0x121643 0 (.base 14 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 54) (.exec 0x121643 (LoadPre 0x121643 (fun s => AddrMode.addr (.base 14 (.d8 0x48)) s (0x121643 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x121643 0 (.base 14 (.d8 0x48))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.exec 0x121647 (StorePre 0x121647 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x121647 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121647 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x12164c (movR64M64Effect 0x12164c 0 (.base 14 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 57) (.exec 0x12164c (LoadPre 0x12164c (fun s => AddrMode.addr (.base 14 (.d8 0x40)) s (0x12164c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12164c 0 (.base 14 (.d8 0x40))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.exec 0x121650 (StorePre 0x121650 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x121650 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121650 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x121655 (movR64M64Effect 0x121655 0 (.base 14 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 60) (.exec 0x121655 (LoadPre 0x121655 (fun s => AddrMode.addr (.base 14 (.d8 0x38)) s (0x121655 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x121655 0 (.base 14 (.d8 0x38))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.exec 0x121659 (StorePre 0x121659 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121659 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121659 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x12165e (movR64M64Effect 0x12165e 0 (.base 14 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 63) (.exec 0x12165e (LoadPre 0x12165e (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x12165e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12165e 0 (.base 14 (.d8 0x28))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 64) (.out 0x121662 (movR64M64Effect 0x121662 1 (.base 14 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 65) (.exec 0x121662 (LoadPre 0x121662 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x121662 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x121662 1 (.base 14 (.d8 0x30))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 66) (.exec 0x121666 (StorePre 0x121666 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x121666 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121666 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x12166b (StorePre 0x12166b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12166b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12166b 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x121670 (leaR64Effect 0x121670 15 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 69) (.exec 0x121670 (fun s => s.RIP = 0x121670) (leaR64Effect 0x121670 15 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x121675 (leaR64Effect 0x121675 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 71) (.exec 0x121675 (fun s => s.RIP = 0x121675) (leaR64Effect 0x121675 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x12167a (movR64R64Effect 0x12167a 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[68]
    (.letOp (n := 73) (.exec 0x12167a (fun s => s.RIP = 0x12167a) (movR64R64Effect 0x12167a 7 15) (Reg.operands [.gpr 15] [])) #v[68]
    (.letOp (n := 74) (.out 0x12167d (callEffect (fun _ => 0x114930) 0x121682) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 75) (.exec 0x12167d (PushPre 0x12167d 5) (callEffect (fun _ => 0x114930) 0x121682) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.const ⟨64, 0x121682⟩) #v[]
    (.terminate (.call ⟨.l114930, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 74), (5, 5), (6, 70), (7, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩ { target := .l121682, kept := #v[], arity := rfl, guard := some (Fin.last 76) })))))))))))))))))))))))))

def bytes_l121643 : List UInt8 :=
  [0x49, 0x8B, 0x46, 0x48, 0x48, 0x89, 0x44, 0x24, 0x28, 0x49, 0x8B, 0x46, 0x40, 0x48, 0x89, 0x44,
    0x24, 0x20, 0x49, 0x8B, 0x46, 0x38, 0x48, 0x89, 0x44, 0x24, 0x18, 0x49, 0x8B, 0x46, 0x28, 0x49,
    0x8B, 0x4E, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x08, 0x4C, 0x8D, 0x7C,
    0x24, 0x50, 0x48, 0x8D, 0x74, 0x24, 0x08, 0x4C, 0x89, 0xFF, 0xE8, 0xAE, 0x32, 0xFF, 0xFF]

theorem code_l121643 : ∀ x ∈ codeRange 0x121643 bytes_l121643, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x21643 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l121682 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x121682 (leaR64Effect 0x121682 7 (.sib 4 none 0 (.d32 0xb7))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x121682 (fun s => s.RIP = 0x121682) (leaR64Effect 0x121682 7 (.sib 4 none 0 (.d32 0xb7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12168a (movR64R64Effect 0x12168a 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 56) (.exec 0x12168a (fun s => s.RIP = 0x12168a) (movR64R64Effect 0x12168a 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x12168d (callEffect (fun _ => 0x1148d0) 0x121692) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x12168d (PushPre 0x12168d 5) (callEffect (fun _ => 0x1148d0) 0x121692) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x121692⟩) #v[]
    (.terminate (.call ⟨.l1148d0, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l121692, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l121682 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0xB7, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFE, 0xE8, 0x3E, 0x32, 0xFF, 0xFF]

theorem code_l121682 : ∀ x ∈ codeRange 0x121682 bytes_l121682, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x21682 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l121692 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x121692 (testR32R32Effect 0x121692 2 5 5) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 5] []) (.flag .ZF)) #v[5, 5]
    (.letOp (n := 54) (.exec 0x121692 (fun s => s.RIP = 0x121692) (testR32R32Effect 0x121692 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l121702, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l121696, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l121692 : List UInt8 :=
  [0x85, 0xED, 0x74, 0x6C]

theorem code_l121692 : ∀ x ∈ codeRange 0x121692 bytes_l121692, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x21692 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l121696 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x121696 (leaR64Effect 0x121696 7 (.sib 4 none 0 (.d32 0xb7))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x121696 (fun s => s.RIP = 0x121696) (leaR64Effect 0x121696 7 (.sib 4 none 0 (.d32 0xb7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12169e (movR32Imm32Effect 0x12169e 5 6 0x20) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x12169e (fun s => s.RIP = 0x12169e) (movR32Imm32Effect 0x12169e 5 6 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1216a3 (callEffect (fun _ => 0x125760) 0x1216a8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1216a3 (PushPre 0x1216a3 5) (callEffect (fun _ => 0x125760) 0x1216a8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1216a8⟩) #v[]
    (.terminate (.call ⟨.l125760, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l1216a8, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l121696 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0xB7, 0x00, 0x00, 0x00, 0xBE, 0x20, 0x00, 0x00, 0x00, 0xE8, 0xB8, 0x40,
    0x00, 0x00]

theorem code_l121696 : ∀ x ∈ codeRange 0x121696 bytes_l121696, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x21696 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1216a8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1216a8 (StorePre 0x1216a8 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1216a8 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1216a8 (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x1216b1 (StorePre 0x1216b1 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1216b1 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1216b1 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1216ba (StorePre 0x1216ba 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1216ba + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1216ba (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x1216c3 (StorePre 0x1216c3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1216c3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1216c3 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1216cc (movR64M64Effect 0x1216cc 1 (.sib 4 none 0 (.d32 0x97))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x1216cc (LoadPre 0x1216cc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x97)) s (0x1216cc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1216cc 1 (.sib 4 none 0 (.d32 0x97))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1216d4 (movR64M64Effect 0x1216d4 2 (.sib 4 none 0 (.d32 0x9f))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x1216d4 (LoadPre 0x1216d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x1216d4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1216d4 2 (.sib 4 none 0 (.d32 0x9f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1216dc (StorePre 0x1216dc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1216dc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1216dc 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 62) (.exec 0x1216e1 (StorePre 0x1216e1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1216e1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1216e1 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 63) (.out 0x1216e6 (movR64M64Effect 0x1216e6 1 (.sib 4 none 0 (.d32 0xa7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 64) (.exec 0x1216e6 (LoadPre 0x1216e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa7)) s (0x1216e6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1216e6 1 (.sib 4 none 0 (.d32 0xa7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x1216ee (StorePre 0x1216ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1216ee + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1216ee 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x1216f3 (movR64M64Effect 0x1216f3 1 (.sib 4 none 0 (.d32 0xaf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 67) (.exec 0x1216f3 (LoadPre 0x1216f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaf)) s (0x1216f3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1216f3 1 (.sib 4 none 0 (.d32 0xaf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x1216fb (StorePre 0x1216fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1216fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1216fb 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[66, 4]
    (.terminate (.br ⟨.l12176c, RegMap.args [(0, 0), (1, 66), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l1216a8 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08,
    0x00, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x97, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24,
    0x9F, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x50, 0x48, 0x89, 0x54, 0x24, 0x58, 0x48, 0x8B,
    0x8C, 0x24, 0xA7, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x60, 0x48, 0x8B, 0x8C, 0x24, 0xAF,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x68, 0xEB, 0x6A]

theorem code_l1216a8 : ∀ x ∈ codeRange 0x1216a8 bytes_l1216a8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x216a8 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l121702 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x121702 (movR64M64Effect 0x121702 0 (.sib 4 none 0 (.d32 0x97))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x121702 (LoadPre 0x121702 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x97)) s (0x121702 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x121702 0 (.sib 4 none 0 (.d32 0x97))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12170a (movR64M64Effect 0x12170a 1 (.sib 4 none 0 (.d32 0x9f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x12170a (LoadPre 0x12170a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x12170a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12170a 1 (.sib 4 none 0 (.d32 0x9f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x121712 (StorePre 0x121712 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x121712 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121712 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x121717 (StorePre 0x121717 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x121717 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121717 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x12171c (movR64M64Effect 0x12171c 0 (.sib 4 none 0 (.d32 0xa7))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x12171c (LoadPre 0x12171c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa7)) s (0x12171c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12171c 0 (.sib 4 none 0 (.d32 0xa7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x121724 (StorePre 0x121724 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x121724 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121724 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x121729 (movR64M64Effect 0x121729 0 (.sib 4 none 0 (.d32 0xaf))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x121729 (LoadPre 0x121729 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaf)) s (0x121729 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x121729 0 (.sib 4 none 0 (.d32 0xaf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x121731 (StorePre 0x121731 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x121731 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121731 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x121736 (movR64M64Effect 0x121736 0 (.sib 4 none 0 (.d32 0xb7))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x121736 (LoadPre 0x121736 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb7)) s (0x121736 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x121736 0 (.sib 4 none 0 (.d32 0xb7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x12173e (movR64M64Effect 0x12173e 1 (.sib 4 none 0 (.d32 0xbf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 68) (.exec 0x12173e (LoadPre 0x12173e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbf)) s (0x12173e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12173e 1 (.sib 4 none 0 (.d32 0xbf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x121746 (StorePre 0x121746 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x121746 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121746 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 70) (.exec 0x12174b (StorePre 0x12174b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12174b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12174b 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 71) (.out 0x121750 (movR64M64Effect 0x121750 0 (.sib 4 none 0 (.d32 0xc7))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x121750 (LoadPre 0x121750 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc7)) s (0x121750 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x121750 0 (.sib 4 none 0 (.d32 0xc7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x121758 (StorePre 0x121758 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121758 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121758 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x12175d (movR64M64Effect 0x12175d 0 (.sib 4 none 0 (.d32 0xcf))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 75) (.exec 0x12175d (LoadPre 0x12175d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcf)) s (0x12175d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12175d 0 (.sib 4 none 0 (.d32 0xcf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x121765 (StorePre 0x121765 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x121765 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121765 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x12176a (movR8Imm8Effect 0x12176a 2 0 0x4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 78) (.exec 0x12176a (fun s => s.RIP = 0x12176a) (movR8Imm8Effect 0x12176a 2 0 0x4) (Reg.operands [.gpr 0] [])) #v[74]
    (.terminate (.br ⟨.l12176c, RegMap.args [(0, 77), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩)))))))))))))))))))))))))))

def bytes_l121702 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x97, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x9F, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x44, 0x24, 0x50, 0x48, 0x89, 0x4C, 0x24, 0x58, 0x48, 0x8B, 0x84, 0x24, 0xA7, 0x00,
    0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x84, 0x24, 0xAF, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x44, 0x24, 0x68, 0x48, 0x8B, 0x84, 0x24, 0xB7, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24,
    0xBF, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48, 0x8B,
    0x84, 0x24, 0xC7, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84, 0x24, 0xCF,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20, 0xB0, 0x04]

theorem code_l121702 : ∀ x ∈ codeRange 0x121702 bytes_l121702, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x21702 106 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12176c_1 : Block Op Label signature Reg.count 81 :=
  .letOp (n := 81) (.exec 0x1217f2 (StorePre 0x1217f2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1217f2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1217f2 (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.exec 0x1217fb (StorePre 0x1217fb 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1217fb + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1217fb (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.exec 0x121804 (StorePre 0x121804 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x121804 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x121804 (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.exec 0x12180d (StorePre 0x12180d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12180d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x12180d (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.exec 0x121816 (StorePre 0x121816 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x121816 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x121816 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.exec 0x12181f (StorePre 0x12181f 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12181f + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x12181f (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x121828 (movR32M32Effect 0x121828 7 (.base 14 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 88) (.exec 0x121828 (LoadPre 0x121828 (fun s => AddrMode.addr (.base 14 (.d8 0x50)) s (0x121828 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x121828 7 (.base 14 (.d8 0x50))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 89) (.out 0x12182c (callEffect (fun _ => 0x127d50) 0x121831) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 90) (.exec 0x12182c (PushPre 0x12182c 5) (callEffect (fun _ => 0x127d50) 0x121831) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.const ⟨64, 0x121831⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 75), (1, 68), (2, 2), (3, 3), (4, 89), (5, 5), (6, 6), (7, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 92⟩ { target := .l121831, kept := #v[], arity := rfl, guard := some (Fin.last 91) }))))))))))))

def bytes_l12176c_1 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x41, 0x8B, 0x7E, 0x50, 0xE8, 0x1F, 0x65, 0x00, 0x00]

theorem code_l12176c_1 : ∀ x ∈ codeRange 0x1217f2 bytes_l12176c_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x217f2 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12176c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12176c (StorePre 0x12176c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd7)) s (0x12176c + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x12176c 7 0 (.sib 4 none 0 (.d32 0xd7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.out 0x121773 (movR64M64Effect 0x121773 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 55) (.exec 0x121773 (LoadPre 0x121773 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x121773 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121773 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x121778 (movR64M64Effect 0x121778 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x121778 (LoadPre 0x121778 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x121778 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121778 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x12177d (StorePre 0x12177d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x12177d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12177d 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 59) (.exec 0x121785 (StorePre 0x121785 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x121785 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x121785 1 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 60) (.out 0x12178d (movR64M64Effect 0x12178d 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 61) (.exec 0x12178d (LoadPre 0x12178d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12178d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12178d 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x121792 (StorePre 0x121792 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x121792 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x121792 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x12179a (movR64M64Effect 0x12179a 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x12179a (LoadPre 0x12179a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x12179a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12179a 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x12179f (StorePre 0x12179f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x12179f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12179f 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x1217a7 (movR64M64Effect 0x1217a7 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 67) (.exec 0x1217a7 (LoadPre 0x1217a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1217a7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1217a7 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x1217ac (movR64M64Effect 0x1217ac 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 69) (.exec 0x1217ac (LoadPre 0x1217ac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1217ac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1217ac 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x1217b1 (StorePre 0x1217b1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1217b1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1217b1 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 71) (.exec 0x1217b9 (StorePre 0x1217b9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1217b9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1217b9 1 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 72) (.out 0x1217c1 (movR64M64Effect 0x1217c1 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 73) (.exec 0x1217c1 (LoadPre 0x1217c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1217c1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1217c1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x1217c6 (StorePre 0x1217c6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1217c6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1217c6 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x1217ce (movR64M64Effect 0x1217ce 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 76) (.exec 0x1217ce (LoadPre 0x1217ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1217ce + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1217ce 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.exec 0x1217d3 (StorePre 0x1217d3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1217d3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1217d3 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.exec 0x1217db (StorePre 0x1217db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1217db + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1217db (.sib 4 none 0 (.d8 0x48)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x1217e0 (StorePre 0x1217e0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1217e0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1217e0 (.sib 4 none 0 (.d8 0x40)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.exec 0x1217e9 (StorePre 0x1217e9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1217e9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1217e9 (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l12176c_1))))))))))))))))))))))))))))

def bytes_l12176c : List UInt8 :=
  [0x88, 0x84, 0x24, 0xD7, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0x8B, 0x4C, 0x24,
    0x58, 0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x44, 0x24, 0x60, 0x48, 0x89, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x8B,
    0x44, 0x24, 0x68, 0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x08,
    0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8C,
    0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0x08, 0x01,
    0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0xC6,
    0x44, 0x24, 0x48, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x38, 0x00, 0x00, 0x00, 0x00] ++ bytes_l12176c_1

theorem code_l12176c : ∀ x ∈ codeRange 0x12176c bytes_l12176c, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2176c 134 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12176c_1

@[cfg_block] def b_l121831 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x121831 (StorePre 0x121831 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x121831 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x121831 (.sib 4 none 0 (.d32 0x90)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x121839 (StorePre 0x121839 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x121839 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x121839 (.sib 4 none 0 (.d32 0x88)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x121845 (StorePre 0x121845 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x121845 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x121845 (.sib 4 none 0 (.d32 0x80)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x121851 (StorePre 0x121851 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x121851 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x121851 (.sib 4 none 0 (.d8 0x78)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x12185a (StorePre 0x12185a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x12185a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x12185a (.sib 4 none 0 (.d8 0x70)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x121863 (StorePre 0x121863 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x121863 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x121863 (.sib 4 none 0 (.d8 0x68)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x12186c (StorePre 0x12186c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12186c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x12186c (.sib 4 none 0 (.d8 0x60)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x121875 (StorePre 0x121875 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x121875 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x121875 (.sib 4 none 0 (.d8 0x58)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x12187e (StorePre 0x12187e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x12187e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x12187e (.sib 4 none 0 (.d8 0x50)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x121887 (xorR32R32Effect 0x121887 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 63) (.exec 0x121887 (fun s => s.RIP = 0x121887) (xorR32R32Effect 0x121887 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 64) (.exec 0x121889 (fun s => s.RIP = 0x121889) (leaR64Effect 0x121889 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x12188e (fun s => s.RIP = 0x12188e) (fun _ => nopEffect 0x12188e 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l121890, RegMap.args [(0, 0), (2, 62), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l121831 : List UInt8 :=
  [0xC6, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x70, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x68, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x60,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x58, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x50, 0x00, 0x00, 0x00, 0x00, 0x31, 0xD2, 0x48, 0x8D, 0x4C, 0x24, 0x07, 0x66, 0x90]

theorem code_l121831 : ∀ x ∈ codeRange 0x121831 bytes_l121831, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x21831 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l121890 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x121890 (movzxR32M8Effect 0x121890 8 6 (.sib 4 (some 2) 0 (.d32 0xd7))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4, .gpr 2] []) (.reg (.gpr 6))) #v[4, 2]
    (.letOp (n := 54) (.exec 0x121890 (LoadPre 0x121890 (fun s => AddrMode.addr (.sib 4 (some 2) 0 (.d32 0xd7)) s (0x121890 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x121890 8 6 (.sib 4 (some 2) 0 (.d32 0xd7))) (Reg.operands [.gpr 4, .gpr 2] [])) #v[4, 2]
    (.letOp (n := 55) (.exec 0x121898 (StorePre 0x121898 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x121898 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x121898 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 56) (.out 0x12189c (movzxR32M8Effect 0x12189c 5 7 (.sib 4 (some 2) 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 2] []) (.reg (.gpr 7))) #v[4, 2]
    (.letOp (n := 57) (.exec 0x12189c (LoadPre 0x12189c (fun s => AddrMode.addr (.sib 4 (some 2) 0 (.d8 0x8)) s (0x12189c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12189c 5 7 (.sib 4 (some 2) 0 (.d8 0x8))) (Reg.operands [.gpr 4, .gpr 2] [])) #v[4, 2]
    (.letOp (n := 58) (.out 0x1218a1 (movzxR32M8Effect 0x1218a1 6 8 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 59) (.exec 0x1218a1 (LoadPre 0x1218a1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1218a1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1218a1 6 8 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x1218a7 (testR8R8Effect 0x1218a7 3 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[58, 58]
    (.letOp (n := 61) (.exec 0x1218a7 (fun s => s.RIP = 0x1218a7) (testR8R8Effect 0x1218a7 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[58, 58]
    (.letOp (n := 62) (.out 0x1218aa (atFlags (condHolds 5) (cmovR32R32Effect 0x1218aa 3 6 7)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[53, 56, 60]
    (.letOp (n := 63) (.exec 0x1218aa (fun s => s.RIP = 0x1218aa) (atFlags (condHolds 5) (cmovR32R32Effect 0x1218aa 3 6 7)) (Reg.operands [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[53, 56, 60]
    (.letOp (n := 64) (.exec 0x1218ad (StorePre 0x1218ad 5 (fun s => AddrMode.addr (.sib 4 (some 2) 0 (.d8 0x50)) s (0x1218ad + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1218ad 5 6 (.sib 4 (some 2) 0 (.d8 0x50))) (Reg.operands [.gpr 6, .gpr 4, .gpr 2] [])) #v[62, 4, 2]
    (.letOp (n := 65) (.out 0x1218b2 (incR64Effect 0x1218b2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 66) (.exec 0x1218b2 (fun s => s.RIP = 0x1218b2) (incR64Effect 0x1218b2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2]
    (.letOp (n := 67) (.out 0x1218b5 (cmpR64Imm8Effect 0x1218b5 2 0x41) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[65]
    (.letOp (n := 68) (.exec 0x1218b5 (fun s => s.RIP = 0x1218b5) (cmpR64Imm8Effect 0x1218b5 2 0x41) (Reg.operands [.gpr 2] [])) #v[65]
    (.letOp (n := 69) (.pure (condOp 5)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l121890, RegMap.args [(0, 0), (2, 65), (3, 3), (4, 4), (5, 5), (6, 62), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l1218bb, RegMap.args [(0, 0), (2, 65), (3, 3), (4, 4), (5, 5), (6, 62), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l121890 : List UInt8 :=
  [0x0F, 0xB6, 0xB4, 0x14, 0xD7, 0x00, 0x00, 0x00, 0x88, 0x44, 0x24, 0x07, 0x0F, 0xB6, 0x7C, 0x14,
    0x08, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x07, 0x45, 0x84, 0xC0, 0x0F, 0x45, 0xF7, 0x40, 0x88, 0x74,
    0x14, 0x50, 0x48, 0xFF, 0xC2, 0x48, 0x83, 0xFA, 0x41, 0x75, 0xD5]

theorem code_l121890 : ∀ x ∈ codeRange 0x121890 bytes_l121890, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x21890 43 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1218bb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1218bb (leaR64Effect 0x1218bb 6 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x1218bb (fun s => s.RIP = 0x1218bb) (leaR64Effect 0x1218bb 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1218c0 (movR32Imm32Effect 0x1218c0 5 2 0x41) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x1218c0 (fun s => s.RIP = 0x1218c0) (movR32Imm32Effect 0x1218c0 5 2 0x41) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1218c5 (movR64R64Effect 0x1218c5 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 58) (.exec 0x1218c5 (fun s => s.RIP = 0x1218c5) (movR64R64Effect 0x1218c5 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x1218c8 (callEffect (callMemPtr 0x1218c8 (.rip 0xe2502)) (0x1218c8 + BitVec.ofNat 64 (callMemLen (.rip 0xe2502)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1218c8 (GoesTo (CallMemPre 0x1218c8 (.rip 0xe2502)) (callEffect (callMemPtr 0x1218c8 (.rip 0xe2502)) (0x1218c8 + BitVec.ofNat 64 (callMemLen (.rip 0xe2502)))) 0x12a820) (callEffect (callMemPtr 0x1218c8 (.rip 0xe2502)) (0x1218c8 + BitVec.ofNat 64 (callMemLen (.rip 0xe2502)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1218ce⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 3), (4, 59), (5, 5), (6, 53), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1218ce, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1218bb : List UInt8 :=
  [0x48, 0x8D, 0x74, 0x24, 0x50, 0xBA, 0x41, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDF, 0xFF, 0x15, 0x02,
    0x25, 0x0E, 0x00]

theorem code_l1218bb : ∀ x ∈ codeRange 0x1218bb bytes_l1218bb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x218bb 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1218ce : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1218ce (movR64R64Effect 0x1218ce 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x1218ce (fun s => s.RIP = 0x1218ce) (movR64R64Effect 0x1218ce 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1218d1 (addR64Imm32Effect 0x1218d1 4 0x118) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x1218d1 (fun s => s.RIP = 0x1218d1) (addR64Imm32Effect 0x1218d1 4 0x118) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1218d8 (popR64Effect 0x1218d8 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x1218d8 (popR64Effect 0x1218d8 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x1218d8 (PopPre 0x1218d8) (popR64Effect 0x1218d8 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x1218d9 (popR64Effect 0x1218d9 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 61) (.out 0x1218d9 (popR64Effect 0x1218d9 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x1218d9 (PopPre 0x1218d9) (popR64Effect 0x1218d9 2 14) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x1218db (popR64Effect 0x1218db 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[61]
    (.letOp (n := 64) (.out 0x1218db (popR64Effect 0x1218db 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x1218db (PopPre 0x1218db) (popR64Effect 0x1218db 2 15) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x1218dd (popR64Effect 0x1218dd 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[64]
    (.letOp (n := 67) (.out 0x1218dd (popR64Effect 0x1218dd 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x1218dd (PopPre 0x1218dd) (popR64Effect 0x1218dd 1 5) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x1218de (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[67]
    (.letOp (n := 70) (.out 0x1218de (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x1218de (RetPre 0x1218de) (retEffect) (Reg.operands [.gpr 4] [])) #v[67]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (5, 66), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 72) (some ⟨69, by decide⟩)))))))))))))))))))))

def bytes_l1218ce : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0x18, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5E, 0x41, 0x5F, 0x5D,
    0xC3]

theorem code_l1218ce : ∀ x ∈ codeRange 0x1218ce bytes_l1218ce, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x218ce 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124290 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124290 (pushR64Effect 0x124290 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x124290 (PushPre 0x124290 1) (pushR64Effect 0x124290 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x124291 (pushR64Effect 0x124291 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x124291 (PushPre 0x124291 2) (pushR64Effect 0x124291 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x124293 (pushR64Effect 0x124293 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[55, 3]
    (.letOp (n := 58) (.exec 0x124293 (PushPre 0x124293 1) (pushR64Effect 0x124293 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 59) (.out 0x124294 (subR64Imm8Effect 0x124294 4 0x60) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x124294 (fun s => s.RIP = 0x124294) (subR64Imm8Effect 0x124294 4 0x60) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x124298 (movR64R64Effect 0x124298 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 62) (.exec 0x124298 (fun s => s.RIP = 0x124298) (movR64R64Effect 0x124298 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 63) (.out 0x12429b (movR32M32LowEffect 0x12429b 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 64) (.exec 0x12429b (LoadPre 0x12429b (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x12429b + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x12429b 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x12429e (cmpR32M32Effect 0x12429e 3 0 (.base 6 (.d8 0x1c))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[63, 6]
    (.letOp (n := 66) (.out 0x12429e (cmpR32M32Effect 0x12429e 3 0 (.base 6 (.d8 0x1c))) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 6] []) (.flag .ZF)) #v[63, 6]
    (.letOp (n := 67) (.exec 0x12429e (LoadPre 0x12429e (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x12429e + BitVec.ofNat 64 3)) 4) (cmpR32M32Effect 0x12429e 3 0 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[63, 6]
    (.letOp (n := 68) (.pure (condOp 6)) #v[65, 66]
    (.terminate (.condBr (Fin.last 68) ⟨.l124322, RegMap.args [(0, 63), (1, 1), (2, 2), (3, 61), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 65), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ ⟨.l1242a3, RegMap.args [(0, 63), (1, 1), (2, 2), (3, 61), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 65), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l124290 : List UInt8 :=
  [0x55, 0x41, 0x56, 0x53, 0x48, 0x83, 0xEC, 0x60, 0x48, 0x89, 0xFB, 0x8B, 0x46, 0x18, 0x3B, 0x46,
    0x1C, 0x76, 0x7F]

theorem code_l124290 : ∀ x ∈ codeRange 0x124290 bytes_l124290, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24290 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1242a3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1242a3 (movR32R32Effect 0x1242a3 2 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 54) (.exec 0x1242a3 (fun s => s.RIP = 0x1242a3) (movR32R32Effect 0x1242a3 2 5 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x1242a5 (movR32R32Effect 0x1242a5 3 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[1]
    (.letOp (n := 56) (.exec 0x1242a5 (fun s => s.RIP = 0x1242a5) (movR32R32Effect 0x1242a5 3 14 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x1242a8 (movR64M64Effect 0x1242a8 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 58) (.exec 0x1242a8 (LoadPre 0x1242a8 (fun s => AddrMode.addr (.base 6 .none) s (0x1242a8 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1242a8 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x1242ab (movR64M64Effect 0x1242ab 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 60) (.exec 0x1242ab (LoadPre 0x1242ab (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1242ab + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1242ab 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x1242af (movzxR32M8Effect 0x1242af 4 2 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 62) (.exec 0x1242af (LoadPre 0x1242af (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1242af + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1242af 4 2 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.out 0x1242b3 (movR64M64Effect 0x1242b3 7 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 64) (.exec 0x1242b3 (LoadPre 0x1242b3 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1242b3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1242b3 7 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.exec 0x1242b7 (StorePre 0x1242b7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1242b7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242b7 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x1242bc (movR64M64Effect 0x1242bc 6 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 67) (.exec 0x1242bc (LoadPre 0x1242bc (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1242bc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1242bc 6 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 68) (.exec 0x1242c0 (StorePre 0x1242c0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1242c0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242c0 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.exec 0x1242c5 (StorePre 0x1242c5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1242c5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242c5 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 70) (.exec 0x1242ca (StorePre 0x1242ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1242ca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242ca 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 71) (.exec 0x1242cf (StorePre 0x1242cf 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1242cf + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1242cf 4 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 72) (.out 0x1242d3 (movR64R64Effect 0x1242d3 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 73) (.exec 0x1242d3 (fun s => s.RIP = 0x1242d3) (movR64R64Effect 0x1242d3 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x1242d6 (leaR64Effect 0x1242d6 6 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 75) (.exec 0x1242d6 (fun s => s.RIP = 0x1242d6) (leaR64Effect 0x1242d6 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.out 0x1242db (callEffect (fun _ => 0x124430) 0x1242e0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 77) (.exec 0x1242db (PushPre 0x1242db 5) (callEffect (fun _ => 0x124430) 0x1242e0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.const ⟨64, 0x1242e0⟩) #v[]
    (.terminate (.call ⟨.l124430, RegMap.args [(0, 57), (1, 59), (2, 61), (3, 3), (4, 76), (5, 53), (6, 74), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩ { target := .l1242e0, kept := #v[], arity := rfl, guard := some (Fin.last 78) })))))))))))))))))))))))))))

def bytes_l1242a3 : List UInt8 :=
  [0x89, 0xD5, 0x41, 0x89, 0xCE, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x0F, 0xB6, 0x56, 0x20,
    0x48, 0x8B, 0x7E, 0x18, 0x48, 0x89, 0x7C, 0x24, 0x50, 0x48, 0x8B, 0x76, 0x10, 0x48, 0x89, 0x74,
    0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0x89, 0x4C, 0x24, 0x40, 0x88, 0x54, 0x24, 0x58,
    0x48, 0x89, 0xE7, 0x48, 0x8D, 0x74, 0x24, 0x38, 0xE8, 0x50, 0x01, 0x00, 0x00]

theorem code_l1242a3 : ∀ x ∈ codeRange 0x1242a3 bytes_l1242a3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x242a3 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1242e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1242e0 (movR32M32LowEffect 0x1242e0 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1242e0 (LoadPre 0x1242e0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1242e0 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1242e0 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1242e3 (movR64M64Effect 0x1242e3 0 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1242e3 (LoadPre 0x1242e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1242e3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1242e3 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1242e8 (cmpR32Imm8Effect 0x1242e8 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x1242e8 (fun s => s.RIP = 0x1242e8) (cmpR32Imm8Effect 0x1242e8 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l12432b, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1242ed, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1242e0 : List UInt8 :=
  [0x8B, 0x0C, 0x24, 0x48, 0x8B, 0x44, 0x24, 0x04, 0x83, 0xF9, 0x02, 0x75, 0x3E]

theorem code_l1242e0 : ∀ x ∈ codeRange 0x1242e0 bytes_l1242e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x242e0 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1242ed : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1242ed (leaR32Effect 0x1242ed 3 2 (.base 0 (.d8 0xea))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[0]
    (.letOp (n := 54) (.exec 0x1242ed (fun s => s.RIP = 0x1242ed) (leaR32Effect 0x1242ed 3 2 (.base 0 (.d8 0xea))) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x1242f0 (movR32R32Effect 0x1242f0 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x1242f0 (fun s => s.RIP = 0x1242f0) (movR32R32Effect 0x1242f0 2 6 2) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.out 0x1242f2 (shlR8Effect 0x1242f2 4 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 58) (.exec 0x1242f2 (fun s => s.RIP = 0x1242f2) (shlR8Effect 0x1242f2 4 6 6) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x1242f6 (addR8Imm8Effect 0x1242f6 4 6 0x40) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[57]
    (.letOp (n := 60) (.exec 0x1242f6 (fun s => s.RIP = 0x1242f6) (addR8Imm8Effect 0x1242f6 4 6 0x40) (Reg.operands [.gpr 6] [])) #v[57]
    (.letOp (n := 61) (.out 0x1242fa (xorR32R32Effect 0x1242fa 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 62) (.exec 0x1242fa (fun s => s.RIP = 0x1242fa) (xorR32R32Effect 0x1242fa 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 63) (.out 0x1242fc (cmpR8Imm8Effect 0x1242fc 3 2 0x3) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[53]
    (.letOp (n := 64) (.exec 0x1242fc (fun s => s.RIP = 0x1242fc) (cmpR8Imm8Effect 0x1242fc 3 2 0x3) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 65) (.out 0x1242ff (movzxR32R8Effect 0x1242ff 4 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 66) (.exec 0x1242ff (fun s => s.RIP = 0x1242ff) (movzxR32R8Effect 0x1242ff 4 2 6) (Reg.operands [.gpr 6] [])) #v[59]
    (.letOp (n := 67) (.out 0x124303 (atFlags (condHolds 3) (cmovR32R32Effect 0x124303 3 2 1)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[65, 61, 63]
    (.letOp (n := 68) (.exec 0x124303 (fun s => s.RIP = 0x124303) (atFlags (condHolds 3) (cmovR32R32Effect 0x124303 3 2 1)) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[65, 61, 63]
    (.letOp (n := 69) (.out 0x124306 (cmpR8R8Effect 0x124306 3 2 5) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 5] []) (.flag .ZF)) #v[67, 5]
    (.letOp (n := 70) (.exec 0x124306 (fun s => s.RIP = 0x124306) (cmpR8R8Effect 0x124306 3 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[67, 5]
    (.letOp (n := 71) (.pure (condOp 5)) #v[69]
    (.terminate (.condBr (Fin.last 71) ⟨.l124411, RegMap.args [(0, 0), (1, 61), (2, 67), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ ⟨.l12430f, RegMap.args [(0, 0), (1, 61), (2, 67), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l1242ed : List UInt8 :=
  [0x8D, 0x50, 0xEA, 0x89, 0xD6, 0x40, 0xC0, 0xE6, 0x06, 0x40, 0x80, 0xC6, 0x40, 0x31, 0xC9, 0x80,
    0xFA, 0x03, 0x40, 0x0F, 0xB6, 0xD6, 0x0F, 0x43, 0xD1, 0x40, 0x38, 0xEA, 0x0F, 0x85, 0x02, 0x01,
    0x00, 0x00]

theorem code_l1242ed : ∀ x ∈ codeRange 0x1242ed bytes_l1242ed, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x242ed 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12430f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12430f (fun s => s.RIP = 0x12430f) (movzxR32R8Effect 0x12430f 3 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (cutBlock 0x124312)

def bytes_l12430f : List UInt8 :=
  [0x0F, 0xB6, 0xC8, 0xFF, 0x24, 0xCD, 0x60, 0x34, 0x20, 0x00]

theorem code_l12430f : ∀ x ∈ codeRange 0x12430f bytes_l12430f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2430f 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124322 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124322 (StorePre 0x124322 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124322 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124322 (.base 3 (.d8 0x4)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l124414, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l124322 : List UInt8 :=
  [0xC6, 0x43, 0x04, 0x00, 0xE9, 0xE9, 0x00, 0x00, 0x00]

theorem code_l124322 : ∀ x ∈ codeRange 0x124322 bytes_l124322, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24322 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12432b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12432b (movR32M32LowEffect 0x12432b 2 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x12432b (LoadPre 0x12432b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x12432b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12432b 2 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x12432f (StorePre 0x12432f 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x12432f + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12432f 2 (.base 3 (.d8 0x34))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x124332 (movR64M64Effect 0x124332 2 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 57) (.exec 0x124332 (LoadPre 0x124332 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x124332 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124332 2 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x124337 (StorePre 0x124337 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x124337 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124337 2 (.base 3 (.d8 0x2c))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x12433b (movR64M64Effect 0x12433b 2 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x12433b (LoadPre 0x12433b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x12433b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12433b 2 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x124340 (StorePre 0x124340 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x124340 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124340 2 (.base 3 (.d8 0x24))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x124344 (movR64M64Effect 0x124344 2 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 63) (.exec 0x124344 (LoadPre 0x124344 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x124344 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124344 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x124349 (StorePre 0x124349 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x124349 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124349 2 (.base 3 (.d8 0x1c))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 65) (.out 0x12434d (movR64M64Effect 0x12434d 2 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 66) (.exec 0x12434d (LoadPre 0x12434d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x12434d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12434d 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x124352 (movR64M64Effect 0x124352 6 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x124352 (LoadPre 0x124352 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124352 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124352 6 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x124357 (StorePre 0x124357 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x124357 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124357 6 (.base 3 (.d8 0x14))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[67, 3]
    (.letOp (n := 70) (.exec 0x12435b (StorePre 0x12435b 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x12435b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12435b 2 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 71) (.exec 0x12435f (StorePre 0x12435f 2 (fun s => AddrMode.addr (.base 3 .none) s (0x12435f + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x12435f 1 (.base 3 .none)) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 72) (.exec 0x124361 (StorePre 0x124361 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124361 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124361 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.terminate (.br ⟨.l12441a, RegMap.args [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l12432b : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x34, 0x89, 0x53, 0x34, 0x48, 0x8B, 0x54, 0x24, 0x2C, 0x48, 0x89, 0x53, 0x2C,
    0x48, 0x8B, 0x54, 0x24, 0x24, 0x48, 0x89, 0x53, 0x24, 0x48, 0x8B, 0x54, 0x24, 0x1C, 0x48, 0x89,
    0x53, 0x1C, 0x48, 0x8B, 0x54, 0x24, 0x0C, 0x48, 0x8B, 0x74, 0x24, 0x14, 0x48, 0x89, 0x73, 0x14,
    0x48, 0x89, 0x53, 0x0C, 0x89, 0x0B, 0x48, 0x89, 0x43, 0x04, 0xE9, 0xB0, 0x00, 0x00, 0x00]

theorem code_l12432b : ∀ x ∈ codeRange 0x12432b bytes_l12432b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2432b 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124411 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124411 (StorePre 0x124411 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124411 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x124411 3 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.terminate (.br ⟨.l124414, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l124411 : List UInt8 :=
  [0x88, 0x4B, 0x04]

theorem code_l124411 : ∀ x ∈ codeRange 0x124411 bytes_l124411, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24411 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124414 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124414 (StorePre 0x124414 6 (fun s => AddrMode.addr (.base 3 .none) s (0x124414 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124414 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l12441a, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l124414 : List UInt8 :=
  [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00]

theorem code_l124414 : ∀ x ∈ codeRange 0x124414 bytes_l124414, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24414 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12441a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12441a (movR64R64Effect 0x12441a 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x12441a (fun s => s.RIP = 0x12441a) (movR64R64Effect 0x12441a 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x12441d (addR64Imm8Effect 0x12441d 4 0x60) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x12441d (fun s => s.RIP = 0x12441d) (addR64Imm8Effect 0x12441d 4 0x60) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124421 (popR64Effect 0x124421 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x124421 (popR64Effect 0x124421 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x124421 (PopPre 0x124421) (popR64Effect 0x124421 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x124422 (popR64Effect 0x124422 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 61) (.out 0x124422 (popR64Effect 0x124422 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x124422 (PopPre 0x124422) (popR64Effect 0x124422 2 14) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x124424 (popR64Effect 0x124424 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[61]
    (.letOp (n := 64) (.out 0x124424 (popR64Effect 0x124424 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x124424 (PopPre 0x124424) (popR64Effect 0x124424 1 5) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x124425 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[64]
    (.letOp (n := 67) (.out 0x124425 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x124425 (RetPre 0x124425) (retEffect) (Reg.operands [.gpr 4] [])) #v[64]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69) (some ⟨66, by decide⟩))))))))))))))))))

def bytes_l12441a : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x60, 0x5B, 0x41, 0x5E, 0x5D, 0xC3]

theorem code_l12441a : ∀ x ∈ codeRange 0x12441a bytes_l12441a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2441a 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124430 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124430 (pushR64Effect 0x124430 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x124430 (PushPre 0x124430 1) (pushR64Effect 0x124430 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x124431 (pushR64Effect 0x124431 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x124431 (PushPre 0x124431 2) (pushR64Effect 0x124431 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x124433 (pushR64Effect 0x124433 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[55, 3]
    (.letOp (n := 58) (.exec 0x124433 (PushPre 0x124433 1) (pushR64Effect 0x124433 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 59) (.out 0x124434 (subR64Imm8Effect 0x124434 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x124434 (fun s => s.RIP = 0x124434) (subR64Imm8Effect 0x124434 4 0x40) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x124438 (movR64R64Effect 0x124438 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 62) (.exec 0x124438 (fun s => s.RIP = 0x124438) (movR64R64Effect 0x124438 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.out 0x12443b (movR64R64Effect 0x12443b 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 64) (.exec 0x12443b (fun s => s.RIP = 0x12443b) (movR64R64Effect 0x12443b 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 65) (.out 0x12443e (leaR64Effect 0x12443e 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 66) (.exec 0x12443e (fun s => s.RIP = 0x12443e) (leaR64Effect 0x12443e 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 67) (.out 0x124443 (movR32Imm32Effect 0x124443 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 68) (.exec 0x124443 (fun s => s.RIP = 0x124443) (movR32Imm32Effect 0x124443 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x124448 (callEffect (fun _ => 0x127b80) 0x12444d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 70) (.exec 0x124448 (PushPre 0x124448 5) (callEffect (fun _ => 0x127b80) 0x12444d) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 71) (.const ⟨64, 0x12444d⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 67), (3, 63), (4, 69), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l12444d, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l124430 : List UInt8 :=
  [0x55, 0x41, 0x56, 0x53, 0x48, 0x83, 0xEC, 0x40, 0x49, 0x89, 0xF6, 0x48, 0x89, 0xFB, 0x48, 0x8D,
    0x7C, 0x24, 0x08, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0x33, 0x37, 0x00, 0x00]

theorem code_l124430 : ∀ x ∈ codeRange 0x124430 bytes_l124430, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24430 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12444d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12444d (movR32M32LowEffect 0x12444d 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x12444d (LoadPre 0x12444d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12444d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12444d 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124451 (cmpR32Imm8Effect 0x124451 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124451 (fun s => s.RIP = 0x124451) (cmpR32Imm8Effect 0x124451 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124488, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124456, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12444d : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x83, 0xF8, 0x02, 0x75, 0x32]

theorem code_l12444d : ∀ x ∈ codeRange 0x12444d bytes_l12444d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2444d 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124456 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124456 (movR64M64Effect 0x124456 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x124456 (LoadPre 0x124456 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124456 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124456 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12445b (cmpR64Imm8Effect 0x12445b 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x12445b (fun s => s.RIP = 0x12445b) (cmpR64Imm8Effect 0x12445b 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l12465d, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124465, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124456 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0xF8, 0x01, 0x00, 0x00]

theorem code_l124456 : ∀ x ∈ codeRange 0x124456 bytes_l124456, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24456 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124465 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124465 (movR64M64Effect 0x124465 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124465 (LoadPre 0x124465 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124465 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124465 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12446a (movzxR32M8Effect 0x12446a 3 5 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x12446a (LoadPre 0x12446a (fun s => AddrMode.addr (.base 0 .none) s (0x12446a + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x12446a 3 5 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x12446d (movR32R32Effect 0x12446d 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x12446d (fun s => s.RIP = 0x12446d) (movR32R32Effect 0x12446d 2 0 5) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 59) (.out 0x12446f (decR32Effect 0x12446f 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 60) (.exec 0x12446f (fun s => s.RIP = 0x12446f) (decR32Effect 0x12446f 2 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x124471 (cmpR32Imm8Effect 0x124471 3 0 0x30) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 62) (.out 0x124471 (cmpR32Imm8Effect 0x124471 3 0 0x30) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[59]
    (.letOp (n := 63) (.exec 0x124471 (fun s => s.RIP = 0x124471) (cmpR32Imm8Effect 0x124471 3 0 0x30) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.pure (condOp 7)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l124518, RegMap.args [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l12447a, RegMap.args [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l124465 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x0F, 0xB6, 0x28, 0x89, 0xE8, 0xFF, 0xC8, 0x83, 0xF8, 0x30, 0x0F,
    0x87, 0x9E, 0x00, 0x00, 0x00]

theorem code_l124465 : ∀ x ∈ codeRange 0x124465 bytes_l124465, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24465 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12447a : Block Op Label signature Reg.count 53 :=
  cutBlock 0x12447a

def bytes_l12447a : List UInt8 :=
  [0xFF, 0x24, 0xC5, 0x28, 0x35, 0x20, 0x00]

theorem code_l12447a : ∀ x ∈ codeRange 0x12447a bytes_l12447a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2447a 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124488 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124488 (movR32M32LowEffect 0x124488 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x124488 (LoadPre 0x124488 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124488 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124488 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12448c (movR64M64Effect 0x12448c 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x12448c (LoadPre 0x12448c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12448c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12448c 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124491 (movR64M64Effect 0x124491 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x124491 (LoadPre 0x124491 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124491 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124491 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x124496 (movR64M64Effect 0x124496 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x124496 (LoadPre 0x124496 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124496 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124496 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x12449b (StorePre 0x12449b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x12449b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12449b 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x12449f (movR64M64Effect 0x12449f 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x12449f (LoadPre 0x12449f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x12449f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12449f 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1244a4 (StorePre 0x1244a4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1244a4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1244a4 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 65) (.out 0x1244a8 (movR64M64Effect 0x1244a8 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x1244a8 (LoadPre 0x1244a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1244a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1244a8 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x1244ad (StorePre 0x1244ad 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1244ad + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1244ad 7 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.out 0x1244b1 (movR64M64Effect 0x1244b1 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x1244b1 (LoadPre 0x1244b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1244b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1244b1 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x1244b6 (StorePre 0x1244b6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1244b6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1244b6 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 71) (.exec 0x1244ba (StorePre 0x1244ba 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1244ba + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1244ba 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 72) (.exec 0x1244bc (StorePre 0x1244bc 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1244bc + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1244bc 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 73) (.exec 0x1244bf (StorePre 0x1244bf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1244bf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1244bf 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 74) (.exec 0x1244c3 (StorePre 0x1244c3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1244c3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1244c3 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[57, 3]
    (.terminate (.br ⟨.l12456a, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l124488 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x0C, 0x48, 0x8B, 0x54, 0x24, 0x10, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x8B,
    0x7C, 0x24, 0x38, 0x48, 0x89, 0x7B, 0x30, 0x48, 0x8B, 0x7C, 0x24, 0x30, 0x48, 0x89, 0x7B, 0x28,
    0x48, 0x8B, 0x7C, 0x24, 0x28, 0x48, 0x89, 0x7B, 0x20, 0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0x89,
    0x7B, 0x18, 0x89, 0x03, 0x89, 0x4B, 0x04, 0x48, 0x89, 0x53, 0x08, 0x48, 0x89, 0x73, 0x10, 0xE9,
    0x9E, 0x00, 0x00, 0x00]

theorem code_l124488 : ∀ x ∈ codeRange 0x124488 bytes_l124488, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24488 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124518 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124518 (cmpR8Imm8Effect 0x124518 4 5 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 5] []) (.flag .ZF)) #v[5]
    (.letOp (n := 54) (.out 0x124518 (cmpR8Imm8Effect 0x124518 4 5 0x3f) (EffectPart.reads (.flag .SF) [.gpr 5] []) (.flag .SF)) #v[5]
    (.letOp (n := 55) (.out 0x124518 (cmpR8Imm8Effect 0x124518 4 5 0x3f) (EffectPart.reads (.flag .OF) [.gpr 5] []) (.flag .OF)) #v[5]
    (.letOp (n := 56) (.exec 0x124518 (fun s => s.RIP = 0x124518) (cmpR8Imm8Effect 0x124518 4 5 0x3f) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.pure (condOp 14)) #v[53, 54, 55]
    (.terminate (.condBr (Fin.last 57) ⟨.l12458b, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l12451e, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124518 : List UInt8 :=
  [0x40, 0x80, 0xFD, 0x3F, 0x7E, 0x6D]

theorem code_l124518 : ∀ x ∈ codeRange 0x124518 bytes_l124518, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24518 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12451e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12451e (movzxR32R8Effect 0x12451e 4 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 54) (.exec 0x12451e (fun s => s.RIP = 0x12451e) (movzxR32R8Effect 0x12451e 4 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x124522 (leaR64Effect 0x124522 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x124522 (fun s => s.RIP = 0x124522) (leaR64Effect 0x124522 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124527 (movR64R64Effect 0x124527 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x124527 (fun s => s.RIP = 0x124527) (movR64R64Effect 0x124527 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x12452a (callEffect (fun _ => 0x124670) 0x12452f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x12452a (PushPre 0x12452a 5) (callEffect (fun _ => 0x124670) 0x12452f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x12452f⟩) #v[]
    (.terminate (.call ⟨.l124670, RegMap.args [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l12452f, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l12451e : List UInt8 :=
  [0x40, 0x0F, 0xB6, 0xF5, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF2, 0xE8, 0x41, 0x01, 0x00,
    0x00]

theorem code_l12451e : ∀ x ∈ codeRange 0x12451e bytes_l12451e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2451e 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12452f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12452f (movR32M32LowEffect 0x12452f 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x12452f (LoadPre 0x12452f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12452f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12452f 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124533 (movzxR32M8Effect 0x124533 5 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x124533 (LoadPre 0x124533 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124533 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x124533 5 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124538 (cmpR32Imm8Effect 0x124538 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x124538 (fun s => s.RIP = 0x124538) (cmpR32Imm8Effect 0x124538 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1245e8, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l124541, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l12452f : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x0C, 0x83, 0xF9, 0x02, 0x0F, 0x85, 0xA7, 0x00,
    0x00, 0x00]

theorem code_l12452f : ∀ x ∈ codeRange 0x12452f bytes_l12452f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2452f 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124541 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124541 (movR32M32LowEffect 0x124541 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x124541 (LoadPre 0x124541 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124541 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124541 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124545 (movR8Imm8Effect 0x124545 2 1 0x16) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x124545 (fun s => s.RIP = 0x124545) (movR8Imm8Effect 0x124545 2 1 0x16) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l12454f, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l124541 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x10, 0xB1, 0x16, 0xEB, 0x06]

theorem code_l124541 : ∀ x ∈ codeRange 0x124541 bytes_l124541, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24541 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12454f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12454f (shrR8Effect 0x12454f 4 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x12454f (fun s => s.RIP = 0x12454f) (shrR8Effect 0x12454f 4 5 5) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 55) (.out 0x124553 (andR8Imm8Effect 0x124553 4 5 0x1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x124553 (fun s => s.RIP = 0x124553) (andR8Imm8Effect 0x124553 4 5 0x1) (Reg.operands [.gpr 5] [])) #v[53]
    (.letOp (n := 57) (.exec 0x124557 (StorePre 0x124557 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124557 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x124557 3 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 58) (.exec 0x12455a (StorePre 0x12455a 3 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x12455a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x12455a 3 0 (.base 3 (.d8 0x5))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 59) (.exec 0x12455d (StorePre 0x12455d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12455d + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12455d 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 60) (.exec 0x124560 (StorePre 0x124560 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x124560 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x124560 4 5 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 61) (.exec 0x124564 (StorePre 0x124564 6 (fun s => AddrMode.addr (.base 3 .none) s (0x124564 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124564 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l12456a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l12454f : List UInt8 :=
  [0x40, 0xC0, 0xED, 0x05, 0x40, 0x80, 0xE5, 0x01, 0x88, 0x4B, 0x04, 0x88, 0x43, 0x05, 0x89, 0x53,
    0x08, 0x40, 0x88, 0x6B, 0x0C, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00]

theorem code_l12454f : ∀ x ∈ codeRange 0x12454f bytes_l12454f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2454f 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12456a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12456a (addR64Imm8Effect 0x12456a 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x12456a (fun s => s.RIP = 0x12456a) (addR64Imm8Effect 0x12456a 4 0x40) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12456e (popR64Effect 0x12456e 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x12456e (popR64Effect 0x12456e 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x12456e (PopPre 0x12456e) (popR64Effect 0x12456e 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x12456f (popR64Effect 0x12456f 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[56]
    (.letOp (n := 59) (.out 0x12456f (popR64Effect 0x12456f 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x12456f (PopPre 0x12456f) (popR64Effect 0x12456f 2 14) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x124571 (popR64Effect 0x124571 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[59]
    (.letOp (n := 62) (.out 0x124571 (popR64Effect 0x124571 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x124571 (PopPre 0x124571) (popR64Effect 0x124571 1 5) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x124572 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[62]
    (.letOp (n := 65) (.out 0x124572 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x124572 (RetPre 0x124572) (retEffect) (Reg.operands [.gpr 4] [])) #v[62]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (5, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67) (some ⟨64, by decide⟩))))))))))))))))

def bytes_l12456a : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x40, 0x5B, 0x41, 0x5E, 0x5D, 0xC3]

theorem code_l12456a : ∀ x ∈ codeRange 0x12456a bytes_l12456a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2456a 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12458b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12458b (cmpR8Imm8Effect 0x12458b 4 5 0xc0) (EffectPart.reads (.flag .CF) [.gpr 5] []) (.flag .CF)) #v[5]
    (.letOp (n := 54) (.out 0x12458b (cmpR8Imm8Effect 0x12458b 4 5 0xc0) (EffectPart.reads (.flag .SF) [.gpr 5] []) (.flag .SF)) #v[5]
    (.letOp (n := 55) (.out 0x12458b (cmpR8Imm8Effect 0x12458b 4 5 0xc0) (EffectPart.reads (.flag .OF) [.gpr 5] []) (.flag .OF)) #v[5]
    (.letOp (n := 56) (.exec 0x12458b (fun s => s.RIP = 0x12458b) (cmpR8Imm8Effect 0x12458b 4 5 0xc0) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.pure (condOp 13)) #v[54, 55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1245b8, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124591, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12458b : List UInt8 :=
  [0x40, 0x80, 0xFD, 0xC0, 0x7D, 0x27]

theorem code_l12458b : ∀ x ∈ codeRange 0x12458b bytes_l12458b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2458b 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124591 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124591 (movzxR32R8Effect 0x124591 4 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 54) (.exec 0x124591 (fun s => s.RIP = 0x124591) (movzxR32R8Effect 0x124591 4 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x124595 (leaR64Effect 0x124595 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x124595 (fun s => s.RIP = 0x124595) (leaR64Effect 0x124595 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x12459a (movR64R64Effect 0x12459a 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x12459a (fun s => s.RIP = 0x12459a) (movR64R64Effect 0x12459a 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x12459d (callEffect (fun _ => 0x124670) 0x1245a2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x12459d (PushPre 0x12459d 5) (callEffect (fun _ => 0x124670) 0x1245a2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1245a2⟩) #v[]
    (.terminate (.call ⟨.l124670, RegMap.args [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1245a2, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l124591 : List UInt8 :=
  [0x40, 0x0F, 0xB6, 0xF5, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF2, 0xE8, 0xCE, 0x00, 0x00,
    0x00]

theorem code_l124591 : ∀ x ∈ codeRange 0x124591 bytes_l124591, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24591 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245a2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1245a2 (movR32M32LowEffect 0x1245a2 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1245a2 (LoadPre 0x1245a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1245a2 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1245a2 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1245a6 (movzxR32M8Effect 0x1245a6 5 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1245a6 (LoadPre 0x1245a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1245a6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1245a6 5 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1245ab (cmpR32Imm8Effect 0x1245ab 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x1245ab (fun s => s.RIP = 0x1245ab) (cmpR32Imm8Effect 0x1245ab 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1245e8, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1245b0, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1245a2 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x0C, 0x83, 0xF9, 0x02, 0x75, 0x38]

theorem code_l1245a2 : ∀ x ∈ codeRange 0x1245a2 bytes_l1245a2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x245a2 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1245b0 (movR32M32LowEffect 0x1245b0 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1245b0 (LoadPre 0x1245b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1245b0 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1245b0 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1245b4 (movR8Imm8Effect 0x1245b4 2 1 0x17) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x1245b4 (fun s => s.RIP = 0x1245b4) (movR8Imm8Effect 0x1245b4 2 1 0x17) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l12454f, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1245b0 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x10, 0xB1, 0x17, 0xEB, 0x97]

theorem code_l1245b0 : ∀ x ∈ codeRange 0x1245b0 bytes_l1245b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x245b0 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245b8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.pure (condOp 2)) #v[16]
    (.terminate (.condBr (Fin.last 53) ⟨.l12463e, RegMap.args (entryMap (live .l1245b8)) 54⟩ ⟨.l1245be, RegMap.args (entryMap (live .l1245b8)) 54⟩))

def bytes_l1245b8 : List UInt8 :=
  [0x0F, 0x82, 0x80, 0x00, 0x00, 0x00]

theorem code_l1245b8 : ∀ x ∈ codeRange 0x1245b8 bytes_l1245b8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x245b8 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245be : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1245be (movzxR32R8Effect 0x1245be 4 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 54) (.exec 0x1245be (fun s => s.RIP = 0x1245be) (movzxR32R8Effect 0x1245be 4 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x1245c2 (leaR64Effect 0x1245c2 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x1245c2 (fun s => s.RIP = 0x1245c2) (leaR64Effect 0x1245c2 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1245c7 (movR64R64Effect 0x1245c7 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x1245c7 (fun s => s.RIP = 0x1245c7) (movR64R64Effect 0x1245c7 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x1245ca (callEffect (fun _ => 0x124670) 0x1245cf) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1245ca (PushPre 0x1245ca 5) (callEffect (fun _ => 0x124670) 0x1245cf) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1245cf⟩) #v[]
    (.terminate (.call ⟨.l124670, RegMap.args [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1245cf, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1245be : List UInt8 :=
  [0x40, 0x0F, 0xB6, 0xF5, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF2, 0xE8, 0xA1, 0x00, 0x00,
    0x00]

theorem code_l1245be : ∀ x ∈ codeRange 0x1245be bytes_l1245be, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x245be 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245cf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1245cf (movR32M32LowEffect 0x1245cf 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1245cf (LoadPre 0x1245cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1245cf + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1245cf 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1245d3 (movzxR32M8Effect 0x1245d3 5 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1245d3 (LoadPre 0x1245d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1245d3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1245d3 5 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1245d8 (cmpR32Imm8Effect 0x1245d8 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x1245d8 (fun s => s.RIP = 0x1245d8) (cmpR32Imm8Effect 0x1245d8 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1245e8, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1245dd, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1245cf : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x0C, 0x83, 0xF9, 0x02, 0x75, 0x0B]

theorem code_l1245cf : ∀ x ∈ codeRange 0x1245cf bytes_l1245cf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x245cf 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245dd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1245dd (movR32M32LowEffect 0x1245dd 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1245dd (LoadPre 0x1245dd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1245dd + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1245dd 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1245e1 (movR8Imm8Effect 0x1245e1 2 1 0x18) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x1245e1 (fun s => s.RIP = 0x1245e1) (movR8Imm8Effect 0x1245e1 2 1 0x18) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l12454f, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1245dd : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x10, 0xB1, 0x18, 0xE9, 0x67, 0xFF, 0xFF, 0xFF]

theorem code_l1245dd : ∀ x ∈ codeRange 0x1245dd bytes_l1245dd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x245dd 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245e8_1 : Block Op Label signature Reg.count 82 :=
  .terminate (.br ⟨.l12456a, RegMap.args [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 76), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩)

def bytes_l1245e8_1 : List UInt8 :=
  [0xE9, 0x2C, 0xFF, 0xFF, 0xFF]

theorem code_l1245e8_1 : ∀ x ∈ codeRange 0x124639 bytes_l1245e8_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24639 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245e8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1245e8 (movzxR32M8Effect 0x1245e8 5 2 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1245e8 (LoadPre 0x1245e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1245e8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1245e8 5 2 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1245ed (StorePre 0x1245ed 3 (fun s => AddrMode.addr (.base 3 (.d8 0x7)) s (0x1245ed + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1245ed 3 2 (.base 3 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x1245f0 (movzxR32M16Effect 0x1245f0 5 2 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 57) (.exec 0x1245f0 (LoadPre 0x1245f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x1245f0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1245f0 5 2 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1245f5 (StorePre 0x1245f5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x1245f5 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x1245f5 4 2 (.base 3 (.d8 0x5))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x1245f9 (movR32M32LowEffect 0x1245f9 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x1245f9 (LoadPre 0x1245f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1245f9 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1245f9 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1245fd (movR64M64Effect 0x1245fd 6 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x1245fd (LoadPre 0x1245fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1245fd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1245fd 6 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x124602 (StorePre 0x124602 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x124602 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124602 6 (.base 3 (.d8 0x14))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 64) (.out 0x124606 (movR64M64Effect 0x124606 6 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 65) (.exec 0x124606 (LoadPre 0x124606 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x124606 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124606 6 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x12460b (StorePre 0x12460b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x12460b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12460b 6 (.base 3 (.d8 0x1c))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[64, 3]
    (.letOp (n := 67) (.out 0x12460f (movR64M64Effect 0x12460f 6 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x12460f (LoadPre 0x12460f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x12460f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12460f 6 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x124614 (StorePre 0x124614 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x124614 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124614 6 (.base 3 (.d8 0x24))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[67, 3]
    (.letOp (n := 70) (.out 0x124618 (movR64M64Effect 0x124618 6 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 71) (.exec 0x124618 (LoadPre 0x124618 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x124618 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124618 6 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x12461d (StorePre 0x12461d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x12461d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12461d 6 (.base 3 (.d8 0x2c))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[70, 3]
    (.letOp (n := 73) (.out 0x124621 (movR32M32LowEffect 0x124621 6 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 74) (.exec 0x124621 (LoadPre 0x124621 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x124621 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124621 6 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x124625 (StorePre 0x124625 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x124625 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124625 6 (.base 3 (.d8 0x34))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[73, 3]
    (.letOp (n := 76) (.out 0x124628 (movR64M64Effect 0x124628 6 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 77) (.exec 0x124628 (LoadPre 0x124628 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124628 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124628 6 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x12462d (StorePre 0x12462d 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x12462d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12462d 6 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[76, 3]
    (.letOp (n := 79) (.exec 0x124631 (StorePre 0x124631 2 (fun s => AddrMode.addr (.base 3 .none) s (0x124631 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x124631 1 (.base 3 .none)) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 80) (.exec 0x124633 (StorePre 0x124633 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124633 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x124633 3 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 81) (.exec 0x124636 (StorePre 0x124636 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x124636 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124636 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[59, 3]
    (b_l1245e8_1)))))))))))))))))))))))))))))

def bytes_l1245e8 : List UInt8 :=
  [0x0F, 0xB6, 0x54, 0x24, 0x0F, 0x88, 0x53, 0x07, 0x0F, 0xB7, 0x54, 0x24, 0x0D, 0x66, 0x89, 0x53,
    0x05, 0x8B, 0x54, 0x24, 0x10, 0x48, 0x8B, 0x74, 0x24, 0x1C, 0x48, 0x89, 0x73, 0x14, 0x48, 0x8B,
    0x74, 0x24, 0x24, 0x48, 0x89, 0x73, 0x1C, 0x48, 0x8B, 0x74, 0x24, 0x2C, 0x48, 0x89, 0x73, 0x24,
    0x48, 0x8B, 0x74, 0x24, 0x34, 0x48, 0x89, 0x73, 0x2C, 0x8B, 0x74, 0x24, 0x3C, 0x89, 0x73, 0x34,
    0x48, 0x8B, 0x74, 0x24, 0x14, 0x48, 0x89, 0x73, 0x0C, 0x89, 0x0B, 0x88, 0x43, 0x04, 0x89, 0x53,
    0x08] ++ bytes_l1245e8_1

theorem code_l1245e8 : ∀ x ∈ codeRange 0x1245e8 bytes_l1245e8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x245e8 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1245e8_1

@[cfg_block] def b_l12463e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12463e (StorePre 0x12463e 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x12463e + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x12463e (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x124643 (movR32M32Effect 0x124643 0 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 55) (.exec 0x124643 (LoadPre 0x124643 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x124643 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x124643 0 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.exec 0x124647 (StorePre 0x124647 6 (fun s => AddrMode.addr (.base 3 .none) s (0x124647 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124647 6 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.exec 0x12464d (StorePre 0x12464d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x12464d + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12464d 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[54, 3]
    (.letOp (n := 58) (.exec 0x124650 (StorePre 0x124650 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x124650 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124650 (.base 3 (.d8 0x8)) 0x12) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.exec 0x124654 (StorePre 0x124654 4 (fun s => AddrMode.addr (.base 3 (.d8 0x9)) s (0x124654 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x124654 4 5 (.base 3 (.d8 0x9))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[5, 3]
    (.terminate (.br ⟨.l12456a, RegMap.args [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l12463e : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x46, 0x1C, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00, 0x89,
    0x43, 0x04, 0xC6, 0x43, 0x08, 0x12, 0x40, 0x88, 0x6B, 0x09, 0xE9, 0x0D, 0xFF, 0xFF, 0xFF]

theorem code_l12463e : ∀ x ∈ codeRange 0x12463e bytes_l12463e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2463e 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12465d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12465d (movR32Imm32Effect 0x12465d 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x12465d (fun s => s.RIP = 0x12465d) (movR32Imm32Effect 0x12465d 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x124662 (movR64Imm32Effect 0x124662 2 0x2036e0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x124662 (fun s => s.RIP = 0x124662) (movR64Imm32Effect 0x124662 2 0x2036e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x124669 (callEffect (fun _ => 0x129c90) 0x12466e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x124669 (PushPre 0x124669 5) (callEffect (fun _ => 0x129c90) 0x12466e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x12466e⟩) #v[]
    (.terminate (.call ⟨.l129c90, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)] 60⟩ { target := .l12466e, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l12465d : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xE0, 0x36, 0x20, 0x00, 0xE8, 0x22, 0x56, 0x00,
    0x00]

theorem code_l12465d : ∀ x ∈ codeRange 0x12465d bytes_l12465d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2465d 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12466e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12466e (fun s => s.RIP = 0x12466e) (fun _ => nopEffect 0x12466e 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l124670, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l12466e : List UInt8 :=
  [0x66, 0x90]

theorem code_l12466e : ∀ x ∈ codeRange 0x12466e bytes_l12466e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2466e 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124670 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124670 (pushR64Effect 0x124670 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x124670 (PushPre 0x124670 1) (pushR64Effect 0x124670 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x124671 (pushR64Effect 0x124671 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x124671 (PushPre 0x124671 2) (pushR64Effect 0x124671 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x124673 (pushR64Effect 0x124673 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x124673 (PushPre 0x124673 2) (pushR64Effect 0x124673 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x124675 (pushR64Effect 0x124675 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x124675 (PushPre 0x124675 2) (pushR64Effect 0x124675 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x124677 (pushR64Effect 0x124677 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x124677 (PushPre 0x124677 2) (pushR64Effect 0x124677 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x124679 (pushR64Effect 0x124679 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x124679 (PushPre 0x124679 1) (pushR64Effect 0x124679 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x12467a (subR64Imm8Effect 0x12467a 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x12467a (fun s => s.RIP = 0x12467a) (subR64Imm8Effect 0x12467a 4 0x38) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x12467e (movR64R64Effect 0x12467e 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x12467e (fun s => s.RIP = 0x12467e) (movR64R64Effect 0x12467e 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x124681 (movR32R32Effect 0x124681 2 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 70) (.exec 0x124681 (fun s => s.RIP = 0x124681) (movR32R32Effect 0x124681 2 5 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x124683 (andR8Imm8Effect 0x124683 4 5 0x20) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[69]
    (.letOp (n := 72) (.exec 0x124683 (fun s => s.RIP = 0x124683) (andR8Imm8Effect 0x124683 4 5 0x20) (Reg.operands [.gpr 5] [])) #v[69]
    (.letOp (n := 73) (.out 0x124687 (andR8Imm8Effect 0x124687 4 6 0x1f) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 74) (.exec 0x124687 (fun s => s.RIP = 0x124687) (andR8Imm8Effect 0x124687 4 6 0x1f) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 75) (.out 0x12468b (cmpR8Imm8Effect 0x12468b 4 6 0x1f) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[73]
    (.letOp (n := 76) (.exec 0x12468b (fun s => s.RIP = 0x12468b) (cmpR8Imm8Effect 0x12468b 4 6 0x1f) (Reg.operands [.gpr 6] [])) #v[73]
    (.letOp (n := 77) (.pure (condOp 5)) #v[75]
    (.terminate (.condBr (Fin.last 77) ⟨.l1246eb, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ ⟨.l124691, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l124670 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x38, 0x48, 0x89,
    0xFB, 0x89, 0xF5, 0x40, 0x80, 0xE5, 0x20, 0x40, 0x80, 0xE6, 0x1F, 0x40, 0x80, 0xFE, 0x1F, 0x75,
    0x5A]

theorem code_l124670 : ∀ x ∈ codeRange 0x124670 bytes_l124670, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24670 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124691 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124691 (movR64R64Effect 0x124691 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 54) (.exec 0x124691 (fun s => s.RIP = 0x124691) (movR64R64Effect 0x124691 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x124694 (movR64R64Effect 0x124694 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x124694 (fun s => s.RIP = 0x124694) (movR64R64Effect 0x124694 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124697 (movR64R64Effect 0x124697 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 58) (.exec 0x124697 (fun s => s.RIP = 0x124697) (movR64R64Effect 0x124697 6 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 59) (.out 0x12469a (movR32Imm32Effect 0x12469a 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x12469a (fun s => s.RIP = 0x12469a) (movR32Imm32Effect 0x12469a 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x12469f (callEffect (fun _ => 0x127b80) 0x1246a4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x12469f (PushPre 0x12469f 5) (callEffect (fun _ => 0x127b80) 0x1246a4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x1246a4⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l1246a4, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l124691 : List UInt8 :=
  [0x49, 0x89, 0xD6, 0x48, 0x89, 0xE7, 0x48, 0x89, 0xD6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0xDC,
    0x34, 0x00, 0x00]

theorem code_l124691 : ∀ x ∈ codeRange 0x124691 bytes_l124691, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24691 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1246a4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1246a4 (movR32M32LowEffect 0x1246a4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1246a4 (LoadPre 0x1246a4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1246a4 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1246a4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1246a7 (cmpR32Imm8Effect 0x1246a7 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1246a7 (fun s => s.RIP = 0x1246a7) (cmpR32Imm8Effect 0x1246a7 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124855, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1246b0, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1246a4 : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0xA5, 0x01, 0x00, 0x00]

theorem code_l1246a4 : ∀ x ∈ codeRange 0x1246a4 bytes_l1246a4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x246a4 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1246b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1246b0 (movR64M64Effect 0x1246b0 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x1246b0 (LoadPre 0x1246b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1246b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1246b0 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1246b5 (cmpR64Imm8Effect 0x1246b5 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1246b5 (fun s => s.RIP = 0x1246b5) (cmpR64Imm8Effect 0x1246b5 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1248a3, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1246bf, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1246b0 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0xE4, 0x01, 0x00, 0x00]

theorem code_l1246b0 : ∀ x ∈ codeRange 0x1246b0 bytes_l1246b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x246b0 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1246bf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1246bf (movR64M64Effect 0x1246bf 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1246bf (LoadPre 0x1246bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1246bf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1246bf 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1246c4 (movzxR32M8Effect 0x1246c4 4 15 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[53]
    (.letOp (n := 56) (.exec 0x1246c4 (LoadPre 0x1246c4 (fun s => AddrMode.addr (.base 0 .none) s (0x1246c4 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1246c4 4 15 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1246c8 (movR32R32Effect 0x1246c8 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x1246c8 (fun s => s.RIP = 0x1246c8) (movR32R32Effect 0x1246c8 3 0 15) (Reg.operands [.gpr 15] [])) #v[55]
    (.letOp (n := 59) (.out 0x1246cb (andR32Imm8Effect 0x1246cb 4 15 0x7f) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[55]
    (.letOp (n := 60) (.exec 0x1246cb (fun s => s.RIP = 0x1246cb) (andR32Imm8Effect 0x1246cb 4 15 0x7f) (Reg.operands [.gpr 15] [])) #v[55]
    (.letOp (n := 61) (.out 0x1246cf (testR8R8Effect 0x1246cf 2 0 0) (EffectPart.reads (.flag .SF) [.gpr 0, .gpr 0] []) (.flag .SF)) #v[57, 57]
    (.letOp (n := 62) (.exec 0x1246cf (fun s => s.RIP = 0x1246cf) (testR8R8Effect 0x1246cf 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[57, 57]
    (.letOp (n := 63) (.pure (condOp 8)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l124705, RegMap.args [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 59), (20, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l1246d3, RegMap.args [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 59), (20, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l1246bf : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x44, 0x0F, 0xB6, 0x38, 0x44, 0x89, 0xF8, 0x41, 0x83, 0xE7, 0x7F,
    0x84, 0xC0, 0x78, 0x32]

theorem code_l1246bf : ∀ x ∈ codeRange 0x1246bf bytes_l1246bf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x246bf 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1246d3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1246d3 (cmpR8Imm8Effect 0x1246d3 4 15 0x1f) (EffectPart.reads (.flag .CF) [.gpr 15] []) (.flag .CF)) #v[15]
    (.letOp (n := 54) (.exec 0x1246d3 (fun s => s.RIP = 0x1246d3) (cmpR8Imm8Effect 0x1246d3 4 15 0x1f) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.pure (condOp 2)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1247f9, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1246dd, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1246d3 : List UInt8 :=
  [0x41, 0x80, 0xFF, 0x1F, 0x0F, 0x82, 0x1C, 0x01, 0x00, 0x00]

theorem code_l1246d3 : ∀ x ∈ codeRange 0x1246d3 bytes_l1246d3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x246d3 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1246dd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1246dd (shrR8Effect 0x1246dd 4 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x1246dd (fun s => s.RIP = 0x1246dd) (shrR8Effect 0x1246dd 4 5 5) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 55) (.exec 0x1246e1 (StorePre 0x1246e1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1246e1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1246e1 4 5 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.exec 0x1246e5 (StorePre 0x1246e5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1246e5 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1246e5 15 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.terminate (.br ⟨.l1246fa, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1246dd : List UInt8 :=
  [0x40, 0xC0, 0xED, 0x05, 0x40, 0x88, 0x6B, 0x04, 0x44, 0x89, 0x7B, 0x08, 0xEB, 0x0F]

theorem code_l1246dd : ∀ x ∈ codeRange 0x1246dd bytes_l1246dd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x246dd 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1246eb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1246eb (movzxR32R8Effect 0x1246eb 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x1246eb (fun s => s.RIP = 0x1246eb) (movzxR32R8Effect 0x1246eb 4 0 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1246ef (shrR8Effect 0x1246ef 4 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 56) (.exec 0x1246ef (fun s => s.RIP = 0x1246ef) (shrR8Effect 0x1246ef 4 5 5) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 57) (.exec 0x1246f3 (StorePre 0x1246f3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1246f3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1246f3 4 5 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 58) (.exec 0x1246f7 (StorePre 0x1246f7 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1246f7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1246f7 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 3]
    (.terminate (.br ⟨.l1246fa, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1246eb : List UInt8 :=
  [0x40, 0x0F, 0xB6, 0xC6, 0x40, 0xC0, 0xED, 0x05, 0x40, 0x88, 0x6B, 0x04, 0x89, 0x43, 0x08]

theorem code_l1246eb : ∀ x ∈ codeRange 0x1246eb bytes_l1246eb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x246eb 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1246fa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1246fa (StorePre 0x1246fa 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1246fa + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1246fa 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l124894, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l1246fa : List UInt8 :=
  [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0x8F, 0x01, 0x00, 0x00]

theorem code_l1246fa : ∀ x ∈ codeRange 0x1246fa bytes_l1246fa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x246fa 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124705 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124705 (testR8R8Effect 0x124705 3 15 15) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 15] []) (.flag .ZF)) #v[15, 15]
    (.letOp (n := 54) (.exec 0x124705 (fun s => s.RIP = 0x124705) (testR8R8Effect 0x124705 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1247f9, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l12470e, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l124705 : List UInt8 :=
  [0x45, 0x84, 0xFF, 0x0F, 0x84, 0xEB, 0x00, 0x00, 0x00]

theorem code_l124705 : ∀ x ∈ codeRange 0x124705 bytes_l124705, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24705 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12470e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12470e (movR64R64Effect 0x12470e 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x12470e (fun s => s.RIP = 0x12470e) (movR64R64Effect 0x12470e 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124711 (movR64R64Effect 0x124711 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x124711 (fun s => s.RIP = 0x124711) (movR64R64Effect 0x124711 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x124714 (movR32Imm32Effect 0x124714 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x124714 (fun s => s.RIP = 0x124714) (movR32Imm32Effect 0x124714 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x124719 (callEffect (fun _ => 0x127b80) 0x12471e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x124719 (PushPre 0x124719 5) (callEffect (fun _ => 0x127b80) 0x12471e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x12471e⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l12471e, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l12470e : List UInt8 :=
  [0x48, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0x62, 0x34, 0x00, 0x00]

theorem code_l12470e : ∀ x ∈ codeRange 0x12470e bytes_l12470e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2470e 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12471e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12471e (movR32M32LowEffect 0x12471e 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x12471e (LoadPre 0x12471e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12471e + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x12471e 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124721 (cmpR32Imm8Effect 0x124721 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124721 (fun s => s.RIP = 0x124721) (cmpR32Imm8Effect 0x124721 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124855, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l12472a, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12471e : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x2B, 0x01, 0x00, 0x00]

theorem code_l12471e : ∀ x ∈ codeRange 0x12471e bytes_l12471e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2471e 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12472a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12472a (movR64M64Effect 0x12472a 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x12472a (LoadPre 0x12472a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12472a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12472a 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12472f (cmpR64Imm8Effect 0x12472f 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x12472f (fun s => s.RIP = 0x12472f) (cmpR64Imm8Effect 0x12472f 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1248a3, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124739, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12472a : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0x6A, 0x01, 0x00, 0x00]

theorem code_l12472a : ∀ x ∈ codeRange 0x12472a bytes_l12472a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2472a 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124739 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124739 (movR32R32Effect 0x124739 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x124739 (fun s => s.RIP = 0x124739) (movR32R32Effect 0x124739 3 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x12473c (shlR32Effect 0x12473c 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x12473c (fun s => s.RIP = 0x12473c) (shlR32Effect 0x12473c 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x12473f (movR64M64Effect 0x12473f 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x12473f (LoadPre 0x12473f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12473f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12473f 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x124744 (movzxR32M8Effect 0x124744 4 12 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[57]
    (.letOp (n := 60) (.exec 0x124744 (LoadPre 0x124744 (fun s => AddrMode.addr (.base 1 .none) s (0x124744 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x124744 4 12 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 61) (.out 0x124748 (movR32R32Effect 0x124748 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 62) (.exec 0x124748 (fun s => s.RIP = 0x124748) (movR32R32Effect 0x124748 3 1 12) (Reg.operands [.gpr 12] [])) #v[59]
    (.letOp (n := 63) (.out 0x12474b (andR32Imm8Effect 0x12474b 4 12 0x7f) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[59]
    (.letOp (n := 64) (.exec 0x12474b (fun s => s.RIP = 0x12474b) (andR32Imm8Effect 0x12474b 4 12 0x7f) (Reg.operands [.gpr 12] [])) #v[59]
    (.letOp (n := 65) (.out 0x12474f (orR32R32Effect 0x12474f 3 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[63, 55]
    (.letOp (n := 66) (.exec 0x12474f (fun s => s.RIP = 0x12474f) (orR32R32Effect 0x12474f 3 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[63, 55]
    (.letOp (n := 67) (.out 0x124752 (testR8R8Effect 0x124752 2 1 1) (EffectPart.reads (.flag .SF) [.gpr 1, .gpr 1] []) (.flag .SF)) #v[61, 61]
    (.letOp (n := 68) (.exec 0x124752 (fun s => s.RIP = 0x124752) (testR8R8Effect 0x124752 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[61, 61]
    (.letOp (n := 69) (.pure (condOp 8)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l12475b, RegMap.args [(0, 55), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l124756, RegMap.args [(0, 55), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l124739 : List UInt8 :=
  [0x44, 0x89, 0xF8, 0xC1, 0xE0, 0x07, 0x48, 0x8B, 0x4C, 0x24, 0x08, 0x44, 0x0F, 0xB6, 0x21, 0x44,
    0x89, 0xE1, 0x41, 0x83, 0xE4, 0x7F, 0x41, 0x09, 0xC4, 0x84, 0xC9, 0x78, 0x05]

theorem code_l124739 : ∀ x ∈ codeRange 0x124739 bytes_l124739, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24739 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124756 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124756 (movR32R32Effect 0x124756 3 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 12] []) (.reg (.gpr 15))) #v[12]
    (.letOp (n := 54) (.exec 0x124756 (fun s => s.RIP = 0x124756) (movR32R32Effect 0x124756 3 15 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.terminate (.br ⟨.l1246dd, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l124756 : List UInt8 :=
  [0x45, 0x89, 0xE7, 0xEB, 0x82]

theorem code_l124756 : ∀ x ∈ codeRange 0x124756 bytes_l124756, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24756 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12475b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12475b (movR64R64Effect 0x12475b 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x12475b (fun s => s.RIP = 0x12475b) (movR64R64Effect 0x12475b 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12475e (movR64R64Effect 0x12475e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x12475e (fun s => s.RIP = 0x12475e) (movR64R64Effect 0x12475e 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x124761 (movR32Imm32Effect 0x124761 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x124761 (fun s => s.RIP = 0x124761) (movR32Imm32Effect 0x124761 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x124766 (callEffect (fun _ => 0x127b80) 0x12476b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x124766 (PushPre 0x124766 5) (callEffect (fun _ => 0x127b80) 0x12476b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x12476b⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l12476b, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l12475b : List UInt8 :=
  [0x48, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0x15, 0x34, 0x00, 0x00]

theorem code_l12475b : ∀ x ∈ codeRange 0x12475b bytes_l12475b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2475b 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12476b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12476b (movR32M32LowEffect 0x12476b 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x12476b (LoadPre 0x12476b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12476b + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x12476b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12476e (cmpR32Imm8Effect 0x12476e 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x12476e (fun s => s.RIP = 0x12476e) (cmpR32Imm8Effect 0x12476e 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124855, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124777, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12476b : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0xDE, 0x00, 0x00, 0x00]

theorem code_l12476b : ∀ x ∈ codeRange 0x12476b bytes_l12476b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2476b 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124777 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124777 (movR64M64Effect 0x124777 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x124777 (LoadPre 0x124777 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124777 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124777 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12477c (cmpR64Imm8Effect 0x12477c 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x12477c (fun s => s.RIP = 0x12477c) (cmpR64Imm8Effect 0x12477c 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1248a3, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124786, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124777 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0x1D, 0x01, 0x00, 0x00]

theorem code_l124777 : ∀ x ∈ codeRange 0x124777 bytes_l124777, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24777 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124786 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124786 (shlR32Effect 0x124786 4 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 54) (.exec 0x124786 (fun s => s.RIP = 0x124786) (shlR32Effect 0x124786 4 12 7) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[12]
    (.letOp (n := 55) (.out 0x12478a (movR64M64Effect 0x12478a 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x12478a (LoadPre 0x12478a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12478a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12478a 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x12478f (movzxR32M8Effect 0x12478f 4 13 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[55]
    (.letOp (n := 58) (.exec 0x12478f (LoadPre 0x12478f (fun s => AddrMode.addr (.base 0 .none) s (0x12478f + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x12478f 4 13 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x124793 (movR32R32Effect 0x124793 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 60) (.exec 0x124793 (fun s => s.RIP = 0x124793) (movR32R32Effect 0x124793 3 0 13) (Reg.operands [.gpr 13] [])) #v[57]
    (.letOp (n := 61) (.out 0x124796 (andR32Imm8Effect 0x124796 4 13 0x7f) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[57]
    (.letOp (n := 62) (.exec 0x124796 (fun s => s.RIP = 0x124796) (andR32Imm8Effect 0x124796 4 13 0x7f) (Reg.operands [.gpr 13] [])) #v[57]
    (.letOp (n := 63) (.out 0x12479a (orR32R32Effect 0x12479a 3 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[61, 53]
    (.letOp (n := 64) (.exec 0x12479a (fun s => s.RIP = 0x12479a) (orR32R32Effect 0x12479a 3 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[61, 53]
    (.letOp (n := 65) (.out 0x12479d (testR8R8Effect 0x12479d 2 0 0) (EffectPart.reads (.flag .SF) [.gpr 0, .gpr 0] []) (.flag .SF)) #v[59, 59]
    (.letOp (n := 66) (.exec 0x12479d (fun s => s.RIP = 0x12479d) (testR8R8Effect 0x12479d 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[59, 59]
    (.letOp (n := 67) (.pure (condOp 8)) #v[65]
    (.terminate (.condBr (Fin.last 67) ⟨.l1247a9, RegMap.args [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 63), (14, 14), (15, 15), (20, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l1247a1, RegMap.args [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 63), (14, 14), (15, 15), (20, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l124786 : List UInt8 :=
  [0x41, 0xC1, 0xE4, 0x07, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x44, 0x0F, 0xB6, 0x28, 0x44, 0x89, 0xE8,
    0x41, 0x83, 0xE5, 0x7F, 0x45, 0x09, 0xE5, 0x84, 0xC0, 0x78, 0x08]

theorem code_l124786 : ∀ x ∈ codeRange 0x124786 bytes_l124786, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24786 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1247a1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1247a1 (movR32R32Effect 0x1247a1 3 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 13] []) (.reg (.gpr 15))) #v[13]
    (.letOp (n := 54) (.exec 0x1247a1 (fun s => s.RIP = 0x1247a1) (movR32R32Effect 0x1247a1 3 15 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.terminate (.br ⟨.l1246dd, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1247a1 : List UInt8 :=
  [0x45, 0x89, 0xEF, 0xE9, 0x34, 0xFF, 0xFF, 0xFF]

theorem code_l1247a1 : ∀ x ∈ codeRange 0x1247a1 bytes_l1247a1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x247a1 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1247a9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1247a9 (movR64R64Effect 0x1247a9 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1247a9 (fun s => s.RIP = 0x1247a9) (movR64R64Effect 0x1247a9 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1247ac (movR64R64Effect 0x1247ac 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x1247ac (fun s => s.RIP = 0x1247ac) (movR64R64Effect 0x1247ac 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x1247af (movR32Imm32Effect 0x1247af 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x1247af (fun s => s.RIP = 0x1247af) (movR32Imm32Effect 0x1247af 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1247b4 (callEffect (fun _ => 0x127b80) 0x1247b9) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1247b4 (PushPre 0x1247b4 5) (callEffect (fun _ => 0x127b80) 0x1247b9) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1247b9⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1247b9, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1247a9 : List UInt8 :=
  [0x48, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0xC7, 0x33, 0x00, 0x00]

theorem code_l1247a9 : ∀ x ∈ codeRange 0x1247a9 bytes_l1247a9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x247a9 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1247b9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1247b9 (movR32M32LowEffect 0x1247b9 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1247b9 (LoadPre 0x1247b9 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1247b9 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1247b9 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1247bc (cmpR32Imm8Effect 0x1247bc 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1247bc (fun s => s.RIP = 0x1247bc) (cmpR32Imm8Effect 0x1247bc 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124855, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1247c5, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1247b9 : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x90, 0x00, 0x00, 0x00]

theorem code_l1247b9 : ∀ x ∈ codeRange 0x1247b9 bytes_l1247b9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x247b9 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1247c5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1247c5 (movR64M64Effect 0x1247c5 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x1247c5 (LoadPre 0x1247c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1247c5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1247c5 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1247ca (cmpR64Imm8Effect 0x1247ca 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1247ca (fun s => s.RIP = 0x1247ca) (cmpR64Imm8Effect 0x1247ca 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1248a3, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1247d4, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1247c5 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0xCF, 0x00, 0x00, 0x00]

theorem code_l1247c5 : ∀ x ∈ codeRange 0x1247c5 bytes_l1247c5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x247c5 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1247d4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1247d4 (shlR32Effect 0x1247d4 4 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 54) (.exec 0x1247d4 (fun s => s.RIP = 0x1247d4) (shlR32Effect 0x1247d4 4 13 7) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[13]
    (.letOp (n := 55) (.out 0x1247d8 (movR64M64Effect 0x1247d8 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1247d8 (LoadPre 0x1247d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1247d8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1247d8 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1247dd (movzxR32M8Effect 0x1247dd 4 12 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[55]
    (.letOp (n := 58) (.exec 0x1247dd (LoadPre 0x1247dd (fun s => AddrMode.addr (.base 0 .none) s (0x1247dd + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1247dd 4 12 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x1247e1 (movR32R32Effect 0x1247e1 3 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 60) (.exec 0x1247e1 (fun s => s.RIP = 0x1247e1) (movR32R32Effect 0x1247e1 3 0 12) (Reg.operands [.gpr 12] [])) #v[57]
    (.letOp (n := 61) (.out 0x1247e4 (andR32Imm8Effect 0x1247e4 4 12 0x7f) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[57]
    (.letOp (n := 62) (.exec 0x1247e4 (fun s => s.RIP = 0x1247e4) (andR32Imm8Effect 0x1247e4 4 12 0x7f) (Reg.operands [.gpr 12] [])) #v[57]
    (.letOp (n := 63) (.out 0x1247e8 (orR32R32Effect 0x1247e8 3 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[61, 53]
    (.letOp (n := 64) (.exec 0x1247e8 (fun s => s.RIP = 0x1247e8) (orR32R32Effect 0x1247e8 3 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[61, 53]
    (.letOp (n := 65) (.out 0x1247eb (testR8R8Effect 0x1247eb 2 0 0) (EffectPart.reads (.flag .SF) [.gpr 0, .gpr 0] []) (.flag .SF)) #v[59, 59]
    (.letOp (n := 66) (.exec 0x1247eb (fun s => s.RIP = 0x1247eb) (testR8R8Effect 0x1247eb 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[59, 59]
    (.letOp (n := 67) (.pure (condOp 9)) #v[65]
    (.terminate (.condBr (Fin.last 67) ⟨.l124756, RegMap.args [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 63), (13, 53), (14, 14), (15, 15), (20, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l1247f3, RegMap.args [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 63), (13, 53), (14, 14), (15, 15), (20, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l1247d4 : List UInt8 :=
  [0x41, 0xC1, 0xE5, 0x07, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x44, 0x0F, 0xB6, 0x20, 0x44, 0x89, 0xE0,
    0x41, 0x83, 0xE4, 0x7F, 0x45, 0x09, 0xEC, 0x84, 0xC0, 0x0F, 0x89, 0x63, 0xFF, 0xFF, 0xFF]

theorem code_l1247d4 : ∀ x ∈ codeRange 0x1247d4 bytes_l1247d4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x247d4 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1247f3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1247f3 (cmpR8Imm8Effect 0x1247f3 4 15 0xf) (EffectPart.reads (.flag .CF) [.gpr 15] []) (.flag .CF)) #v[15]
    (.letOp (n := 54) (.out 0x1247f3 (cmpR8Imm8Effect 0x1247f3 4 15 0xf) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[15]
    (.letOp (n := 55) (.exec 0x1247f3 (fun s => s.RIP = 0x1247f3) (cmpR8Imm8Effect 0x1247f3 4 15 0xf) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l124814, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l1247f9, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1247f3 : List UInt8 :=
  [0x41, 0x80, 0xFF, 0x0F, 0x76, 0x1B]

theorem code_l1247f3 : ∀ x ∈ codeRange 0x1247f3 bytes_l1247f3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x247f3 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1247f9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1247f9 (StorePre 0x1247f9 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1247f9 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1247f9 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x1247fe (movR32M32Effect 0x1247fe 0 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 55) (.exec 0x1247fe (LoadPre 0x1247fe (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1247fe + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1247fe 0 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.exec 0x124802 (StorePre 0x124802 6 (fun s => AddrMode.addr (.base 3 .none) s (0x124802 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124802 6 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.exec 0x124808 (StorePre 0x124808 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124808 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124808 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[54, 3]
    (.letOp (n := 58) (.exec 0x12480b (StorePre 0x12480b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12480b + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x12480b (.base 3 (.d8 0x8)) 0x10) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l124894, RegMap.args [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1247f9 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x46, 0x1C, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00, 0x89,
    0x43, 0x04, 0xC6, 0x43, 0x08, 0x10, 0xE9, 0x80, 0x00, 0x00, 0x00]

theorem code_l1247f9 : ∀ x ∈ codeRange 0x1247f9 bytes_l1247f9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x247f9 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124814 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124814 (movR64R64Effect 0x124814 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x124814 (fun s => s.RIP = 0x124814) (movR64R64Effect 0x124814 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124817 (movR64R64Effect 0x124817 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x124817 (fun s => s.RIP = 0x124817) (movR64R64Effect 0x124817 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x12481a (movR32Imm32Effect 0x12481a 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x12481a (fun s => s.RIP = 0x12481a) (movR32Imm32Effect 0x12481a 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x12481f (callEffect (fun _ => 0x127b80) 0x124824) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x12481f (PushPre 0x12481f 5) (callEffect (fun _ => 0x127b80) 0x124824) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x124824⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l124824, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l124814 : List UInt8 :=
  [0x48, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0x5C, 0x33, 0x00, 0x00]

theorem code_l124814 : ∀ x ∈ codeRange 0x124814 bytes_l124814, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24814 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124824 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124824 (movR32M32LowEffect 0x124824 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124824 (LoadPre 0x124824 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124824 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124824 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124827 (cmpR32Imm8Effect 0x124827 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124827 (fun s => s.RIP = 0x124827) (cmpR32Imm8Effect 0x124827 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124855, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l12482c, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124824 : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x75, 0x29]

theorem code_l124824 : ∀ x ∈ codeRange 0x124824 bytes_l124824, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24824 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12482c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12482c (movR64M64Effect 0x12482c 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x12482c (LoadPre 0x12482c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12482c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12482c 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124831 (cmpR64Imm8Effect 0x124831 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124831 (fun s => s.RIP = 0x124831) (cmpR64Imm8Effect 0x124831 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1248a3, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124837, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12482c : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x83, 0xFE, 0x01, 0x75, 0x6C]

theorem code_l12482c : ∀ x ∈ codeRange 0x12482c bytes_l12482c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2482c 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124837 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124837 (movR64M64Effect 0x124837 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124837 (LoadPre 0x124837 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124837 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124837 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12483c (movzxR32M8Effect 0x12483c 4 15 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[53]
    (.letOp (n := 56) (.exec 0x12483c (LoadPre 0x12483c (fun s => AddrMode.addr (.base 0 .none) s (0x12483c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x12483c 4 15 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x124840 (testR8R8Effect 0x124840 3 15 15) (EffectPart.reads (.flag .SF) [.gpr 15, .gpr 15] []) (.flag .SF)) #v[55, 55]
    (.letOp (n := 58) (.exec 0x124840 (fun s => s.RIP = 0x124840) (testR8R8Effect 0x124840 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[55, 55]
    (.letOp (n := 59) (.pure (condOp 8)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1247f9, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 55), (20, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l124845, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 55), (20, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l124837 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x44, 0x0F, 0xB6, 0x38, 0x45, 0x84, 0xFF, 0x78, 0xB4]

theorem code_l124837 : ∀ x ∈ codeRange 0x124837 bytes_l124837, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24837 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124845 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124845 (shlR32Effect 0x124845 4 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 54) (.exec 0x124845 (fun s => s.RIP = 0x124845) (shlR32Effect 0x124845 4 12 7) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[12]
    (.letOp (n := 55) (.out 0x124849 (andR32Imm8Effect 0x124849 4 15 0x7f) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 56) (.exec 0x124849 (fun s => s.RIP = 0x124849) (andR32Imm8Effect 0x124849 4 15 0x7f) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x12484d (orR32R32Effect 0x12484d 3 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x12484d (fun s => s.RIP = 0x12484d) (orR32R32Effect 0x12484d 3 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[55, 53]
    (.terminate (.br ⟨.l1246dd, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l124845 : List UInt8 :=
  [0x41, 0xC1, 0xE4, 0x07, 0x41, 0x83, 0xE7, 0x7F, 0x45, 0x09, 0xE7, 0xE9, 0x88, 0xFE, 0xFF, 0xFF]

theorem code_l124845 : ∀ x ∈ codeRange 0x124845 bytes_l124845, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24845 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124855 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124855 (movR32M32LowEffect 0x124855 1 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x124855 (LoadPre 0x124855 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x124855 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124855 1 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124859 (movR64M64Effect 0x124859 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x124859 (LoadPre 0x124859 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124859 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124859 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x12485e (movR64M64Effect 0x12485e 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x12485e (LoadPre 0x12485e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12485e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12485e 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x124863 (movR64M64Effect 0x124863 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x124863 (LoadPre 0x124863 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x124863 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124863 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x124868 (StorePre 0x124868 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x124868 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124868 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x12486c (movR64M64Effect 0x12486c 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x12486c (LoadPre 0x12486c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x12486c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12486c 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x124871 (StorePre 0x124871 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x124871 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124871 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 65) (.out 0x124875 (movR64M64Effect 0x124875 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x124875 (LoadPre 0x124875 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x124875 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124875 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x12487a (StorePre 0x12487a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x12487a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12487a 7 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.out 0x12487e (movR64M64Effect 0x12487e 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x12487e (LoadPre 0x12487e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12487e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12487e 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x124883 (StorePre 0x124883 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x124883 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124883 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 71) (.exec 0x124887 (StorePre 0x124887 2 (fun s => AddrMode.addr (.base 3 .none) s (0x124887 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x124887 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 72) (.exec 0x124889 (StorePre 0x124889 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124889 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124889 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 73) (.exec 0x12488c (StorePre 0x12488c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12488c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12488c 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 74) (.exec 0x124890 (StorePre 0x124890 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x124890 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124890 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[57, 3]
    (.terminate (.br ⟨.l124894, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l124855 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x04, 0x48, 0x8B, 0x54, 0x24, 0x08, 0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x8B,
    0x7C, 0x24, 0x30, 0x48, 0x89, 0x7B, 0x30, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x48, 0x89, 0x7B, 0x28,
    0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0x89, 0x7B, 0x20, 0x48, 0x8B, 0x7C, 0x24, 0x18, 0x48, 0x89,
    0x7B, 0x18, 0x89, 0x03, 0x89, 0x4B, 0x04, 0x48, 0x89, 0x53, 0x08, 0x48, 0x89, 0x73, 0x10]

theorem code_l124855 : ∀ x ∈ codeRange 0x124855 bytes_l124855, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24855 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124894 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124894 (addR64Imm8Effect 0x124894 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x124894 (fun s => s.RIP = 0x124894) (addR64Imm8Effect 0x124894 4 0x38) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124898 (popR64Effect 0x124898 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x124898 (popR64Effect 0x124898 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x124898 (PopPre 0x124898) (popR64Effect 0x124898 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x124899 (popR64Effect 0x124899 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x124899 (popR64Effect 0x124899 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x124899 (PopPre 0x124899) (popR64Effect 0x124899 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x12489b (popR64Effect 0x12489b 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x12489b (popR64Effect 0x12489b 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x12489b (PopPre 0x12489b) (popR64Effect 0x12489b 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x12489d (popR64Effect 0x12489d 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x12489d (popR64Effect 0x12489d 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x12489d (PopPre 0x12489d) (popR64Effect 0x12489d 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x12489f (popR64Effect 0x12489f 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x12489f (popR64Effect 0x12489f 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x12489f (PopPre 0x12489f) (popR64Effect 0x12489f 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x1248a1 (popR64Effect 0x1248a1 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x1248a1 (popR64Effect 0x1248a1 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x1248a1 (PopPre 0x1248a1) (popR64Effect 0x1248a1 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x1248a2 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x1248a2 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x1248a2 (RetPre 0x1248a2) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l124894 : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x38, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l124894 : ∀ x ∈ codeRange 0x124894 bytes_l124894, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24894 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1248a3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1248a3 (movR32Imm32Effect 0x1248a3 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x1248a3 (fun s => s.RIP = 0x1248a3) (movR32Imm32Effect 0x1248a3 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1248a8 (movR64Imm32Effect 0x1248a8 2 0x2036e0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x1248a8 (fun s => s.RIP = 0x1248a8) (movR64Imm32Effect 0x1248a8 2 0x2036e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1248af (callEffect (fun _ => 0x129c90) 0x1248b4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1248af (PushPre 0x1248af 5) (callEffect (fun _ => 0x129c90) 0x1248b4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1248b4⟩) #v[]
    (.terminate (.call ⟨.l129c90, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)] 60⟩ { target := .l1248b4, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1248a3 : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xE0, 0x36, 0x20, 0x00, 0xE8, 0xDC, 0x53, 0x00,
    0x00]

theorem code_l1248a3 : ∀ x ∈ codeRange 0x1248a3 bytes_l1248a3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x248a3 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1248b4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1248b4 (fun s => s.RIP = 0x1248b4) (fun _ => nopEffect 0x1248b4 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x1248be (fun s => s.RIP = 0x1248be) (fun _ => nopEffect 0x1248be 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1248c0, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1248b4 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x66, 0x90]

theorem code_l1248b4 : ∀ x ∈ codeRange 0x1248b4 bytes_l1248b4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x248b4 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1248c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1248c0 (pushR64Effect 0x1248c0 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x1248c0 (PushPre 0x1248c0 2) (pushR64Effect 0x1248c0 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x1248c2 (pushR64Effect 0x1248c2 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x1248c2 (PushPre 0x1248c2 2) (pushR64Effect 0x1248c2 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x1248c4 (pushR64Effect 0x1248c4 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[55, 12]
    (.letOp (n := 58) (.exec 0x1248c4 (PushPre 0x1248c4 2) (pushR64Effect 0x1248c4 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[55, 12]
    (.letOp (n := 59) (.out 0x1248c6 (pushR64Effect 0x1248c6 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[57, 3]
    (.letOp (n := 60) (.exec 0x1248c6 (PushPre 0x1248c6 1) (pushR64Effect 0x1248c6 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 61) (.out 0x1248c7 (subR64Imm32Effect 0x1248c7 4 0x98) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x1248c7 (fun s => s.RIP = 0x1248c7) (subR64Imm32Effect 0x1248c7 4 0x98) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.out 0x1248ce (movR64R64Effect 0x1248ce 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 64) (.exec 0x1248ce (fun s => s.RIP = 0x1248ce) (movR64R64Effect 0x1248ce 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 65) (.out 0x1248d1 (movR32M32Effect 0x1248d1 14 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 66) (.exec 0x1248d1 (LoadPre 0x1248d1 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1248d1 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1248d1 14 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 67) (.exec 0x1248d5 (StorePre 0x1248d5 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f)) s (0x1248d5 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1248d5 (.sib 4 none 0 (.d32 0x8f)) 0x0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 68) (.exec 0x1248e1 (StorePre 0x1248e1 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1248e1 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1248e1 (.sib 4 none 0 (.d32 0x88)) 0x0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 69) (.exec 0x1248ed (StorePre 0x1248ed 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1248ed + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1248ed (.sib 4 none 0 (.d32 0x80)) 0x0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 70) (.exec 0x1248f9 (StorePre 0x1248f9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1248f9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1248f9 (.sib 4 none 0 (.d8 0x78)) 0x0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 71) (.exec 0x124902 (StorePre 0x124902 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x124902 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x124902 (.sib 4 none 0 (.d8 0x70)) 0x0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 72) (.out 0x12490b (cmpR64Imm8Effect 0x12490b 14 0x28) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[65]
    (.letOp (n := 73) (.exec 0x12490b (fun s => s.RIP = 0x12490b) (cmpR64Imm8Effect 0x12490b 14 0x28) (Reg.operands [.gpr 14] [])) #v[65]
    (.letOp (n := 74) (.pure (condOp 3)) #v[72]
    (.terminate (.condBr (Fin.last 74) ⟨.l124996, RegMap.args [(2, 2), (3, 63), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (16, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ ⟨.l124915, RegMap.args [(2, 2), (3, 63), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (16, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l1248c0 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89,
    0xFB, 0x44, 0x8B, 0x72, 0x08, 0x48, 0xC7, 0x84, 0x24, 0x8F, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84,
    0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x70, 0x00, 0x00, 0x00, 0x00, 0x49, 0x83, 0xFE, 0x28, 0x0F,
    0x83, 0x81, 0x00, 0x00, 0x00]

theorem code_l1248c0 : ∀ x ∈ codeRange 0x1248c0 bytes_l1248c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x248c0 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124915 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124915 (leaR64Effect 0x124915 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x124915 (fun s => s.RIP = 0x124915) (leaR64Effect 0x124915 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12491a (movR64R64Effect 0x12491a 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 56) (.exec 0x12491a (fun s => s.RIP = 0x12491a) (movR64R64Effect 0x12491a 12 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x12491d (movR32R32Effect 0x12491d 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x12491d (fun s => s.RIP = 0x12491d) (movR32R32Effect 0x12491d 3 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x124920 (callEffect (fun _ => 0x127b80) 0x124925) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x124920 (PushPre 0x124920 5) (callEffect (fun _ => 0x127b80) 0x124925) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x124925⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l124925, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l124915 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0x49, 0x89, 0xF4, 0x44, 0x89, 0xF2, 0xE8, 0x5B, 0x32, 0x00, 0x00]

theorem code_l124915 : ∀ x ∈ codeRange 0x124915 bytes_l124915, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24915 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124925 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124925 (movR32M32LowEffect 0x124925 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x124925 (LoadPre 0x124925 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124925 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124925 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124929 (cmpR32Imm8Effect 0x124929 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124929 (fun s => s.RIP = 0x124929) (cmpR32Imm8Effect 0x124929 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1249bc, RegMap.args [(1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124932, RegMap.args [(1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124925 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x83, 0xF9, 0x02, 0x0F, 0x85, 0x8A, 0x00, 0x00, 0x00]

theorem code_l124925 : ∀ x ∈ codeRange 0x124925 bytes_l124925, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24925 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124932 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124932 (movR64M64Effect 0x124932 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x124932 (LoadPre 0x124932 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124932 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124932 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124937 (cmpR64R64Effect 0x124937 6 14) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 14] []) (.flag .ZF)) #v[53, 14]
    (.letOp (n := 56) (.exec 0x124937 (fun s => s.RIP = 0x124937) (cmpR64R64Effect 0x124937 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124acf, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124940, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124932 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x18, 0x4C, 0x39, 0xF6, 0x0F, 0x85, 0x8F, 0x01, 0x00, 0x00]

theorem code_l124932 : ∀ x ∈ codeRange 0x124932 bytes_l124932, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24932 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124940 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124940 (movR64M64Effect 0x124940 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x124940 (LoadPre 0x124940 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124940 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124940 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124945 (leaR64Effect 0x124945 15 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 56) (.exec 0x124945 (fun s => s.RIP = 0x124945) (leaR64Effect 0x124945 15 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x12494a (movR64R64Effect 0x12494a 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x12494a (fun s => s.RIP = 0x12494a) (movR64R64Effect 0x12494a 7 15) (Reg.operands [.gpr 15] [])) #v[55]
    (.letOp (n := 59) (.out 0x12494d (movR64R64Effect 0x12494d 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 60) (.exec 0x12494d (fun s => s.RIP = 0x12494d) (movR64R64Effect 0x12494d 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x124950 (callEffect (callMemPtr 0x124950 (.rip 0xdf47a)) (0x124950 + BitVec.ofNat 64 (callMemLen (.rip 0xdf47a)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x124950 (GoesTo (CallMemPre 0x124950 (.rip 0xdf47a)) (callEffect (callMemPtr 0x124950 (.rip 0xdf47a)) (0x124950 + BitVec.ofNat 64 (callMemLen (.rip 0xdf47a)))) 0x12a820) (callEffect (callMemPtr 0x124950 (.rip 0xdf47a)) (0x124950 + BitVec.ofNat 64 (callMemLen (.rip 0xdf47a)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x124956⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 59), (3, 3), (4, 61), (5, 5), (6, 53), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l124956, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l124940 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x10, 0x4C, 0x8D, 0x7C, 0x24, 0x70, 0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xF2,
    0xFF, 0x15, 0x7A, 0xF4, 0x0D, 0x00]

theorem code_l124940 : ∀ x ∈ codeRange 0x124940 bytes_l124940, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24940 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124956 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124956 (leaR64Effect 0x124956 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x124956 (fun s => s.RIP = 0x124956) (leaR64Effect 0x124956 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12495b (movR64R64Effect 0x12495b 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 56) (.exec 0x12495b (fun s => s.RIP = 0x12495b) (movR64R64Effect 0x12495b 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x12495e (movR64R64Effect 0x12495e 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x12495e (fun s => s.RIP = 0x12495e) (movR64R64Effect 0x12495e 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x124961 (callEffect (fun _ => 0x127fc0) 0x124966) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x124961 (PushPre 0x124961 5) (callEffect (fun _ => 0x127fc0) 0x124966) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x124966⟩) #v[]
    (.terminate (.call ⟨.l127fc0, RegMap.args [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l124966, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l124956 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x60, 0x4C, 0x89, 0xFE, 0x4C, 0x89, 0xF2, 0xE8, 0x5A, 0x36, 0x00, 0x00]

theorem code_l124956 : ∀ x ∈ codeRange 0x124956 bytes_l124956, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24956 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Sec1.LIR
