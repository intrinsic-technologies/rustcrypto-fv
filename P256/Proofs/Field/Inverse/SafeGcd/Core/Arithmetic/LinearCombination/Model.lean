import X86Proofs.Instructions.Adc.Operation
import X86Proofs.Instructions.Mul.Operation
import X86Proofs.Instructions.Add.Operation
import P256.Proofs.Common.Instructions.Carry.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination

open X86Proofs

structure Inputs where
  a : Vector (BitVec 64) 4
  b : Vector (BitVec 64) 4
  aSign : BitVec 8
  bSign : BitVec 8
  u : BitVec 64
  v : BitVec 64

def v1b10e4 (p : Inputs) := (p.u : BitVec 64) >>> 63

def v1b10f0 (p : Inputs) := -(p.u : BitVec 64)

def v1b10fd (p : Inputs) := (v1b10f0 p : BitVec 64) ^^^ (p.u)

def v1b1100 (p : Inputs) := -((((v1b10e4 p).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b1103 (p : Inputs) := (v1b1100 p : BitVec 64) &&& (v1b10fd p)

def v1b1106 (p : Inputs) := (v1b1103 p : BitVec 64) ^^^ (p.u)

def v1b110c (p : Inputs) := (p.v : BitVec 64) >>> 63

def v1b111e (p : Inputs) := mulResult (v1b1106 p) (p.a[0])

def v1b112a (p : Inputs) := -(p.v : BitVec 64)

def v1b1130 (p : Inputs) := mulResult (v1b1106 p) (p.a[1])

def v1b113f (p : Inputs) := (v1b112a p : BitVec 64) ^^^ (p.v)

def v1b1145 (p : Inputs) := mulResult (v1b1106 p) (p.a[2])

def v1b114f (p : Inputs) := -((((v1b110c p).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b1152 (p : Inputs) := (v1b114f p : BitVec 64) &&& (v1b113f p)

def v1b1158 (p : Inputs) := mulResult (v1b1106 p) (p.a[3])

def v1b1162 (p : Inputs) := (v1b1152 p : BitVec 64) ^^^ (p.v)

def v1b1165 (p : Inputs) := addSpec ((v1b1130 p).1 : BitVec 64) ((v1b111e p).2)

def v1b1168 (p : Inputs) := adcSpec ((v1b1165 p).2.CF) ((v1b1145 p).1 : BitVec 64) ((v1b1130 p).2)

def v1b116b (p : Inputs) := adcSpec ((v1b1168 p).2.CF) ((v1b1158 p).1 : BitVec 64) ((v1b1145 p).2)

def v1b116e (p : Inputs) := adcSpec ((v1b116b p).2.CF) ((v1b1158 p).2 : BitVec 64) (0)

def v1b1175 (p : Inputs) := mulResult (v1b1162 p) (p.b[0])

def v1b1185 (p : Inputs) := mulResult (v1b1162 p) (p.b[1])

def v1b1194 (p : Inputs) := mulResult (v1b1162 p) (p.b[2])

def v1b11a3 (p : Inputs) := ((v1b10e4 p).setWidth 8 : BitVec 8) ^^^ (p.aSign)

def v1b11af (p : Inputs) := mulResult (v1b1162 p) (p.b[3])

def v1b11b3 (p : Inputs) := addSpec ((v1b1185 p).1 : BitVec 64) ((v1b1175 p).2)

def v1b11b8 (p : Inputs) := adcSpec ((v1b11b3 p).2.CF) ((v1b1194 p).1 : BitVec 64) ((v1b1185 p).2)

def v1b11c5 (p : Inputs) := adcSpec ((v1b11b8 p).2.CF) ((v1b11af p).1 : BitVec 64) ((v1b1194 p).2)

def v1b11c8 (p : Inputs) := adcSpec ((v1b11c5 p).2.CF) ((v1b11af p).2 : BitVec 64) (0)

def v1b11d6 (p : Inputs) := ((v1b110c p).setWidth 8 : BitVec 8) ^^^ (p.bSign)

def v1b11e2 (p : Inputs) := ((((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64).setWidth 8 : BitVec 8) ^^^ ((mergeGPR 8 (v1b11a3 p) (v1b10e4 p)).setWidth 8)

def v1b11ea (p : Inputs) := ((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8 : BitVec 8) ^^^ (1)

def v1b11f6 (p : Inputs) := -((v1b1175 p).1 : BitVec 64)

def v1b11fe (p : Inputs) := P256.Proofs.Common.Instructions.Carry.sbbSpec ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v1b11b3 p).1) (BitVec.ofBool (decide (((v1b1175 p).1 : BitVec 64) ≠ 0)))

def v1b1207 (p : Inputs) := P256.Proofs.Common.Instructions.Carry.sbbSpec ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v1b11b8 p).1) (BitVec.ofBool ((v1b11fe p).2.CF))

def v1b120f (p : Inputs) := P256.Proofs.Common.Instructions.Carry.sbbSpec ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v1b11c5 p).1) (BitVec.ofBool ((v1b1207 p).2.CF))

def v1b1229 (p : Inputs) := (v1b11f6 p : BitVec 64) ^^^ ((v1b1175 p).1)

def v1b1230 (p : Inputs) := -((((mergeGPR 8 (v1b11ea p) (mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b1233 (p : Inputs) := (v1b1230 p : BitVec 64) &&& (v1b1229 p)

def v1b1236 (p : Inputs) := (v1b1233 p : BitVec 64) ^^^ ((v1b1175 p).1)

def v1b1240 (p : Inputs) := ((v1b11fe p).1 : BitVec 64) ^^^ ((v1b11b3 p).1)

def v1b1248 (p : Inputs) := -((((mergeGPR 8 (v1b11ea p) (mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b124b (p : Inputs) := (v1b1248 p : BitVec 64) &&& (v1b1240 p)

def v1b124e (p : Inputs) := (v1b124b p : BitVec 64) ^^^ ((v1b11b3 p).1)

def v1b125d (p : Inputs) := ((v1b1207 p).1 : BitVec 64) ^^^ ((v1b11b8 p).1)

def v1b1264 (p : Inputs) := -((((mergeGPR 8 (v1b11ea p) (mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b1267 (p : Inputs) := (v1b1264 p : BitVec 64) &&& (v1b125d p)

def v1b126a (p : Inputs) := (v1b1267 p : BitVec 64) ^^^ ((v1b11b8 p).1)

def v1b1271 (p : Inputs) := ((v1b120f p).1 : BitVec 64) ^^^ ((v1b11c5 p).1)

def v1b1279 (p : Inputs) := -((((mergeGPR 8 (v1b11ea p) (mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b127c (p : Inputs) := (v1b1279 p : BitVec 64) &&& (v1b1271 p)

def v1b127f (p : Inputs) := (v1b127c p : BitVec 64) ^^^ ((v1b11c5 p).1)

def v1b128c (p : Inputs) := ((v1b111e p).1 : BitVec 64) - (v1b1236 p)

def v1b128f (p : Inputs) := ~~~((v1b111e p).1 : BitVec 64)

def v1b1295 (p : Inputs) := (v1b1236 p : BitVec 64) &&& (v1b128f p)

def v1b1298 (p : Inputs) := (v1b128f p : BitVec 64) ||| (v1b1236 p)

def v1b129b (p : Inputs) := (v1b1298 p : BitVec 64) &&& (v1b128c p)

def v1b129e (p : Inputs) := (v1b129b p : BitVec 64) ||| (v1b1295 p)

def v1b12a1 (p : Inputs) := (v1b129e p : BitVec 64) >>> 63

def v1b12b4 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1b12a1 p)

def v1b12bb (p : Inputs) := ((v1b1165 p).1 : BitVec 64) - (v1b124e p)

def v1b12be (p : Inputs) := (v1b12b4 p : BitVec 64).sshiftRight 63

def v1b12c2 (p : Inputs) := addSpec (v1b12be p : BitVec 64) (v1b12bb p)

def v1b12c5 (p : Inputs) := ~~~((v1b1165 p).1 : BitVec 64)

def v1b12cb (p : Inputs) := (v1b124e p : BitVec 64) &&& (v1b12c5 p)

def v1b12ce (p : Inputs) := (v1b12c5 p : BitVec 64) ||| (v1b124e p)

def v1b12d1 (p : Inputs) := (v1b12ce p : BitVec 64) &&& ((v1b12c2 p).1)

def v1b12d4 (p : Inputs) := (v1b12d1 p : BitVec 64) ||| (v1b12cb p)

def v1b12d7 (p : Inputs) := (v1b12d4 p : BitVec 64) >>> 63

def v1b12e2 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1b12d7 p)

def v1b12e9 (p : Inputs) := ((v1b1168 p).1 : BitVec 64) - (v1b126a p)

def v1b12ec (p : Inputs) := (v1b12e2 p : BitVec 64).sshiftRight 63

def v1b12f0 (p : Inputs) := addSpec (v1b12ec p : BitVec 64) (v1b12e9 p)

def v1b12f3 (p : Inputs) := ~~~((v1b1168 p).1 : BitVec 64)

def v1b12f9 (p : Inputs) := (v1b126a p : BitVec 64) &&& (v1b12f3 p)

def v1b12fc (p : Inputs) := (v1b12f3 p : BitVec 64) ||| (v1b126a p)

def v1b12ff (p : Inputs) := (v1b12fc p : BitVec 64) &&& ((v1b12f0 p).1)

def v1b1302 (p : Inputs) := (v1b12ff p : BitVec 64) ||| (v1b12f9 p)

def v1b1305 (p : Inputs) := (v1b1302 p : BitVec 64) >>> 63

def v1b1310 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1b1305 p)

def v1b1317 (p : Inputs) := ((v1b116b p).1 : BitVec 64) - (v1b127f p)

def v1b131a (p : Inputs) := (v1b1310 p : BitVec 64).sshiftRight 63

def v1b131e (p : Inputs) := addSpec (v1b131a p : BitVec 64) (v1b1317 p)

def v1b1321 (p : Inputs) := ~~~((v1b116b p).1 : BitVec 64)

def v1b1327 (p : Inputs) := (v1b127f p : BitVec 64) &&& (v1b1321 p)

def v1b132a (p : Inputs) := (v1b1321 p : BitVec 64) ||| (v1b127f p)

def v1b132d (p : Inputs) := (v1b132a p : BitVec 64) &&& ((v1b131e p).1)

def v1b1330 (p : Inputs) := (v1b132d p : BitVec 64) ||| (v1b1327 p)

def v1b1333 (p : Inputs) := (v1b1330 p : BitVec 64) >>> 63

def v1b133d (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1b1333 p)

def v1b1346 (p : Inputs) := (((((if !((v1b120f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32) &&& (1)

def v1b1352 (p : Inputs) := ~~~((v1b11c8 p).1 : BitVec 64)

def v1b1355 (p : Inputs) := addSpec (v1b1352 p : BitVec 64) ((v1b1346 p : BitVec 32).setWidth 64)

def v1b1358 (p : Inputs) := ((v1b1355 p).1 : BitVec 64) ^^^ ((v1b11c8 p).1)

def v1b135b (p : Inputs) := -((((mergeGPR 8 (v1b11ea p) (mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b135e (p : Inputs) := (v1b135b p : BitVec 64) &&& (v1b1358 p)

def v1b1361 (p : Inputs) := (v1b135e p : BitVec 64) ^^^ ((v1b11c8 p).1)

def v1b1367 (p : Inputs) := ((v1b116e p).1 : BitVec 64) - (v1b1361 p)

def v1b136a (p : Inputs) := ~~~((v1b116e p).1 : BitVec 64)

def v1b1370 (p : Inputs) := (v1b1361 p : BitVec 64) &&& (v1b136a p)

def v1b1373 (p : Inputs) := (v1b136a p : BitVec 64) ||| (v1b1361 p)

def v1b1376 (p : Inputs) := (v1b133d p : BitVec 64).sshiftRight 63

def v1b137a (p : Inputs) := addSpec (v1b1376 p : BitVec 64) (v1b1367 p)

def v1b137d (p : Inputs) := (v1b1373 p : BitVec 64) &&& ((v1b137a p).1)

def v1b1380 (p : Inputs) := (v1b137d p : BitVec 64) ||| (v1b1370 p)

def v1b1383 (p : Inputs) := (v1b1380 p : BitVec 64) >>> 63

def v1b1393 (p : Inputs) := (((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 8 : BitVec 8) &&& (1)

def v1b13ab (p : Inputs) := -(v1b128c p : BitVec 64)

def v1b13b4 (p : Inputs) := P256.Proofs.Common.Instructions.Carry.sbbSpec ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v1b12c2 p).1) (BitVec.ofBool (decide ((v1b128c p : BitVec 64) ≠ 0)))

def v1b13bd (p : Inputs) := P256.Proofs.Common.Instructions.Carry.sbbSpec ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v1b12f0 p).1) (BitVec.ofBool ((v1b13b4 p).2.CF))

def v1b13c0 (p : Inputs) := P256.Proofs.Common.Instructions.Carry.sbbSpec ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v1b131e p).1) (BitVec.ofBool ((v1b13bd p).2.CF))

def v1b13c6 (p : Inputs) := ~~~((v1b137a p).1 : BitVec 64)

def v1b13d4 (p : Inputs) := (((((if !((v1b13c0 p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32) &&& (1)

def v1b13d7 (p : Inputs) := addSpec ((v1b13d4 p : BitVec 32).setWidth 64 : BitVec 64) (v1b13c6 p)

def v1b13e0 (p : Inputs) := (v1b13ab p : BitVec 64) ^^^ (v1b128c p)

def v1b13e7 (p : Inputs) := -((((((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b13ea (p : Inputs) := (v1b13e7 p : BitVec 64) &&& (v1b13e0 p)

def v1b13ed (p : Inputs) := (v1b13ea p : BitVec 64) ^^^ (v1b128c p)

def v1b13f7 (p : Inputs) := ((v1b13b4 p).1 : BitVec 64) ^^^ ((v1b12c2 p).1)

def v1b13fa (p : Inputs) := -((((((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b13fd (p : Inputs) := (v1b13fa p : BitVec 64) &&& (v1b13f7 p)

def v1b1400 (p : Inputs) := (v1b13fd p : BitVec 64) ^^^ ((v1b12c2 p).1)

def v1b140b (p : Inputs) := ((v1b13bd p).1 : BitVec 64) ^^^ ((v1b12f0 p).1)

def v1b140e (p : Inputs) := -((((((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b1411 (p : Inputs) := (v1b140e p : BitVec 64) &&& (v1b140b p)

def v1b1414 (p : Inputs) := (v1b1411 p : BitVec 64) ^^^ ((v1b12f0 p).1)

def v1b141f (p : Inputs) := ((v1b13c0 p).1 : BitVec 64) ^^^ ((v1b131e p).1)

def v1b1422 (p : Inputs) := -((((((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b1425 (p : Inputs) := (v1b1422 p : BitVec 64) &&& (v1b141f p)

def v1b1428 (p : Inputs) := (v1b1425 p : BitVec 64) ^^^ ((v1b131e p).1)

def v1b1436 (p : Inputs) := ((v1b13d7 p).1 : BitVec 64) ^^^ ((v1b137a p).1)

def v1b1439 (p : Inputs) := -((((((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b143c (p : Inputs) := (v1b1439 p : BitVec 64) &&& (v1b1436 p)

def v1b143f (p : Inputs) := (v1b143c p : BitVec 64) ^^^ ((v1b137a p).1)

def v1b1447 (p : Inputs) := ((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 8 : BitVec 8) &&& ((((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8)

def v1b1449 (p : Inputs) := ((((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8 : BitVec 8) ^^^ (1)

def v1b144c (p : Inputs) := ((mergeGPR 8 (v1b1449 p) (((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64)).setWidth 8 : BitVec 8) &&& ((mergeGPR 8 (v1b11a3 p) (v1b10e4 p)).setWidth 8)

def v1b1466 (p : Inputs) := ((mergeGPR 8 (v1b1447 p) (mergeGPR 8 (v1b11d6 p) (v1b110c p))).setWidth 8 : BitVec 8) ||| ((mergeGPR 8 (v1b144c p) (mergeGPR 8 (v1b1449 p) (((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64))).setWidth 8)

def resultWords (p : Inputs) : Vector (BitVec 64) 5 :=
  #v[v1b13ed p, v1b1400 p, v1b1414 p, v1b1428 p, v1b143f p]

def resultSign (p : Inputs) : BitVec 8 :=
  (mergeGPR 8 (v1b1466 p) (mergeGPR 8 (v1b1447 p) (mergeGPR 8 (v1b11d6 p) (v1b110c p)))).setWidth 8

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
