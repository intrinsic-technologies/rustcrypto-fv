import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point
  K256.Proofs.Generate.Generator.Multiply.AddGraph K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment65 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_65 b_l10a410_66 := by
  replay_segment 65
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2767, ⟨64, (AddGraph.w1231 s.p s.q)⟩),
      (2799, ⟨64, (AddGraph.w1242 s.p s.q)⟩),
      (2805, ⟨64, (AddGraph.w1243 s.p s.q)⟩)]
    loads [((.stack 14), (s.fr.rsp - 424), (AddGraph.w23 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w21 s.p s.q)),
      ((.stack 19), (s.fr.rsp - 384), (AddGraph.w784 s.p s.q)),
      ((.stack 21), (s.fr.rsp - 368), (AddGraph.w9 s.p s.q)),
      ((.stack 23), (s.fr.rsp - 352), (AddGraph.w20 s.p s.q)),
      ((.stack 24), (s.fr.rsp - 344), (AddGraph.w22 s.p s.q)),
      ((.stack 26), (s.fr.rsp - 328), (AddGraph.w19 s.p s.q)),
      ((.stack 28), (s.fr.rsp - 312), (AddGraph.w12 s.p s.q)),
      ((.stack 31), (s.fr.rsp - 288), (AddGraph.w10 s.p s.q)),
      ((.stack 39), (s.fr.rsp - 224), (AddGraph.w543 s.p s.q)),
      ((.stack 43), (s.fr.rsp - 192), (AddGraph.w11 s.p s.q)),
      ((.stack 56), (s.fr.rsp - 88), (AddGraph.w13 s.p s.q))]
    stores [((.stack 4), 1245, (s.fr.rsp - 504), (AddGraph.w1245 s.p s.q)),
      ((.stack 8), 1248, (s.fr.rsp - 472), (AddGraph.w1248 s.p s.q)),
      ((.stack 16), 1253, (s.fr.rsp - 408), (AddGraph.w1253 s.p s.q)),
      ((.stack 24), 1255, (s.fr.rsp - 344), (AddGraph.w1255 s.p s.q)),
      ((.stack 14), 1257, (s.fr.rsp - 424), (AddGraph.w1257 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment66 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_66 b_l10a410_67 := by
  replay_segment 66
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2777, ⟨64, (AddGraph.w1235 s.p s.q)⟩),
      (2787, ⟨64, (AddGraph.w1238 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w35 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w34 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w36 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w38 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w37 s.p s.q)),
      ((.stack 20), (s.fr.rsp - 376), (AddGraph.w26 s.p s.q)),
      ((.stack 25), (s.fr.rsp - 336), (AddGraph.w27 s.p s.q)),
      ((.stack 34), (s.fr.rsp - 264), (AddGraph.w28 s.p s.q)),
      ((.stack 40), (s.fr.rsp - 216), (AddGraph.w24 s.p s.q)),
      ((.stack 41), (s.fr.rsp - 208), (AddGraph.w25 s.p s.q))]
    stores [((.stack 3), 1259, (s.fr.rsp - 512), (AddGraph.w1259 s.p s.q)),
      ((.stack 1), 1261, (s.fr.rsp - 528), (AddGraph.w1261 s.p s.q)),
      ((.stack 6), 1263, (s.fr.rsp - 488), (AddGraph.w1263 s.p s.q)),
      ((.stack 18), 1269, (s.fr.rsp - 392), (AddGraph.w1269 s.p s.q)),
      ((.stack 15), 1271, (s.fr.rsp - 416), (AddGraph.w1271 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment67 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_67 b_l10a410_68 := by
  replay_segment 67
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2797, ⟨64, (AddGraph.w1241 s.p s.q)⟩),
      (2821, ⟨64, (AddGraph.w1249 s.p s.q)⟩),
      (2825, ⟨64, (AddGraph.w1251 s.p s.q)⟩),
      (2829, ⟨64, (AddGraph.w1253 s.p s.q)⟩),
      (2834, ⟨64, (AddGraph.w1255 s.p s.q)⟩),
      (2844, ⟨64, (AddGraph.w1259 s.p s.q)⟩),
      (2849, ⟨64, (AddGraph.w1261 s.p s.q)⟩),
      (2854, ⟨64, (AddGraph.w1263 s.p s.q)⟩),
      (2859, ⟨64, (AddGraph.w1265 s.p s.q)⟩),
      (2870, ⟨64, (AddGraph.w1000 s.p s.q)⟩)]
    loads []
    stores [((.stack 11), 1265, (s.fr.rsp - 448), (AddGraph.w1265 s.p s.q)),
      ((.stack 26), 1249, (s.fr.rsp - 328), (AddGraph.w1249 s.p s.q)),
      ((.stack 0), 1273, (s.fr.rsp - 536), (AddGraph.w1273 s.p s.q)),
      ((.stack 2), 1274, (s.fr.rsp - 520), (AddGraph.w1274 s.p s.q)),
      ((.stack 23), 1251, (s.fr.rsp - 352), (AddGraph.w1251 s.p s.q)),
      ((.stack 10), 1276, (s.fr.rsp - 456), (AddGraph.w1276 s.p s.q)),
      ((.stack 7), 1275, (s.fr.rsp - 480), (AddGraph.w1275 s.p s.q)),
      ((.stack 30), 1277, (s.fr.rsp - 296), (AddGraph.w1277 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment68 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_68 b_l10a410_69 := by
  replay_segment 68
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2839, ⟨64, (AddGraph.w1257 s.p s.q)⟩),
      (2863, ⟨64, (AddGraph.w1267 s.p s.q)⟩),
      (2897, ⟨64, (AddGraph.w1000 s.p s.q)⟩),
      (2904, ⟨64, (AddGraph.w1279 s.p s.q)⟩),
      (2906, ⟨64, (AddGraph.w1280 s.p s.q)⟩),
      (2910, ⟨64, (AddGraph.w1282 s.p s.q)⟩),
      (2911, ⟨64, (AddGraph.w1281 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w1273 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w1274 s.p s.q)),
      ((.stack 4), (s.fr.rsp - 504), (AddGraph.w1245 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w1275 s.p s.q)),
      ((.stack 8), (s.fr.rsp - 472), (AddGraph.w1248 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w1276 s.p s.q))]
    stores [((.stack 9), 1267, (s.fr.rsp - 464), (AddGraph.w1267 s.p s.q)),
      ((.stack 4), 1285, (s.fr.rsp - 504), (AddGraph.w1285 s.p s.q)),
      ((.stack 8), 1290, (s.fr.rsp - 472), (AddGraph.w1290 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment69 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_69 b_l10a410_70 := by
  replay_segment 69
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2825, ⟨64, (AddGraph.w1251 s.p s.q)⟩),
      (2863, ⟨64, (AddGraph.w1267 s.p s.q)⟩),
      (2875, ⟨64, (AddGraph.w1265 s.p s.q)⟩),
      (2881, ⟨64, (AddGraph.w1249 s.p s.q)⟩),
      (2923, ⟨64, (AddGraph.w1284 s.p s.q)⟩),
      (2925, ⟨64, (AddGraph.w1283 s.p s.q)⟩),
      (2934, ⟨64, (AddGraph.w1289 s.p s.q)⟩),
      (2935, ⟨64, (AddGraph.w1288 s.p s.q)⟩),
      (2950, ⟨64, (AddGraph.w1300 s.p s.q)⟩),
      (2953, ⟨64, (AddGraph.w1303 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w1261 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w1263 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w1253 s.p s.q)),
      ((.stack 24), (s.fr.rsp - 344), (AddGraph.w1255 s.p s.q))]
    stores [((.stack 0), 1304, (s.fr.rsp - 536), (AddGraph.w1304 s.p s.q)),
      ((.stack 2), 1310, (s.fr.rsp - 520), (AddGraph.w1310 s.p s.q)),
      ((.stack 7), 1311, (s.fr.rsp - 480), (AddGraph.w1311 s.p s.q)),
      ((.stack 10), 1312, (s.fr.rsp - 456), (AddGraph.w1312 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment70 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_70 b_l10a410_71 := by
  replay_segment 70
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2961, ⟨64, (AddGraph.w1308 s.p s.q)⟩),
      (2978, ⟨64, (AddGraph.w1313 s.p s.q)⟩),
      (2987, ⟨64, (AddGraph.w1314 s.p s.q)⟩),
      (2989, ⟨64, (AddGraph.w1315 s.p s.q)⟩),
      (2991, ⟨64, (AddGraph.w1261 s.p s.q)⟩),
      (2993, ⟨64, (AddGraph.w1255 s.p s.q)⟩)]
    loads [((.stack 2), (s.fr.rsp - 520), (AddGraph.w1310 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w1259 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w1311 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w1312 s.p s.q)),
      ((.stack 14), (s.fr.rsp - 424), (AddGraph.w1257 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment71 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_71 b_l10a410_72 := by
  replay_segment 71
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2963, ⟨64, (AddGraph.w1309 s.p s.q)⟩),
      (3002, ⟨64, (AddGraph.w1259 s.p s.q)⟩),
      (3019, ⟨64, (AddGraph.w1321 s.p s.q)⟩),
      (3020, ⟨64, (AddGraph.w1320 s.p s.q)⟩),
      (3037, ⟨64, (AddGraph.w1334 s.p s.q)⟩),
      (3040, ⟨64, (AddGraph.w1337 s.p s.q)⟩)]
    loads [((.stack 9), (s.fr.rsp - 464), (AddGraph.w1267 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w1265 s.p s.q)),
      ((.stack 23), (s.fr.rsp - 352), (AddGraph.w1251 s.p s.q)),
      ((.stack 26), (s.fr.rsp - 328), (AddGraph.w1249 s.p s.q))]
    stores [((.stack 2), 1342, (s.fr.rsp - 520), (AddGraph.w1342 s.p s.q)),
      ((.stack 7), 1348, (s.fr.rsp - 480), (AddGraph.w1348 s.p s.q)),
      ((.stack 10), 1349, (s.fr.rsp - 456), (AddGraph.w1349 s.p s.q)),
      ((.stack 5), 1350, (s.fr.rsp - 496), (AddGraph.w1350 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment72 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_72 b_l10a410_73 := by
  replay_segment 72
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2982, ⟨64, (AddGraph.w1253 s.p s.q)⟩),
      (2993, ⟨64, (AddGraph.w1255 s.p s.q)⟩),
      (3006, ⟨64, (AddGraph.w1257 s.p s.q)⟩),
      (3053, ⟨64, (AddGraph.w1346 s.p s.q)⟩),
      (3057, ⟨64, (AddGraph.w1347 s.p s.q)⟩),
      (3078, ⟨64, (AddGraph.w1351 s.p s.q)⟩),
      (3080, ⟨64, (AddGraph.w1265 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w1261 s.p s.q)),
      ((.stack 5), (s.fr.rsp - 496), (AddGraph.w1350 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w1263 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment73 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_73 b_l10a410_74 := by
  replay_segment 73
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3061, ⟨64, (AddGraph.w1249 s.p s.q)⟩),
      (3072, ⟨64, (AddGraph.w1251 s.p s.q)⟩),
      (3091, ⟨64, (AddGraph.w1354 s.p s.q)⟩),
      (3102, ⟨64, (AddGraph.w1261 s.p s.q)⟩),
      (3124, ⟨64, (AddGraph.w1371 s.p s.q)⟩),
      (3127, ⟨64, (AddGraph.w1374 s.p s.q)⟩)]
    loads [((.stack 3), (s.fr.rsp - 512), (AddGraph.w1259 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w1348 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w1349 s.p s.q))]
    stores [((.stack 10), 1386, (s.fr.rsp - 456), (AddGraph.w1386 s.p s.q)),
      ((.stack 5), 1387, (s.fr.rsp - 496), (AddGraph.w1387 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment74 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_74 b_l10a410_75 := by
  replay_segment 74
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3068, ⟨64, (AddGraph.w1267 s.p s.q)⟩),
      (3080, ⟨64, (AddGraph.w1265 s.p s.q)⟩),
      (3153, ⟨64, (AddGraph.w1381 s.p s.q)⟩)]
    loads [((.stack 6), (s.fr.rsp - 488), (AddGraph.w1263 s.p s.q)),
      ((.stack 14), (s.fr.rsp - 424), (AddGraph.w1257 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w1253 s.p s.q)),
      ((.stack 24), (s.fr.rsp - 344), (AddGraph.w1255 s.p s.q))]
    stores [((.stack 7), 1392, (s.fr.rsp - 480), (AddGraph.w1392 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment75 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_75 b_l10a410_76 := by
  replay_segment 75
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3129, ⟨64, (AddGraph.w1375 s.p s.q)⟩),
      (3151, ⟨64, (AddGraph.w1385 s.p s.q)⟩),
      (3167, ⟨64, (AddGraph.w1388 s.p s.q)⟩),
      (3169, ⟨64, (AddGraph.w1389 s.p s.q)⟩),
      (3182, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (3196, ⟨64, (AddGraph.w1263 s.p s.q)⟩),
      (3210, ⟨64, (AddGraph.w1401 s.p s.q)⟩),
      (3213, ⟨64, (AddGraph.w1404 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w1261 s.p s.q)),
      ((.stack 5), (s.fr.rsp - 496), (AddGraph.w1387 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w1386 s.p s.q)),
      ((.stack 26), (s.fr.rsp - 328), (AddGraph.w1249 s.p s.q))]
    stores [((.stack 6), 1426, (s.fr.rsp - 488), (AddGraph.w1426 s.p s.q))]


theorem segments65To75 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_65 b_l10a410_76 :=
  BodySegment.trans (segment65 inc s r) <|
    BodySegment.trans (segment66 inc s r) <|
    BodySegment.trans (segment67 inc s r) <|
    BodySegment.trans (segment68 inc s r) <|
    BodySegment.trans (segment69 inc s r) <|
    BodySegment.trans (segment70 inc s r) <|
    BodySegment.trans (segment71 inc s r) <|
    BodySegment.trans (segment72 inc s r) <|
    BodySegment.trans (segment73 inc s r) <|
    BodySegment.trans (segment74 inc s r) <|
    segment75 inc s r

end K256.Proofs.Generate.Generator.Multiply.AddReplay
