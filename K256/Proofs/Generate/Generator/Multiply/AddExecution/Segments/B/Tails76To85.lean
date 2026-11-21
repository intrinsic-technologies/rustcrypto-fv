import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point
  K256.Proofs.Generate.Generator.Multiply.AddGraph K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment76 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_76 b_l10a410_77 := by
  replay_segment 76
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3173, ⟨64, (AddGraph.w1253 s.p s.q)⟩),
      (3200, ⟨64, (AddGraph.w1257 s.p s.q)⟩),
      (3220, ⟨64, (AddGraph.w1409 s.p s.q)⟩),
      (3224, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (3243, ⟨64, (AddGraph.w1421 s.p s.q)⟩),
      (3258, ⟨64, (AddGraph.w1261 s.p s.q)⟩)]
    loads [((.stack 3), (s.fr.rsp - 512), (AddGraph.w1259 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w1267 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w1265 s.p s.q)),
      ((.stack 23), (s.fr.rsp - 352), (AddGraph.w1251 s.p s.q)),
      ((.stack 24), (s.fr.rsp - 344), (AddGraph.w1255 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment77 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_77 b_l10a410_78 := by
  replay_segment 77
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3248, ⟨64, (AddGraph.w1425 s.p s.q)⟩),
      (3256, ⟨64, (AddGraph.w1427 s.p s.q)⟩),
      (3263, ⟨64, (AddGraph.w1428 s.p s.q)⟩),
      (3265, ⟨64, (AddGraph.w1429 s.p s.q)⟩),
      (3272, ⟨64, (AddGraph.w1431 s.p s.q)⟩),
      (3274, ⟨64, (AddGraph.w1430 s.p s.q)⟩),
      (3276, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (3301, ⟨64, (AddGraph.w1441 s.p s.q)⟩),
      (3304, ⟨64, (AddGraph.w1444 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w1304 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w1426 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment78 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_78 b_l10a410_79 := by
  replay_segment 78
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3276, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (3337, ⟨64, (AddGraph.w1465 s.p s.q)⟩),
      (3345, ⟨64, (AddGraph.w1468 s.p s.q)⟩),
      (3346, ⟨64, (AddGraph.w1467 s.p s.q)⟩),
      (3350, ⟨64, (AddGraph.w1469 s.p s.q)⟩)]
    loads [((.stack 2), (s.fr.rsp - 520), (AddGraph.w1342 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w1392 s.p s.q)),
      ((.stack 13), (s.fr.rsp - 432), (AddGraph.w694 s.p s.q)),
      ((.stack 53), (s.fr.rsp - 112), (AddGraph.w195 s.p s.q)),
      ((.stack 59), (s.fr.rsp - 64), (AddGraph.w653 s.p s.q))]
    stores [((.stack 7), 1485, (s.fr.rsp - 480), (AddGraph.w1485 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment79 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_79 b_l10a410_80 := by
  replay_segment 79
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3278, ⟨64, (AddGraph.w1432 s.p s.q)⟩),
      (3341, ⟨64, (AddGraph.w1466 s.p s.q)⟩),
      (3352, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (3366, ⟨64, (AddGraph.w1474 s.p s.q)⟩),
      (3391, ⟨64, (AddGraph.w694 s.p s.q)⟩)]
    loads [((.stack 27), (s.fr.rsp - 320), (AddGraph.w789 s.p s.q)),
      ((.stack 44), (s.fr.rsp - 184), (AddGraph.w236 s.p s.q)),
      ((.stack 47), (s.fr.rsp - 160), (AddGraph.w320 s.p s.q)),
      ((.stack 52), (s.fr.rsp - 120), (AddGraph.w270 s.p s.q)),
      ((.stack 58), (s.fr.rsp - 72), (AddGraph.w728 s.p s.q))]
    stores [((.stack 10), 1497, (s.fr.rsp - 456), (AddGraph.w1497 s.p s.q)),
      ((.stack 16), 1499, (s.fr.rsp - 408), (AddGraph.w1499 s.p s.q)),
      ((.stack 0), 1501, (s.fr.rsp - 536), (AddGraph.w1501 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment80 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_80 b_l10a410_81 := by
  replay_segment 80
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3374, ⟨64, (AddGraph.w1480 s.p s.q)⟩),
      (3376, ⟨64, (AddGraph.w653 s.p s.q)⟩),
      (3391, ⟨64, (AddGraph.w694 s.p s.q)⟩),
      (3401, ⟨64, (AddGraph.w728 s.p s.q)⟩),
      (3411, ⟨64, (AddGraph.w789 s.p s.q)⟩)]
    loads [((.stack 19), (s.fr.rsp - 384), (AddGraph.w784 s.p s.q)),
      ((.stack 50), (s.fr.rsp - 136), (AddGraph.w315 s.p s.q))]
    stores [((.stack 2), 1505, (s.fr.rsp - 520), (AddGraph.w1505 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment81 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_81 b_l10a410_82 := by
  replay_segment 81
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3352, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (3370, ⟨64, (AddGraph.w308 s.p s.q)⟩),
      (3445, ⟨64, (AddGraph.w1510 s.p s.q)⟩),
      (3449, ⟨64, (AddGraph.w1514 s.p s.q)⟩),
      (3453, ⟨64, (AddGraph.w1518 s.p s.q)⟩),
      (3457, ⟨64, (AddGraph.w1522 s.p s.q)⟩),
      (3461, ⟨64, (AddGraph.w1526 s.p s.q)⟩),
      (3465, ⟨64, (AddGraph.w1527 s.p s.q)⟩),
      (3467, ⟨64, (AddGraph.w180 s.p s.q)⟩)]
    loads [((.stack 42), (s.fr.rsp - 200), (AddGraph.w424 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment82 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_82 b_l10a410_83 := by
  replay_segment 82
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3352, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (3481, ⟨64, (AddGraph.w1533 s.p s.q)⟩),
      (3485, ⟨64, (AddGraph.w1536 s.p s.q)⟩),
      (3503, ⟨64, (AddGraph.w1545 s.p s.q)⟩),
      (3505, ⟨64, (AddGraph.w1546 s.p s.q)⟩),
      (3507, ⟨64, (AddGraph.w424 s.p s.q)⟩)]
    loads [((.stack 37), (s.fr.rsp - 240), (AddGraph.w465 s.p s.q)),
      ((.stack 45), (s.fr.rsp - 176), (AddGraph.w500 s.p s.q))]
    stores [((.stack 1), 1549, (s.fr.rsp - 528), (AddGraph.w1549 s.p s.q)),
      ((.stack 26), 1550, (s.fr.rsp - 328), (AddGraph.w1550 s.p s.q)),
      ((.stack 5), 1556, (s.fr.rsp - 496), (AddGraph.w1556 s.p s.q)),
      ((.stack 22), 1557, (s.fr.rsp - 360), (AddGraph.w1557 s.p s.q)),
      ((.stack 6), 1561, (s.fr.rsp - 488), (AddGraph.w1561 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment83 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_83 b_l10a410_84 := by
  replay_segment 83
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3352, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (3491, ⟨64, (AddGraph.w1539 s.p s.q)⟩),
      (3501, ⟨64, (AddGraph.w1543 s.p s.q)⟩),
      (3521, ⟨64, (AddGraph.w1553 s.p s.q)⟩),
      (3542, ⟨64, (AddGraph.w1562 s.p s.q)⟩)]
    loads [((.stack 8), (s.fr.rsp - 472), (AddGraph.w1290 s.p s.q)),
      ((.stack 39), (s.fr.rsp - 224), (AddGraph.w543 s.p s.q)),
      ((.stack 55), (s.fr.rsp - 96), (AddGraph.w548 s.p s.q))]
    stores [((.stack 14), 1562, (s.fr.rsp - 424), (AddGraph.w1562 s.p s.q)),
      ((.stack 11), 1566, (s.fr.rsp - 448), (AddGraph.w1566 s.p s.q)),
      ((.stack 24), 1567, (s.fr.rsp - 344), (AddGraph.w1567 s.p s.q)),
      ((.stack 9), 1572, (s.fr.rsp - 464), (AddGraph.w1572 s.p s.q)),
      ((.stack 3), 1573, (s.fr.rsp - 512), (AddGraph.w1573 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment84 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_84 b_l10a410_85 := by
  replay_segment 84
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3467, ⟨64, (AddGraph.w180 s.p s.q)⟩),
      (3493, ⟨64, (AddGraph.w308 s.p s.q)⟩),
      (3573, ⟨64, (AddGraph.w1577 s.p s.q)⟩),
      (3577, ⟨64, (AddGraph.w1578 s.p s.q)⟩)]
    loads [((.stack 4), (s.fr.rsp - 504), (AddGraph.w1285 s.p s.q)),
      ((.stack 15), (s.fr.rsp - 416), (AddGraph.w1271 s.p s.q)),
      ((.stack 18), (s.fr.rsp - 392), (AddGraph.w1269 s.p s.q)),
      ((.stack 30), (s.fr.rsp - 296), (AddGraph.w1277 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment85 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_85 b_l10a410_86 := by
  replay_segment 85
    regs [(3467, ⟨64, (AddGraph.w180 s.p s.q)⟩),
      (3517, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (3579, ⟨64, (AddGraph.w1579 s.p s.q)⟩),
      (3589, ⟨64, (AddGraph.w1583 s.p s.q)⟩),
      (3599, ⟨64, (AddGraph.w1587 s.p s.q)⟩),
      (3609, ⟨64, (AddGraph.w1591 s.p s.q)⟩),
      (3615, ⟨64, (AddGraph.w1285 s.p s.q)⟩),
      (3617, ⟨64, (AddGraph.w1594 s.p s.q)⟩)]
    loads []
    stores []


theorem segments76To85 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_76 b_l10a410_86 :=
  BodySegment.trans (segment76 inc s r) <|
    BodySegment.trans (segment77 inc s r) <|
    BodySegment.trans (segment78 inc s r) <|
    BodySegment.trans (segment79 inc s r) <|
    BodySegment.trans (segment80 inc s r) <|
    BodySegment.trans (segment81 inc s r) <|
    BodySegment.trans (segment82 inc s r) <|
    BodySegment.trans (segment83 inc s r) <|
    BodySegment.trans (segment84 inc s r) <|
    segment85 inc s r

end K256.Proofs.Generate.Generator.Multiply.AddReplay
