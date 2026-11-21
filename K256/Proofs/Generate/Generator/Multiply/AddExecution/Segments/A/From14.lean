import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point
  K256.Proofs.Generate.Generator.Multiply.AddGraph K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment14 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_14 b_l10a410_15 := by
  replay_segment 14
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (563, ⟨64, (AddGraph.w279 s.p s.q)⟩),
      (568, ⟨64, (AddGraph.w283 s.p s.q)⟩),
      (605, ⟨64, (AddGraph.w301 s.p s.q)⟩),
      (607, ⟨64, (AddGraph.w300 s.p s.q)⟩),
      (618, ⟨64, (AddGraph.w307 s.p s.q)⟩),
      (620, ⟨64, (AddGraph.w306 s.p s.q)⟩),
      (626, ⟨64, (AddGraph.w309 s.p s.q)⟩),
      (628, ⟨64, (AddGraph.w18 s.p s.q)⟩),
      (634, ⟨64, (AddGraph.w313 s.p s.q)⟩),
      (635, ⟨64, (AddGraph.w312 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w294 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w288 s.p s.q)),
      ((.stack 4), (s.fr.rsp - 504), (AddGraph.w287 s.p s.q)),
      ((.stack 8), (s.fr.rsp - 472), (AddGraph.w295 s.p s.q))]
    stores [((.stack 30), 18, (s.fr.rsp - 296), (AddGraph.w18 s.p s.q)),
      ((.stack 50), 315, (s.fr.rsp - 136), (AddGraph.w315 s.p s.q)),
      ((.stack 47), 320, (s.fr.rsp - 160), (AddGraph.w320 s.p s.q)),
      ((.stack 4), 333, (s.fr.rsp - 504), (AddGraph.w333 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment15 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_15 b_l10a410_16 := by
  replay_segment 15
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (572, ⟨64, (AddGraph.w14 s.p s.q)⟩),
      (596, ⟨64, (AddGraph.w16 s.p s.q)⟩),
      (630, ⟨64, (AddGraph.w33 s.p s.q)⟩),
      (640, ⟨64, (AddGraph.w313 s.p s.q)⟩),
      (642, ⟨64, (AddGraph.w312 s.p s.q)⟩),
      (654, ⟨64, (AddGraph.w318 s.p s.q)⟩),
      (672, ⟨64, (AddGraph.w332 s.p s.q)⟩),
      (674, ⟨64, (AddGraph.w333 s.p s.q)⟩),
      (675, Value.ofBool (addSpec (AddGraph.w319 s.p s.q) (AddGraph.w329 s.p s.q)).2.CF)]
    loads [((.stack 2), (s.fr.rsp - 520), (AddGraph.w30 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w32 s.p s.q)),
      ((.stack 15), (s.fr.rsp - 416), (AddGraph.w31 s.p s.q)),
      ((.stack 17), (s.fr.rsp - 400), (AddGraph.w17 s.p s.q)),
      ((.stack 22), (s.fr.rsp - 360), (AddGraph.w15 s.p s.q))]
    stores [((.stack 32), 33, (s.fr.rsp - 280), (AddGraph.w33 s.p s.q)),
      ((.stack 3), 340, (s.fr.rsp - 512), (AddGraph.w340 s.p s.q)),
      ((.stack 1), 341, (s.fr.rsp - 528), (AddGraph.w341 s.p s.q)),
      ((.stack 8), 342, (s.fr.rsp - 472), (AddGraph.w342 s.p s.q)),
      ((.stack 29), 343, (s.fr.rsp - 304), (AddGraph.w343 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment16 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_16 b_l10a410_17 := by
  replay_segment 16
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (637, ⟨64, (AddGraph.w18 s.p s.q)⟩),
      (680, ⟨64, (AddGraph.w337 s.p s.q)⟩),
      (708, ⟨64, (AddGraph.w345 s.p s.q)⟩),
      (710, ⟨64, (AddGraph.w346 s.p s.q)⟩),
      (712, ⟨64, (AddGraph.w30 s.p s.q)⟩),
      (714, ⟨64, (AddGraph.w17 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w29 s.p s.q)),
      ((.stack 1), (s.fr.rsp - 528), (AddGraph.w341 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w340 s.p s.q)),
      ((.stack 8), (s.fr.rsp - 472), (AddGraph.w342 s.p s.q)),
      ((.stack 29), (s.fr.rsp - 304), (AddGraph.w343 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment17 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_17 b_l10a410_18 := by
  replay_segment 17
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (630, ⟨64, (AddGraph.w33 s.p s.q)⟩),
      (682, ⟨64, (AddGraph.w338 s.p s.q)⟩),
      (694, ⟨64, (AddGraph.w15 s.p s.q)⟩),
      (723, ⟨64, (AddGraph.w29 s.p s.q)⟩),
      (739, ⟨64, (AddGraph.w351 s.p s.q)⟩),
      (759, ⟨64, (AddGraph.w368 s.p s.q)⟩),
      (761, ⟨64, (AddGraph.w369 s.p s.q)⟩),
      (762, Value.ofBool (addSpec (AddGraph.w352 s.p s.q) (AddGraph.w365 s.p s.q)).2.CF)]
    loads [((.stack 5), (s.fr.rsp - 496), (AddGraph.w16 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w32 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w14 s.p s.q))]
    stores [((.stack 39), 373, (s.fr.rsp - 224), (AddGraph.w373 s.p s.q)),
      ((.stack 3), 381, (s.fr.rsp - 512), (AddGraph.w381 s.p s.q)),
      ((.stack 1), 382, (s.fr.rsp - 528), (AddGraph.w382 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment18 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_18 b_l10a410_19 := by
  replay_segment 18
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (701, ⟨64, (AddGraph.w31 s.p s.q)⟩),
      (714, ⟨64, (AddGraph.w17 s.p s.q)⟩),
      (774, ⟨64, (AddGraph.w378 s.p s.q)⟩),
      (776, ⟨64, (AddGraph.w379 s.p s.q)⟩),
      (794, ⟨64, (AddGraph.w383 s.p s.q)⟩),
      (802, ⟨64, (AddGraph.w385 s.p s.q)⟩),
      (803, ⟨64, (AddGraph.w384 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w382 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w30 s.p s.q)),
      ((.stack 30), (s.fr.rsp - 296), (AddGraph.w18 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment19 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_19 b_l10a410_20 := by
  replay_segment 19
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (780, ⟨64, (AddGraph.w14 s.p s.q)⟩),
      (785, ⟨64, (AddGraph.w380 s.p s.q)⟩),
      (809, ⟨64, (AddGraph.w386 s.p s.q)⟩),
      (820, ⟨64, (AddGraph.w30 s.p s.q)⟩),
      (849, ⟨64, (AddGraph.w408 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w29 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w381 s.p s.q)),
      ((.stack 22), (s.fr.rsp - 360), (AddGraph.w15 s.p s.q)),
      ((.stack 32), (s.fr.rsp - 280), (AddGraph.w33 s.p s.q))]
    stores [((.stack 3), 418, (s.fr.rsp - 512), (AddGraph.w418 s.p s.q)),
      ((.stack 1), 419, (s.fr.rsp - 528), (AddGraph.w419 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment20 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_20 b_l10a410_21 := by
  replay_segment 20
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (796, ⟨64, (AddGraph.w32 s.p s.q)⟩),
      (800, ⟨64, (AddGraph.w16 s.p s.q)⟩),
      (847, ⟨64, (AddGraph.w407 s.p s.q)⟩),
      (869, ⟨64, (AddGraph.w413 s.p s.q)⟩),
      (891, ⟨64, (AddGraph.w33 s.p s.q)⟩)]
    loads [((.stack 15), (s.fr.rsp - 416), (AddGraph.w31 s.p s.q)),
      ((.stack 17), (s.fr.rsp - 400), (AddGraph.w17 s.p s.q)),
      ((.stack 30), (s.fr.rsp - 296), (AddGraph.w18 s.p s.q))]
    stores [((.stack 42), 424, (s.fr.rsp - 200), (AddGraph.w424 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment21 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_21 b_l10a410_22 := by
  replay_segment 21
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (867, ⟨64, (AddGraph.w417 s.p s.q)⟩),
      (880, ⟨64, (AddGraph.w15 s.p s.q)⟩),
      (885, ⟨64, (AddGraph.w420 s.p s.q)⟩),
      (887, ⟨64, (AddGraph.w421 s.p s.q)⟩),
      (916, ⟨64, (AddGraph.w31 s.p s.q)⟩),
      (933, ⟨64, (AddGraph.w437 s.p s.q)⟩),
      (935, ⟨64, (AddGraph.w438 s.p s.q)⟩),
      (936, Value.ofBool (addSpec (AddGraph.w434 s.p s.q) (AddGraph.w407 s.p s.q)).2.CF)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w419 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w30 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w418 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w14 s.p s.q))]
    stores [((.stack 3), 459, (s.fr.rsp - 512), (AddGraph.w459 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment22 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_22 b_l10a410_23 := by
  replay_segment 22
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (889, ⟨64, (AddGraph.w33 s.p s.q)⟩),
      (907, ⟨64, (AddGraph.w17 s.p s.q)⟩),
      (920, ⟨64, (AddGraph.w18 s.p s.q)⟩),
      (940, ⟨64, (AddGraph.w442 s.p s.q)⟩),
      (942, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (968, ⟨64, (AddGraph.w454 s.p s.q)⟩),
      (980, ⟨64, (AddGraph.w462 s.p s.q)⟩),
      (981, ⟨64, (AddGraph.w461 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w29 s.p s.q)),
      ((.stack 5), (s.fr.rsp - 496), (AddGraph.w16 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w32 s.p s.q))]
    stores [((.stack 37), 465, (s.fr.rsp - 240), (AddGraph.w465 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment23 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_23 b_l10a410_24 := by
  replay_segment 23
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (942, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (966, ⟨64, (AddGraph.w458 s.p s.q)⟩),
      (976, ⟨64, (AddGraph.w460 s.p s.q)⟩),
      (983, ⟨64, (AddGraph.w461 s.p s.q)⟩),
      (985, ⟨64, (AddGraph.w462 s.p s.q)⟩),
      (992, ⟨64, (AddGraph.w464 s.p s.q)⟩),
      (994, ⟨64, (AddGraph.w463 s.p s.q)⟩),
      (1020, ⟨64, (AddGraph.w475 s.p s.q)⟩),
      (1023, ⟨64, (AddGraph.w478 s.p s.q)⟩),
      (1025, ⟨64, (AddGraph.w475 s.p s.q)⟩)]
    loads [((.stack 3), (s.fr.rsp - 512), (AddGraph.w459 s.p s.q)),
      ((.stack 4), (s.fr.rsp - 504), (AddGraph.w333 s.p s.q))]
    stores [((.stack 45), 500, (s.fr.rsp - 176), (AddGraph.w500 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment24 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_24 b_l10a410_25 := by
  replay_segment 24
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1056, ⟨64, (AddGraph.w499 s.p s.q)⟩),
      (1063, ⟨64, (AddGraph.w503 s.p s.q)⟩),
      (1066, ⟨64, (AddGraph.w502 s.p s.q)⟩),
      (1070, ⟨64, (AddGraph.w504 s.p s.q)⟩)]
    loads [((.right 10), (s.fr.rsi + 80), (AddGraph.w34 s.p s.q)),
      ((.right 11), (s.fr.rsi + 88), (AddGraph.w35 s.p s.q)),
      ((.right 12), (s.fr.rsi + 96), (AddGraph.w36 s.p s.q)),
      ((.right 13), (s.fr.rsi + 104), (AddGraph.w37 s.p s.q)),
      ((.right 14), (s.fr.rsi + 112), (AddGraph.w38 s.p s.q)),
      ((.stack 12), (s.fr.rsp - 440), s.fr.rsi),
      ((.stack 39), (s.fr.rsp - 224), (AddGraph.w373 s.p s.q)),
      ((.stack 48), (s.fr.rsp - 152), s.fr.rdi)]
    stores [((.stack 3), 34, (s.fr.rsp - 512), (AddGraph.w34 s.p s.q)),
      ((.stack 1), 35, (s.fr.rsp - 528), (AddGraph.w35 s.p s.q)),
      ((.stack 6), 36, (s.fr.rsp - 488), (AddGraph.w36 s.p s.q)),
      ((.stack 11), 37, (s.fr.rsp - 448), (AddGraph.w37 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment25 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_25 b_l10a410_26 := by
  replay_segment 25
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1094, ⟨64, (AddGraph.w34 s.p s.q)⟩),
      (1097, ⟨64, (AddGraph.w35 s.p s.q)⟩),
      (1100, ⟨64, (AddGraph.w36 s.p s.q)⟩),
      (1103, ⟨64, (AddGraph.w37 s.p s.q)⟩),
      (1108, ⟨64, s.fr.rdi⟩)]
    loads [((.left 10), (s.fr.rdi + 80), (AddGraph.w19 s.p s.q)),
      ((.left 11), (s.fr.rdi + 88), (AddGraph.w20 s.p s.q)),
      ((.left 12), (s.fr.rdi + 96), (AddGraph.w21 s.p s.q)),
      ((.left 13), (s.fr.rdi + 104), (AddGraph.w22 s.p s.q))]
    stores [((.stack 26), 19, (s.fr.rsp - 328), (AddGraph.w19 s.p s.q)),
      ((.stack 4), 524, (s.fr.rsp - 504), (AddGraph.w524 s.p s.q)),
      ((.stack 12), 523, (s.fr.rsp - 440), (AddGraph.w523 s.p s.q)),
      ((.stack 23), 20, (s.fr.rsp - 352), (AddGraph.w20 s.p s.q)),
      ((.stack 29), 529, (s.fr.rsp - 304), (AddGraph.w529 s.p s.q)),
      ((.stack 8), 528, (s.fr.rsp - 472), (AddGraph.w528 s.p s.q)),
      ((.stack 16), 21, (s.fr.rsp - 408), (AddGraph.w21 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment26 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_26 b_l10a410_27 := by
  replay_segment 26
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1082, ⟨64, (AddGraph.w513 s.p s.q)⟩),
      (1084, ⟨64, (AddGraph.w509 s.p s.q)⟩),
      (1090, ⟨64, (AddGraph.w514 s.p s.q)⟩),
      (1106, ⟨64, (AddGraph.w38 s.p s.q)⟩),
      (1108, ⟨64, s.fr.rdi⟩),
      (1136, ⟨64, (AddGraph.w533 s.p s.q)⟩),
      (1138, ⟨64, (AddGraph.w532 s.p s.q)⟩),
      (1140, ⟨64, (AddGraph.w22 s.p s.q)⟩),
      (1144, ⟨64, (AddGraph.w536 s.p s.q)⟩),
      (1145, ⟨64, (AddGraph.w535 s.p s.q)⟩)]
    loads [((.left 14), (s.fr.rdi + 112), (AddGraph.w23 s.p s.q))]
    stores [((.stack 24), 22, (s.fr.rsp - 344), (AddGraph.w22 s.p s.q)),
      ((.stack 9), 38, (s.fr.rsp - 464), (AddGraph.w38 s.p s.q)),
      ((.stack 14), 23, (s.fr.rsp - 424), (AddGraph.w23 s.p s.q)),
      ((.stack 39), 543, (s.fr.rsp - 224), (AddGraph.w543 s.p s.q)),
      ((.stack 55), 548, (s.fr.rsp - 96), (AddGraph.w548 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment27 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_27 b_l10a410_28 := by
  replay_segment 27
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1106, ⟨64, (AddGraph.w38 s.p s.q)⟩),
      (1110, ⟨64, (AddGraph.w19 s.p s.q)⟩),
      (1161, ⟨64, (AddGraph.w541 s.p s.q)⟩),
      (1163, ⟨64, (AddGraph.w540 s.p s.q)⟩),
      (1174, ⟨64, (AddGraph.w547 s.p s.q)⟩),
      (1175, ⟨64, (AddGraph.w546 s.p s.q)⟩),
      (1180, ⟨64, (AddGraph.w550 s.p s.q)⟩),
      (1183, ⟨64, (AddGraph.w553 s.p s.q)⟩)]
    loads [((.stack 4), (s.fr.rsp - 504), (AddGraph.w524 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w36 s.p s.q)),
      ((.stack 8), (s.fr.rsp - 472), (AddGraph.w528 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w37 s.p s.q)),
      ((.stack 12), (s.fr.rsp - 440), (AddGraph.w523 s.p s.q)),
      ((.stack 23), (s.fr.rsp - 352), (AddGraph.w20 s.p s.q)),
      ((.stack 29), (s.fr.rsp - 304), (AddGraph.w529 s.p s.q))]
    stores [((.stack 27), 562, (s.fr.rsp - 320), (AddGraph.w562 s.p s.q)),
      ((.stack 12), 569, (s.fr.rsp - 440), (AddGraph.w569 s.p s.q)),
      ((.stack 4), 570, (s.fr.rsp - 504), (AddGraph.w570 s.p s.q)),
      ((.stack 8), 571, (s.fr.rsp - 472), (AddGraph.w571 s.p s.q))]

theorem segments14To27 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_14 b_l10a410_28 :=
  BodySegment.trans
    (BodySegment.trans
      (BodySegment.trans
        (segment14 inc s r)
        (BodySegment.trans
          (segment15 inc s r)
          (segment16 inc s r)))
      (BodySegment.trans
        (BodySegment.trans
          (segment17 inc s r)
          (segment18 inc s r))
        (BodySegment.trans
          (segment19 inc s r)
          (segment20 inc s r))))
    (BodySegment.trans
      (BodySegment.trans
        (segment21 inc s r)
        (BodySegment.trans
          (segment22 inc s r)
          (segment23 inc s r)))
      (BodySegment.trans
        (BodySegment.trans
          (segment24 inc s r)
          (segment25 inc s r))
        (BodySegment.trans
          (segment26 inc s r)
          (segment27 inc s r))))

end K256.Proofs.Generate.Generator.Multiply.AddReplay
