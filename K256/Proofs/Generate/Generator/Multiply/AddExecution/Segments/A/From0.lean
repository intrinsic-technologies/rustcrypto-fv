import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point
  K256.Proofs.Generate.Generator.Multiply.AddGraph K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment0 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410 b_l10a410_1 := by
  replay_segment 0
    regs [(3, ⟨64, s.fr.rbx⟩),
      (4, ⟨64, s.fr.rsp⟩),
      (5, ⟨64, s.fr.rbp⟩),
      (6, ⟨64, s.fr.rsi⟩),
      (7, ⟨64, s.fr.rdi⟩),
      (12, ⟨64, s.fr.r12⟩),
      (13, ⟨64, s.fr.r13⟩),
      (14, ⟨64, s.fr.r14⟩),
      (15, ⟨64, s.fr.r15⟩)]
    loads [((.left 0), s.fr.rdi, (AddGraph.w9 s.p s.q)),
      ((.left 1), (s.fr.rdi + 8), (AddGraph.w10 s.p s.q)),
      ((.left 2), (s.fr.rdi + 16), (AddGraph.w11 s.p s.q)),
      ((.left 3), (s.fr.rdi + 24), (AddGraph.w12 s.p s.q)),
      ((.right 2), (s.fr.rsi + 16), (AddGraph.w26 s.p s.q)),
      ((.right 3), (s.fr.rsi + 24), (AddGraph.w27 s.p s.q))]
    stores [((.stack 66), 4, (s.fr.rsp - 8), s.fr.rbp),
      ((.stack 65), 8, (s.fr.rsp - 16), s.fr.r15),
      ((.stack 64), 7, (s.fr.rsp - 24), s.fr.r14),
      ((.stack 63), 6, (s.fr.rsp - 32), s.fr.r13),
      ((.stack 62), 5, (s.fr.rsp - 40), s.fr.r12),
      ((.stack 61), 3, (s.fr.rsp - 48), s.fr.rbx),
      ((.stack 28), 12, (s.fr.rsp - 312), (AddGraph.w12 s.p s.q)),
      ((.stack 48), 1, (s.fr.rsp - 152), s.fr.rdi),
      ((.stack 20), 26, (s.fr.rsp - 376), (AddGraph.w26 s.p s.q)),
      ((.stack 25), 27, (s.fr.rsp - 336), (AddGraph.w27 s.p s.q)),
      ((.stack 21), 9, (s.fr.rsp - 368), (AddGraph.w9 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment1 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_1 b_l10a410_2 := by
  replay_segment 1
    regs [(6, ⟨64, s.fr.rsi⟩),
      (7, ⟨64, s.fr.rdi⟩),
      (65, ⟨64, (s.fr.rsp - 536)⟩),
      (69, ⟨64, (AddGraph.w10 s.p s.q)⟩),
      (71, ⟨64, (AddGraph.w11 s.p s.q)⟩),
      (73, ⟨64, (AddGraph.w12 s.p s.q)⟩),
      (77, ⟨64, (AddGraph.w26 s.p s.q)⟩),
      (85, ⟨64, (AddGraph.w57 s.p s.q)⟩),
      (86, ⟨64, (AddGraph.w56 s.p s.q)⟩)]
    loads [((.left 4), (s.fr.rdi + 32), (AddGraph.w13 s.p s.q)),
      ((.right 0), s.fr.rsi, (AddGraph.w24 s.p s.q)),
      ((.right 1), (s.fr.rsi + 8), (AddGraph.w25 s.p s.q))]
    stores [((.stack 0), 56, (s.fr.rsp - 536), (AddGraph.w56 s.p s.q)),
      ((.stack 2), 57, (s.fr.rsp - 520), (AddGraph.w57 s.p s.q)),
      ((.stack 31), 10, (s.fr.rsp - 288), (AddGraph.w10 s.p s.q)),
      ((.stack 3), 61, (s.fr.rsp - 512), (AddGraph.w61 s.p s.q)),
      ((.stack 4), 60, (s.fr.rsp - 504), (AddGraph.w60 s.p s.q)),
      ((.stack 41), 25, (s.fr.rsp - 208), (AddGraph.w25 s.p s.q)),
      ((.stack 43), 11, (s.fr.rsp - 192), (AddGraph.w11 s.p s.q)),
      ((.stack 40), 24, (s.fr.rsp - 216), (AddGraph.w24 s.p s.q)),
      ((.stack 12), 2, (s.fr.rsp - 440), s.fr.rsi)]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment2 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_2 b_l10a410_3 := by
  replay_segment 2
    regs [(6, ⟨64, s.fr.rsi⟩),
      (65, ⟨64, (s.fr.rsp - 536)⟩),
      (106, ⟨64, (AddGraph.w68 s.p s.q)⟩),
      (108, ⟨64, (AddGraph.w67 s.p s.q)⟩),
      (117, ⟨64, (AddGraph.w73 s.p s.q)⟩),
      (119, ⟨64, (AddGraph.w72 s.p s.q)⟩),
      (121, ⟨64, (AddGraph.w13 s.p s.q)⟩)]
    loads [((.right 4), (s.fr.rsi + 32), (AddGraph.w28 s.p s.q)),
      ((.stack 0), (s.fr.rsp - 536), (AddGraph.w56 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w57 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w61 s.p s.q)),
      ((.stack 4), (s.fr.rsp - 504), (AddGraph.w60 s.p s.q))]
    stores [((.stack 34), 28, (s.fr.rsp - 264), (AddGraph.w28 s.p s.q)),
      ((.stack 56), 13, (s.fr.rsp - 88), (AddGraph.w13 s.p s.q)),
      ((.stack 47), 97, (s.fr.rsp - 160), (AddGraph.w97 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment3 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_3 b_l10a410_4 := by
  replay_segment 3
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (67, ⟨64, (AddGraph.w9 s.p s.q)⟩),
      (69, ⟨64, (AddGraph.w10 s.p s.q)⟩),
      (71, ⟨64, (AddGraph.w11 s.p s.q)⟩),
      (80, ⟨64, (AddGraph.w27 s.p s.q)⟩),
      (123, ⟨64, (AddGraph.w28 s.p s.q)⟩),
      (132, ⟨64, (AddGraph.w78 s.p s.q)⟩),
      (134, ⟨64, (AddGraph.w77 s.p s.q)⟩),
      (160, ⟨64, (AddGraph.w97 s.p s.q)⟩),
      (164, ⟨64, (AddGraph.w101 s.p s.q)⟩)]
    loads [((.stack 20), (s.fr.rsp - 376), (AddGraph.w26 s.p s.q)),
      ((.stack 28), (s.fr.rsp - 312), (AddGraph.w12 s.p s.q)),
      ((.stack 41), (s.fr.rsp - 208), (AddGraph.w25 s.p s.q))]
    stores [((.stack 0), 105, (s.fr.rsp - 536), (AddGraph.w105 s.p s.q)),
      ((.stack 2), 106, (s.fr.rsp - 520), (AddGraph.w106 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment4 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_4 b_l10a410_5 := by
  replay_segment 4
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (121, ⟨64, (AddGraph.w13 s.p s.q)⟩),
      (166, ⟨64, (AddGraph.w103 s.p s.q)⟩),
      (168, ⟨64, (AddGraph.w104 s.p s.q)⟩),
      (182, ⟨64, (AddGraph.w107 s.p s.q)⟩),
      (184, ⟨64, (AddGraph.w108 s.p s.q)⟩),
      (193, ⟨64, (AddGraph.w109 s.p s.q)⟩),
      (195, ⟨64, (AddGraph.w110 s.p s.q)⟩),
      (204, ⟨64, (AddGraph.w111 s.p s.q)⟩),
      (206, ⟨64, (AddGraph.w112 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w105 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w106 s.p s.q)),
      ((.stack 40), (s.fr.rsp - 216), (AddGraph.w24 s.p s.q))]
    stores [((.stack 50), 137, (s.fr.rsp - 136), (AddGraph.w137 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment5 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_5 b_l10a410_6 := by
  replay_segment 5
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (186, ⟨64, (AddGraph.w26 s.p s.q)⟩),
      (208, ⟨64, (AddGraph.w24 s.p s.q)⟩),
      (249, ⟨64, (AddGraph.w136 s.p s.q)⟩),
      (251, ⟨64, (AddGraph.w137 s.p s.q)⟩),
      (252, Value.ofBool (addSpec (AddGraph.w133 s.p s.q) (AddGraph.w104 s.p s.q)).2.CF)]
    loads [((.stack 21), (s.fr.rsp - 368), (AddGraph.w9 s.p s.q)),
      ((.stack 25), (s.fr.rsp - 336), (AddGraph.w27 s.p s.q)),
      ((.stack 31), (s.fr.rsp - 288), (AddGraph.w10 s.p s.q)),
      ((.stack 34), (s.fr.rsp - 264), (AddGraph.w28 s.p s.q)),
      ((.stack 43), (s.fr.rsp - 192), (AddGraph.w11 s.p s.q))]
    stores [((.stack 0), 146, (s.fr.rsp - 536), (AddGraph.w146 s.p s.q)),
      ((.stack 2), 147, (s.fr.rsp - 520), (AddGraph.w147 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment6 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_6 b_l10a410_7 := by
  replay_segment 6
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (199, ⟨64, (AddGraph.w12 s.p s.q)⟩),
      (257, ⟨64, (AddGraph.w143 s.p s.q)⟩),
      (277, ⟨64, (AddGraph.w148 s.p s.q)⟩),
      (279, ⟨64, (AddGraph.w149 s.p s.q)⟩),
      (288, ⟨64, (AddGraph.w151 s.p s.q)⟩),
      (290, ⟨64, (AddGraph.w150 s.p s.q)⟩),
      (292, ⟨64, (AddGraph.w153 s.p s.q)⟩),
      (294, ⟨64, (AddGraph.w26 s.p s.q)⟩)]
    loads [((.stack 41), (s.fr.rsp - 208), (AddGraph.w25 s.p s.q)),
      ((.stack 56), (s.fr.rsp - 88), (AddGraph.w13 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment7 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_7 b_l10a410_8 := by
  replay_segment 7
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (263, ⟨64, (AddGraph.w9 s.p s.q)⟩),
      (272, ⟨64, (AddGraph.w10 s.p s.q)⟩),
      (303, ⟨64, (AddGraph.w25 s.p s.q)⟩),
      (340, ⟨64, (AddGraph.w179 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w146 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w147 s.p s.q)),
      ((.stack 34), (s.fr.rsp - 264), (AddGraph.w28 s.p s.q)),
      ((.stack 40), (s.fr.rsp - 216), (AddGraph.w24 s.p s.q)),
      ((.stack 43), (s.fr.rsp - 192), (AddGraph.w11 s.p s.q))]
    stores [((.stack 0), 188, (s.fr.rsp - 536), (AddGraph.w188 s.p s.q)),
      ((.stack 2), 189, (s.fr.rsp - 520), (AddGraph.w189 s.p s.q)),
      ((.stack 44), 191, (s.fr.rsp - 184), (AddGraph.w191 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment8 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_8 b_l10a410_9 := by
  replay_segment 8
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (281, ⟨64, (AddGraph.w27 s.p s.q)⟩),
      (307, ⟨64, (AddGraph.w13 s.p s.q)⟩),
      (332, ⟨64, (AddGraph.w174 s.p s.q)⟩),
      (356, ⟨64, (AddGraph.w183 s.p s.q)⟩),
      (380, ⟨64, (AddGraph.w193 s.p s.q)⟩),
      (382, ⟨64, (AddGraph.w194 s.p s.q)⟩)]
    loads [((.stack 20), (s.fr.rsp - 376), (AddGraph.w26 s.p s.q)),
      ((.stack 28), (s.fr.rsp - 312), (AddGraph.w12 s.p s.q))]
    stores [((.stack 53), 195, (s.fr.rsp - 112), (AddGraph.w195 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment9 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_9 b_l10a410_10 := by
  replay_segment 9
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (354, ⟨64, (AddGraph.w187 s.p s.q)⟩),
      (370, ⟨64, (AddGraph.w190 s.p s.q)⟩),
      (402, ⟨64, (AddGraph.w26 s.p s.q)⟩),
      (419, ⟨64, (AddGraph.w209 s.p s.q)⟩),
      (426, ⟨64, (AddGraph.w80 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w188 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w189 s.p s.q)),
      ((.stack 21), (s.fr.rsp - 368), (AddGraph.w9 s.p s.q)),
      ((.stack 31), (s.fr.rsp - 288), (AddGraph.w10 s.p s.q)),
      ((.stack 40), (s.fr.rsp - 216), (AddGraph.w24 s.p s.q)),
      ((.stack 41), (s.fr.rsp - 208), (AddGraph.w25 s.p s.q)),
      ((.stack 44), (s.fr.rsp - 184), (AddGraph.w191 s.p s.q))]
    stores [((.stack 0), 230, (s.fr.rsp - 536), (AddGraph.w230 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment10 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_10 b_l10a410_11 := by
  replay_segment 10
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (307, ⟨64, (AddGraph.w13 s.p s.q)⟩),
      (373, ⟨64, (AddGraph.w28 s.p s.q)⟩),
      (377, ⟨64, (AddGraph.w11 s.p s.q)⟩),
      (393, ⟨64, (AddGraph.w12 s.p s.q)⟩),
      (424, ⟨64, (AddGraph.w213 s.p s.q)⟩),
      (426, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (447, ⟨64, (AddGraph.w225 s.p s.q)⟩),
      (471, ⟨64, (AddGraph.w24 s.p s.q)⟩)]
    loads [((.stack 25), (s.fr.rsp - 336), (AddGraph.w27 s.p s.q))]
    stores [((.stack 44), 236, (s.fr.rsp - 184), (AddGraph.w236 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment11 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_11 b_l10a410_12 := by
  replay_segment 11
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (452, ⟨64, (AddGraph.w229 s.p s.q)⟩),
      (460, ⟨64, (AddGraph.w231 s.p s.q)⟩),
      (467, ⟨64, (AddGraph.w232 s.p s.q)⟩),
      (469, ⟨64, (AddGraph.w233 s.p s.q)⟩),
      (476, ⟨64, (AddGraph.w235 s.p s.q)⟩),
      (478, ⟨64, (AddGraph.w234 s.p s.q)⟩),
      (482, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (506, ⟨64, (AddGraph.w245 s.p s.q)⟩),
      (509, ⟨64, (AddGraph.w248 s.p s.q)⟩),
      (513, ⟨64, (AddGraph.w249 s.p s.q)⟩),
      (515, ⟨64, (AddGraph.w82 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w230 s.p s.q)),
      ((.stack 47), (s.fr.rsp - 160), (AddGraph.w97 s.p s.q))]
    stores [((.stack 52), 270, (s.fr.rsp - 120), (AddGraph.w270 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment12 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_12 b_l10a410_13 := by
  replay_segment 12
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (542, ⟨64, (AddGraph.w269 s.p s.q)⟩),
      (558, ⟨64, (AddGraph.w275 s.p s.q)⟩),
      (561, ⟨64, (AddGraph.w278 s.p s.q)⟩)]
    loads [((.left 5), (s.fr.rdi + 40), (AddGraph.w14 s.p s.q)),
      ((.left 6), (s.fr.rdi + 48), (AddGraph.w15 s.p s.q)),
      ((.left 7), (s.fr.rdi + 56), (AddGraph.w16 s.p s.q)),
      ((.right 7), (s.fr.rsi + 56), (AddGraph.w31 s.p s.q)),
      ((.right 8), (s.fr.rsi + 64), (AddGraph.w32 s.p s.q)),
      ((.stack 12), (s.fr.rsp - 440), s.fr.rsi),
      ((.stack 48), (s.fr.rsp - 152), s.fr.rdi)]
    stores [((.stack 7), 32, (s.fr.rsp - 480), (AddGraph.w32 s.p s.q)),
      ((.stack 10), 14, (s.fr.rsp - 456), (AddGraph.w14 s.p s.q)),
      ((.stack 3), 288, (s.fr.rsp - 512), (AddGraph.w288 s.p s.q)),
      ((.stack 4), 287, (s.fr.rsp - 504), (AddGraph.w287 s.p s.q)),
      ((.stack 22), 15, (s.fr.rsp - 360), (AddGraph.w15 s.p s.q)),
      ((.stack 15), 31, (s.fr.rsp - 416), (AddGraph.w31 s.p s.q)),
      ((.stack 8), 295, (s.fr.rsp - 472), (AddGraph.w295 s.p s.q)),
      ((.stack 1), 294, (s.fr.rsp - 528), (AddGraph.w294 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment13 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_13 b_l10a410_14 := by
  replay_segment 13
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (570, ⟨64, s.fr.rdi⟩),
      (574, ⟨64, s.fr.rsi⟩),
      (596, ⟨64, (AddGraph.w16 s.p s.q)⟩)]
    loads [((.left 8), (s.fr.rdi + 64), (AddGraph.w17 s.p s.q)),
      ((.left 9), (s.fr.rdi + 72), (AddGraph.w18 s.p s.q)),
      ((.right 5), (s.fr.rsi + 40), (AddGraph.w29 s.p s.q)),
      ((.right 6), (s.fr.rsi + 48), (AddGraph.w30 s.p s.q)),
      ((.right 9), (s.fr.rsi + 72), (AddGraph.w33 s.p s.q)),
      ((.stack 50), (s.fr.rsp - 136), (AddGraph.w137 s.p s.q))]
    stores [((.stack 2), 30, (s.fr.rsp - 520), (AddGraph.w30 s.p s.q)),
      ((.stack 5), 16, (s.fr.rsp - 496), (AddGraph.w16 s.p s.q)),
      ((.stack 17), 17, (s.fr.rsp - 400), (AddGraph.w17 s.p s.q)),
      ((.stack 0), 29, (s.fr.rsp - 536), (AddGraph.w29 s.p s.q))]

theorem segments0To13 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410 b_l10a410_14 :=
  BodySegment.trans
    (BodySegment.trans
      (BodySegment.trans
        (segment0 inc s r)
        (BodySegment.trans
          (segment1 inc s r)
          (segment2 inc s r)))
      (BodySegment.trans
        (BodySegment.trans
          (segment3 inc s r)
          (segment4 inc s r))
        (BodySegment.trans
          (segment5 inc s r)
          (segment6 inc s r))))
    (BodySegment.trans
      (BodySegment.trans
        (segment7 inc s r)
        (BodySegment.trans
          (segment8 inc s r)
          (segment9 inc s r)))
      (BodySegment.trans
        (BodySegment.trans
          (segment10 inc s r)
          (segment11 inc s r))
        (BodySegment.trans
          (segment12 inc s r)
          (segment13 inc s r))))

end K256.Proofs.Generate.Generator.Multiply.AddReplay
