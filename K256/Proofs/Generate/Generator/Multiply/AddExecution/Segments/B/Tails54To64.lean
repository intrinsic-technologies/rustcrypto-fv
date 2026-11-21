import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point
  K256.Proofs.Generate.Generator.Multiply.AddGraph K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment54 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_54 b_l10a410_55 := by
  replay_segment 54
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2215, ⟨64, (AddGraph.w996 s.p s.q)⟩),
      (2235, ⟨64, (AddGraph.w1007 s.p s.q)⟩),
      (2290, ⟨64, (AddGraph.w1029 s.p s.q)⟩),
      (2297, ⟨64, (AddGraph.w1031 s.p s.q)⟩),
      (2299, ⟨64, (AddGraph.w1032 s.p s.q)⟩),
      (2309, ⟨64, (AddGraph.w1033 s.p s.q)⟩),
      (2311, ⟨64, (AddGraph.w1034 s.p s.q)⟩),
      (2316, ⟨64, (AddGraph.w1036 s.p s.q)⟩),
      (2320, ⟨64, (AddGraph.w1035 s.p s.q)⟩),
      (2322, ⟨64, (AddGraph.w1036 s.p s.q)⟩),
      (2324, ⟨64, (AddGraph.w80 s.p s.q)⟩)]
    loads [((.stack 4), (s.fr.rsp - 504), (AddGraph.w1025 s.p s.q)),
      ((.stack 8), (s.fr.rsp - 472), (AddGraph.w1026 s.p s.q)),
      ((.stack 18), (s.fr.rsp - 392), (AddGraph.w1027 s.p s.q)),
      ((.stack 38), (s.fr.rsp - 232), (AddGraph.w1028 s.p s.q))]
    stores [((.stack 29), 1041, (s.fr.rsp - 304), (AddGraph.w1041 s.p s.q)),
      ((.stack 4), 1055, (s.fr.rsp - 504), (AddGraph.w1055 s.p s.q)),
      ((.stack 8), 1061, (s.fr.rsp - 472), (AddGraph.w1061 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment55 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_55 b_l10a410_56 := by
  replay_segment 55
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2239, ⟨64, (AddGraph.w1009 s.p s.q)⟩),
      (2252, ⟨64, (AddGraph.w1015 s.p s.q)⟩),
      (2306, ⟨64, (AddGraph.w1013 s.p s.q)⟩),
      (2365, ⟨64, (AddGraph.w1062 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w1017 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w1019 s.p s.q)),
      ((.stack 5), (s.fr.rsp - 496), (AddGraph.w1011 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w1023 s.p s.q)),
      ((.stack 15), (s.fr.rsp - 416), (AddGraph.w1021 s.p s.q))]
    stores [((.stack 18), 1062, (s.fr.rsp - 392), (AddGraph.w1062 s.p s.q)),
      ((.stack 38), 1063, (s.fr.rsp - 232), (AddGraph.w1063 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment56 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_56 b_l10a410_57 := by
  replay_segment 56
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2359, ⟨64, (AddGraph.w1059 s.p s.q)⟩),
      (2361, ⟨64, (AddGraph.w1060 s.p s.q)⟩),
      (2376, ⟨64, (AddGraph.w1064 s.p s.q)⟩),
      (2387, ⟨64, (AddGraph.w1065 s.p s.q)⟩),
      (2389, ⟨64, (AddGraph.w1066 s.p s.q)⟩),
      (2396, ⟨64, (AddGraph.w1067 s.p s.q)⟩),
      (2398, ⟨64, (AddGraph.w1068 s.p s.q)⟩),
      (2400, ⟨64, (AddGraph.w1017 s.p s.q)⟩),
      (2407, ⟨64, (AddGraph.w1069 s.p s.q)⟩),
      (2409, ⟨64, (AddGraph.w1070 s.p s.q)⟩)]
    loads [((.stack 8), (s.fr.rsp - 472), (AddGraph.w1061 s.p s.q)),
      ((.stack 18), (s.fr.rsp - 392), (AddGraph.w1062 s.p s.q)),
      ((.stack 38), (s.fr.rsp - 232), (AddGraph.w1063 s.p s.q))]
    stores [((.stack 8), 1093, (s.fr.rsp - 472), (AddGraph.w1093 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment57 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_57 b_l10a410_58 := by
  replay_segment 57
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2378, ⟨64, (AddGraph.w1021 s.p s.q)⟩),
      (2382, ⟨64, (AddGraph.w1011 s.p s.q)⟩),
      (2453, ⟨64, (AddGraph.w1098 s.p s.q)⟩),
      (2455, ⟨64, (AddGraph.w1017 s.p s.q)⟩)]
    loads [((.stack 7), (s.fr.rsp - 480), (AddGraph.w1023 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w1007 s.p s.q)),
      ((.stack 17), (s.fr.rsp - 400), (AddGraph.w1013 s.p s.q)),
      ((.stack 22), (s.fr.rsp - 360), (AddGraph.w1009 s.p s.q)),
      ((.stack 32), (s.fr.rsp - 280), (AddGraph.w1029 s.p s.q))]
    stores [((.stack 18), 1099, (s.fr.rsp - 392), (AddGraph.w1099 s.p s.q)),
      ((.stack 38), 1100, (s.fr.rsp - 232), (AddGraph.w1100 s.p s.q)),
      ((.stack 46), 1101, (s.fr.rsp - 168), (AddGraph.w1101 s.p s.q)),
      ((.stack 51), 1102, (s.fr.rsp - 128), (AddGraph.w1102 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment58 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_58 b_l10a410_59 := by
  replay_segment 58
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2449, ⟨64, (AddGraph.w1097 s.p s.q)⟩),
      (2482, ⟨64, (AddGraph.w1104 s.p s.q)⟩),
      (2484, ⟨64, (AddGraph.w1103 s.p s.q)⟩),
      (2486, ⟨64, (AddGraph.w1105 s.p s.q)⟩),
      (2492, ⟨64, (AddGraph.w1107 s.p s.q)⟩),
      (2495, ⟨64, (AddGraph.w1106 s.p s.q)⟩)]
    loads [((.stack 2), (s.fr.rsp - 520), (AddGraph.w1019 s.p s.q)),
      ((.stack 30), (s.fr.rsp - 296), (AddGraph.w1015 s.p s.q)),
      ((.stack 46), (s.fr.rsp - 168), (AddGraph.w1101 s.p s.q)),
      ((.stack 51), (s.fr.rsp - 128), (AddGraph.w1102 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment59 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_59 b_l10a410_60 := by
  replay_segment 59
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2457, ⟨64, (AddGraph.w1007 s.p s.q)⟩),
      (2464, ⟨64, (AddGraph.w1029 s.p s.q)⟩),
      (2468, ⟨64, (AddGraph.w1009 s.p s.q)⟩),
      (2499, ⟨64, (AddGraph.w1019 s.p s.q)⟩),
      (2540, ⟨64, (AddGraph.w1131 s.p s.q)⟩),
      (2541, ⟨64, (AddGraph.w1130 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w1017 s.p s.q)),
      ((.stack 5), (s.fr.rsp - 496), (AddGraph.w1011 s.p s.q)),
      ((.stack 18), (s.fr.rsp - 392), (AddGraph.w1099 s.p s.q)),
      ((.stack 38), (s.fr.rsp - 232), (AddGraph.w1100 s.p s.q))]
    stores [((.stack 38), 1137, (s.fr.rsp - 232), (AddGraph.w1137 s.p s.q)),
      ((.stack 46), 1138, (s.fr.rsp - 168), (AddGraph.w1138 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment60 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_60 b_l10a410_61 := by
  replay_segment 60
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2475, ⟨64, (AddGraph.w1023 s.p s.q)⟩),
      (2490, ⟨64, (AddGraph.w1013 s.p s.q)⟩),
      (2503, ⟨64, (AddGraph.w1015 s.p s.q)⟩),
      (2528, ⟨64, (AddGraph.w1126 s.p s.q)⟩),
      (2566, ⟨64, (AddGraph.w1139 s.p s.q)⟩),
      (2568, ⟨64, (AddGraph.w1140 s.p s.q)⟩),
      (2577, ⟨64, (AddGraph.w1142 s.p s.q)⟩),
      (2579, ⟨64, (AddGraph.w1141 s.p s.q)⟩),
      (2581, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (2583, ⟨64, (AddGraph.w1143 s.p s.q)⟩)]
    loads [((.stack 15), (s.fr.rsp - 416), (AddGraph.w1021 s.p s.q)),
      ((.stack 38), (s.fr.rsp - 232), (AddGraph.w1137 s.p s.q)),
      ((.stack 46), (s.fr.rsp - 168), (AddGraph.w1138 s.p s.q))]
    stores [((.stack 18), 1143, (s.fr.rsp - 392), (AddGraph.w1143 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment61 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_61 b_l10a410_62 := by
  replay_segment 61
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2550, ⟨64, (AddGraph.w1136 s.p s.q)⟩),
      (2572, ⟨64, (AddGraph.w1011 s.p s.q)⟩),
      (2581, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (2595, ⟨64, (AddGraph.w1021 s.p s.q)⟩),
      (2623, ⟨64, (AddGraph.w1163 s.p s.q)⟩),
      (2624, ⟨64, (AddGraph.w1162 s.p s.q)⟩),
      (2626, ⟨64, (AddGraph.w1164 s.p s.q)⟩),
      (2629, ⟨64, (AddGraph.w1167 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w1017 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w1019 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w1007 s.p s.q)),
      ((.stack 22), (s.fr.rsp - 360), (AddGraph.w1009 s.p s.q))]
    stores [((.stack 15), 1183, (s.fr.rsp - 416), (AddGraph.w1183 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment62 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_62 b_l10a410_63 := by
  replay_segment 62
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2581, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (2617, ⟨64, (AddGraph.w1160 s.p s.q)⟩),
      (2650, ⟨64, (AddGraph.w1177 s.p s.q)⟩),
      (2652, ⟨64, (AddGraph.w1178 s.p s.q)⟩),
      (2659, ⟨64, (AddGraph.w1179 s.p s.q)⟩),
      (2661, ⟨64, (AddGraph.w1180 s.p s.q)⟩),
      (2668, ⟨64, (AddGraph.w1182 s.p s.q)⟩),
      (2670, ⟨64, (AddGraph.w1181 s.p s.q)⟩)]
    loads [((.stack 7), (s.fr.rsp - 480), (AddGraph.w1023 s.p s.q)),
      ((.stack 17), (s.fr.rsp - 400), (AddGraph.w1013 s.p s.q)),
      ((.stack 30), (s.fr.rsp - 296), (AddGraph.w1015 s.p s.q)),
      ((.stack 32), (s.fr.rsp - 280), (AddGraph.w1029 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment63 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_63 b_l10a410_64 := by
  replay_segment 63
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2581, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (2641, ⟨64, (AddGraph.w1176 s.p s.q)⟩),
      (2696, ⟨64, (AddGraph.w1192 s.p s.q)⟩),
      (2699, ⟨64, (AddGraph.w1195 s.p s.q)⟩),
      (2705, ⟨64, (AddGraph.w82 s.p s.q)⟩),
      (2708, ⟨64, (AddGraph.w1197 s.p s.q)⟩),
      (2718, ⟨64, (AddGraph.w1206 s.p s.q)⟩),
      (2720, ⟨64, (AddGraph.w1207 s.p s.q)⟩),
      (2721, Value.ofBool (addSpec (AddGraph.w1203 s.p s.q) (AddGraph.w1198 s.p s.q)).2.CF)]
    loads [((.stack 4), (s.fr.rsp - 504), (AddGraph.w1055 s.p s.q)),
      ((.stack 8), (s.fr.rsp - 472), (AddGraph.w1093 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment64 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_64 b_l10a410_65 := by
  replay_segment 64
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2734, ⟨64, (AddGraph.w1217 s.p s.q)⟩),
      (2745, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (2752, ⟨64, (AddGraph.w1225 s.p s.q)⟩),
      (2765, ⟨64, (AddGraph.w1231 s.p s.q)⟩)]
    loads [((.stack 13), (s.fr.rsp - 432), (AddGraph.w694 s.p s.q)),
      ((.stack 15), (s.fr.rsp - 416), (AddGraph.w1183 s.p s.q)),
      ((.stack 18), (s.fr.rsp - 392), (AddGraph.w1143 s.p s.q)),
      ((.stack 27), (s.fr.rsp - 320), (AddGraph.w789 s.p s.q)),
      ((.stack 37), (s.fr.rsp - 240), (AddGraph.w465 s.p s.q)),
      ((.stack 42), (s.fr.rsp - 200), (AddGraph.w424 s.p s.q)),
      ((.stack 45), (s.fr.rsp - 176), (AddGraph.w500 s.p s.q)),
      ((.stack 55), (s.fr.rsp - 96), (AddGraph.w548 s.p s.q)),
      ((.stack 58), (s.fr.rsp - 72), (AddGraph.w728 s.p s.q)),
      ((.stack 59), (s.fr.rsp - 64), (AddGraph.w653 s.p s.q))]
    stores []


theorem segments54To64 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_54 b_l10a410_65 :=
  BodySegment.trans (segment54 inc s r) <|
    BodySegment.trans (segment55 inc s r) <|
    BodySegment.trans (segment56 inc s r) <|
    BodySegment.trans (segment57 inc s r) <|
    BodySegment.trans (segment58 inc s r) <|
    BodySegment.trans (segment59 inc s r) <|
    BodySegment.trans (segment60 inc s r) <|
    BodySegment.trans (segment61 inc s r) <|
    BodySegment.trans (segment62 inc s r) <|
    BodySegment.trans (segment63 inc s r) <|
    segment64 inc s r

end K256.Proofs.Generate.Generator.Multiply.AddReplay
