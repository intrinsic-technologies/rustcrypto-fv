import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment108 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_108 b_l10a410_109 := by
  replay_segment 108
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4547, ⟨64, (AddGraph.w1978 s.p s.q)⟩),
      (4549, ⟨64, (AddGraph.w1979 s.p s.q)⟩),
      (4565, ⟨64, (AddGraph.w1983 s.p s.q)⟩),
      (4567, ⟨64, (AddGraph.w1982 s.p s.q)⟩),
      (4571, ⟨64, (AddGraph.w1984 s.p s.q)⟩),
      (4578, ⟨64, (AddGraph.w1985 s.p s.q)⟩),
      (4580, ⟨64, (AddGraph.w1986 s.p s.q)⟩),
      (4582, ⟨64, (AddGraph.w1688 s.p s.q)⟩)]
    loads [((.stack 10), (s.fr.rsp - 456), (AddGraph.w1497 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w1499 s.p s.q)),
      ((.stack 28), (s.fr.rsp - 312), (AddGraph.w1629 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment109 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_109 b_l10a410_110 := by
  replay_segment 109
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4551, ⟨64, (AddGraph.w1685 s.p s.q)⟩),
      (4595, ⟨64, (AddGraph.w1497 s.p s.q)⟩),
      (4600, ⟨64, (AddGraph.w1991 s.p s.q)⟩),
      (4622, ⟨64, (AddGraph.w2007 s.p s.q)⟩),
      (4626, ⟨64, (AddGraph.w2009 s.p s.q)⟩),
      (4628, ⟨64, (AddGraph.w177 s.p s.q)⟩)]
    loads [((.stack 7), (s.fr.rsp - 480), (AddGraph.w1485 s.p s.q)),
      ((.stack 31), (s.fr.rsp - 288), (AddGraph.w1686 s.p s.q)),
      ((.stack 37), (s.fr.rsp - 240), (AddGraph.w1981 s.p s.q)),
      ((.stack 42), (s.fr.rsp - 200), (AddGraph.w1980 s.p s.q))]
    stores [((.stack 37), 2021, (s.fr.rsp - 240), (AddGraph.w2021 s.p s.q)),
      ((.stack 45), 2022, (s.fr.rsp - 176), (AddGraph.w2022 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment110 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_110 b_l10a410_111 := by
  replay_segment 110
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4591, ⟨64, (AddGraph.w1629 s.p s.q)⟩),
      (4624, ⟨64, (AddGraph.w2008 s.p s.q)⟩),
      (4654, ⟨64, (AddGraph.w2015 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w1501 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w1505 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w1499 s.p s.q)),
      ((.stack 21), (s.fr.rsp - 368), (AddGraph.w1687 s.p s.q)),
      ((.stack 25), (s.fr.rsp - 336), (AddGraph.w1688 s.p s.q))]
    stores [((.stack 42), 2025, (s.fr.rsp - 200), (AddGraph.w2025 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment111 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_111 b_l10a410_112 := by
  replay_segment 111
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4634, ⟨64, (AddGraph.w2012 s.p s.q)⟩),
      (4650, ⟨64, (AddGraph.w2019 s.p s.q)⟩),
      (4652, ⟨64, (AddGraph.w2020 s.p s.q)⟩),
      (4668, ⟨64, (AddGraph.w2024 s.p s.q)⟩),
      (4670, ⟨64, (AddGraph.w2023 s.p s.q)⟩),
      (4697, ⟨64, (AddGraph.w1499 s.p s.q)⟩),
      (4712, ⟨64, (AddGraph.w2039 s.p s.q)⟩),
      (4714, ⟨64, (AddGraph.w2040 s.p s.q)⟩),
      (4715, Value.ofBool (addSpec (AddGraph.w2036 s.p s.q) (AddGraph.w2008 s.p s.q)).2.CF)]
    loads [((.stack 13), (s.fr.rsp - 432), (AddGraph.w1685 s.p s.q)),
      ((.stack 37), (s.fr.rsp - 240), (AddGraph.w2021 s.p s.q)),
      ((.stack 45), (s.fr.rsp - 176), (AddGraph.w2022 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment112 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_112 b_l10a410_113 := by
  replay_segment 112
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4721, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (4740, ⟨64, (AddGraph.w2055 s.p s.q)⟩),
      (4759, ⟨64, (AddGraph.w2064 s.p s.q)⟩),
      (4760, ⟨64, (AddGraph.w2063 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w1501 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w1505 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w1485 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w1497 s.p s.q)),
      ((.stack 21), (s.fr.rsp - 368), (AddGraph.w1687 s.p s.q)),
      ((.stack 25), (s.fr.rsp - 336), (AddGraph.w1688 s.p s.q)),
      ((.stack 28), (s.fr.rsp - 312), (AddGraph.w1629 s.p s.q)),
      ((.stack 31), (s.fr.rsp - 288), (AddGraph.w1686 s.p s.q))]
    stores [((.stack 13), 2063, (s.fr.rsp - 432), (AddGraph.w2063 s.p s.q)),
      ((.stack 37), 2064, (s.fr.rsp - 240), (AddGraph.w2064 s.p s.q)),
      ((.stack 31), 2068, (s.fr.rsp - 288), (AddGraph.w2068 s.p s.q)),
      ((.stack 21), 2067, (s.fr.rsp - 368), (AddGraph.w2067 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment113 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_113 b_l10a410_114 := by
  replay_segment 113
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4747, ⟨64, (AddGraph.w2059 s.p s.q)⟩),
      (4749, ⟨64, (AddGraph.w2060 s.p s.q)⟩),
      (4753, ⟨64, (AddGraph.w2061 s.p s.q)⟩),
      (4755, ⟨64, (AddGraph.w2062 s.p s.q)⟩),
      (4769, ⟨64, (AddGraph.w2065 s.p s.q)⟩),
      (4771, ⟨64, (AddGraph.w2066 s.p s.q)⟩),
      (4780, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (4789, ⟨64, (AddGraph.w2070 s.p s.q)⟩),
      (4791, ⟨64, (AddGraph.w2071 s.p s.q)⟩),
      (4798, ⟨64, (AddGraph.w2072 s.p s.q)⟩),
      (4800, ⟨64, (AddGraph.w2073 s.p s.q)⟩)]
    loads [((.stack 13), (s.fr.rsp - 432), (AddGraph.w2063 s.p s.q)),
      ((.stack 21), (s.fr.rsp - 368), (AddGraph.w2067 s.p s.q)),
      ((.stack 31), (s.fr.rsp - 288), (AddGraph.w2068 s.p s.q)),
      ((.stack 37), (s.fr.rsp - 240), (AddGraph.w2064 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment114 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_114 b_l10a410_115 := by
  replay_segment 114
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4540, ⟨64, (AddGraph.w1974 s.p s.q)⟩),
      (4780, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (4816, ⟨64, (AddGraph.w82 s.p s.q)⟩),
      (4836, ⟨64, (AddGraph.w2097 s.p s.q)⟩),
      (4839, ⟨64, (AddGraph.w2100 s.p s.q)⟩),
      (4841, ⟨64, (AddGraph.w2101 s.p s.q)⟩),
      (4843, ⟨64, (AddGraph.w2102 s.p s.q)⟩),
      (4847, ⟨64, (AddGraph.w2103 s.p s.q)⟩)]
    loads [((.stack 19), (s.fr.rsp - 384), (AddGraph.w1907 s.p s.q)),
      ((.stack 27), (s.fr.rsp - 320), (AddGraph.w1936 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment115 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_115 b_l10a410_116 := by
  replay_segment 115
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4782, ⟨64, (AddGraph.w2069 s.p s.q)⟩),
      (4888, ⟨64, (AddGraph.w2122 s.p s.q)⟩),
      (4890, ⟨64, (AddGraph.w1569 s.p s.q)⟩)]
    loads [((.stack 17), (s.fr.rsp - 400), (AddGraph.w1856 s.p s.q)),
      ((.stack 20), (s.fr.rsp - 376), (AddGraph.w1892 s.p s.q)),
      ((.stack 34), (s.fr.rsp - 264), (AddGraph.w1814 s.p s.q)),
      ((.stack 42), (s.fr.rsp - 200), (AddGraph.w2025 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment116 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_116 b_l10a410_117 := by
  replay_segment 116
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4851, ⟨64, (AddGraph.w2105 s.p s.q)⟩),
      (4864, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (4878, ⟨64, (AddGraph.w2114 s.p s.q)⟩),
      (4880, ⟨64, (AddGraph.w308 s.p s.q)⟩),
      (4892, ⟨64, (AddGraph.w2123 s.p s.q)⟩),
      (4914, ⟨64, (AddGraph.w1553 s.p s.q)⟩),
      (4922, ⟨64, (AddGraph.w2130 s.p s.q)⟩),
      (4926, ⟨64, (AddGraph.w2136 s.p s.q)⟩),
      (4930, ⟨64, (AddGraph.w2138 s.p s.q)⟩)]
    loads [((.stack 11), (s.fr.rsp - 448), (AddGraph.w1566 s.p s.q)),
      ((.stack 23), (s.fr.rsp - 352), (AddGraph.w1909 s.p s.q))]
    stores [((.stack 31), 2153, (s.fr.rsp - 288), (AddGraph.w2153 s.p s.q)),
      ((.stack 34), 2155, (s.fr.rsp - 264), (AddGraph.w2155 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment117 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_117 b_l10a410_118 := by
  replay_segment 117
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4864, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (4936, ⟨64, (AddGraph.w2136 s.p s.q)⟩),
      (4968, ⟨64, (AddGraph.w1566 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w1549 s.p s.q)),
      ((.stack 5), (s.fr.rsp - 496), (AddGraph.w1556 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w1561 s.p s.q)),
      ((.stack 14), (s.fr.rsp - 424), (AddGraph.w1562 s.p s.q)),
      ((.stack 22), (s.fr.rsp - 360), (AddGraph.w1557 s.p s.q)),
      ((.stack 24), (s.fr.rsp - 344), (AddGraph.w1567 s.p s.q)),
      ((.stack 26), (s.fr.rsp - 328), (AddGraph.w1550 s.p s.q))]
    stores [((.stack 21), 2156, (s.fr.rsp - 368), (AddGraph.w2156 s.p s.q)),
      ((.stack 25), 2157, (s.fr.rsp - 336), (AddGraph.w2157 s.p s.q)),
      ((.stack 13), 2159, (s.fr.rsp - 432), (AddGraph.w2159 s.p s.q)),
      ((.stack 28), 2158, (s.fr.rsp - 312), (AddGraph.w2158 s.p s.q)),
      ((.stack 17), 2160, (s.fr.rsp - 400), (AddGraph.w2160 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment118 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_118 b_l10a410_119 := by
  replay_segment 118
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4940, ⟨64, (AddGraph.w2142 s.p s.q)⟩),
      (4954, ⟨64, (AddGraph.w2149 s.p s.q)⟩),
      (4998, ⟨64, (AddGraph.w2161 s.p s.q)⟩),
      (5000, ⟨64, (AddGraph.w2162 s.p s.q)⟩),
      (5006, ⟨64, (AddGraph.w2164 s.p s.q)⟩),
      (5007, ⟨64, (AddGraph.w2163 s.p s.q)⟩)]
    loads [((.stack 3), (s.fr.rsp - 512), (AddGraph.w1573 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w1572 s.p s.q)),
      ((.stack 13), (s.fr.rsp - 432), (AddGraph.w2159 s.p s.q)),
      ((.stack 21), (s.fr.rsp - 368), (AddGraph.w2156 s.p s.q)),
      ((.stack 25), (s.fr.rsp - 336), (AddGraph.w2157 s.p s.q)),
      ((.stack 28), (s.fr.rsp - 312), (AddGraph.w2158 s.p s.q))]
    stores [((.stack 19), 2163, (s.fr.rsp - 384), (AddGraph.w2163 s.p s.q)),
      ((.stack 20), 2167, (s.fr.rsp - 376), (AddGraph.w2167 s.p s.q)),
      ((.stack 23), 2171, (s.fr.rsp - 352), (AddGraph.w2171 s.p s.q))]

theorem segments108To118 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_108 b_l10a410_119 :=
  BodySegment.trans (BodySegment.trans (BodySegment.trans (segment108 inc s r)
        (segment109 inc s r))
      (BodySegment.trans (segment110 inc s r)
        (BodySegment.trans (segment111 inc s r)
          (segment112 inc s r))))
    (BodySegment.trans (BodySegment.trans (segment113 inc s r)
        (BodySegment.trans (segment114 inc s r)
          (segment115 inc s r)))
      (BodySegment.trans (segment116 inc s r)
        (BodySegment.trans (segment117 inc s r)
          (segment118 inc s r))))

end K256.Proofs.Generate.Generator.Multiply.AddReplay
