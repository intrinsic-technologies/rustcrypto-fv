import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment119 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_119 b_l10a410_120 := by
  replay_segment 119
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4970, ⟨64, (AddGraph.w1550 s.p s.q)⟩),
      (4977, ⟨64, (AddGraph.w1561 s.p s.q)⟩),
      (4981, ⟨64, (AddGraph.w1557 s.p s.q)⟩),
      (4991, ⟨64, (AddGraph.w1562 s.p s.q)⟩),
      (5002, ⟨64, (AddGraph.w1567 s.p s.q)⟩),
      (5010, ⟨64, (AddGraph.w2164 s.p s.q)⟩),
      (5014, ⟨64, (AddGraph.w1572 s.p s.q)⟩),
      (5019, ⟨64, (AddGraph.w2166 s.p s.q)⟩),
      (5021, ⟨64, (AddGraph.w2165 s.p s.q)⟩),
      (5034, ⟨64, (AddGraph.w2170 s.p s.q)⟩),
      (5035, ⟨64, (AddGraph.w2169 s.p s.q)⟩),
      (5045, ⟨64, (AddGraph.w2176 s.p s.q)⟩),
      (5048, ⟨64, (AddGraph.w2179 s.p s.q)⟩)]
    loads [((.stack 11), (s.fr.rsp - 448), (AddGraph.w1566 s.p s.q)),
      ((.stack 19), (s.fr.rsp - 384), (AddGraph.w2163 s.p s.q))]
    stores [((.stack 21), 2184, (s.fr.rsp - 368), (AddGraph.w2184 s.p s.q)),
      ((.stack 25), 2189, (s.fr.rsp - 336), (AddGraph.w2189 s.p s.q)),
      ((.stack 28), 2190, (s.fr.rsp - 312), (AddGraph.w2190 s.p s.q)),
      ((.stack 13), 2191, (s.fr.rsp - 432), (AddGraph.w2191 s.p s.q)),
      ((.stack 19), 2192, (s.fr.rsp - 384), (AddGraph.w2192 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment120 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_120 b_l10a410_121 := by
  replay_segment 120
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5002, ⟨64, (AddGraph.w1567 s.p s.q)⟩),
      (5021, ⟨64, (AddGraph.w2165 s.p s.q)⟩),
      (5055, ⟨64, (AddGraph.w2184 s.p s.q)⟩),
      (5059, ⟨64, (AddGraph.w2187 s.p s.q)⟩),
      (5061, ⟨64, (AddGraph.w2188 s.p s.q)⟩),
      (5086, ⟨64, (AddGraph.w2194 s.p s.q)⟩),
      (5088, ⟨64, (AddGraph.w1567 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w1549 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w1573 s.p s.q)),
      ((.stack 5), (s.fr.rsp - 496), (AddGraph.w1556 s.p s.q)),
      ((.stack 19), (s.fr.rsp - 384), (AddGraph.w2192 s.p s.q))]
    stores [((.stack 27), 2197, (s.fr.rsp - 320), (AddGraph.w2197 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment121 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_121 b_l10a410_122 := by
  replay_segment 121
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5084, ⟨64, (AddGraph.w2193 s.p s.q)⟩),
      (5095, ⟨64, (AddGraph.w2195 s.p s.q)⟩),
      (5097, ⟨64, (AddGraph.w2196 s.p s.q)⟩),
      (5103, ⟨64, (AddGraph.w1549 s.p s.q)⟩),
      (5108, ⟨64, (AddGraph.w2198 s.p s.q)⟩),
      (5119, ⟨64, (AddGraph.w2202 s.p s.q)⟩),
      (5122, ⟨64, (AddGraph.w2203 s.p s.q)⟩),
      (5126, ⟨64, (AddGraph.w2205 s.p s.q)⟩),
      (5128, ⟨64, (AddGraph.w2206 s.p s.q)⟩),
      (5130, ⟨64, (AddGraph.w2207 s.p s.q)⟩),
      (5131, Value.ofBool (addSpec (AddGraph.w2194 s.p s.q) (AddGraph.w2192 s.p s.q)).2.CF)]
    loads [((.stack 13), (s.fr.rsp - 432), (AddGraph.w2191 s.p s.q)),
      ((.stack 25), (s.fr.rsp - 336), (AddGraph.w2189 s.p s.q)),
      ((.stack 26), (s.fr.rsp - 328), (AddGraph.w1550 s.p s.q)),
      ((.stack 27), (s.fr.rsp - 320), (AddGraph.w2197 s.p s.q)),
      ((.stack 28), (s.fr.rsp - 312), (AddGraph.w2190 s.p s.q))]
    stores [((.stack 25), 2227, (s.fr.rsp - 336), (AddGraph.w2227 s.p s.q)),
      ((.stack 28), 2233, (s.fr.rsp - 312), (AddGraph.w2233 s.p s.q)),
      ((.stack 13), 2234, (s.fr.rsp - 432), (AddGraph.w2234 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment122 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_122 b_l10a410_123 := by
  replay_segment 122
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5070, ⟨64, (AddGraph.w1566 s.p s.q)⟩),
      (5090, ⟨64, (AddGraph.w1567 s.p s.q)⟩),
      (5099, ⟨64, (AddGraph.w1573 s.p s.q)⟩),
      (5166, ⟨64, (AddGraph.w2227 s.p s.q)⟩)]
    loads [((.stack 5), (s.fr.rsp - 496), (AddGraph.w1556 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w1561 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w1572 s.p s.q)),
      ((.stack 14), (s.fr.rsp - 424), (AddGraph.w1562 s.p s.q)),
      ((.stack 22), (s.fr.rsp - 360), (AddGraph.w1557 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment123 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_123 b_l10a410_124 := by
  replay_segment 123
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5162, ⟨64, (AddGraph.w2231 s.p s.q)⟩),
      (5164, ⟨64, (AddGraph.w2232 s.p s.q)⟩),
      (5185, ⟨64, (AddGraph.w2236 s.p s.q)⟩),
      (5187, ⟨64, (AddGraph.w2235 s.p s.q)⟩),
      (5198, ⟨64, (AddGraph.w2238 s.p s.q)⟩),
      (5200, ⟨64, (AddGraph.w2239 s.p s.q)⟩),
      (5207, ⟨64, (AddGraph.w2240 s.p s.q)⟩),
      (5209, ⟨64, (AddGraph.w2241 s.p s.q)⟩),
      (5215, ⟨64, (AddGraph.w2243 s.p s.q)⟩),
      (5216, ⟨64, (AddGraph.w2242 s.p s.q)⟩),
      (5218, ⟨64, (AddGraph.w2244 s.p s.q)⟩)]
    loads [((.stack 13), (s.fr.rsp - 432), (AddGraph.w2234 s.p s.q)),
      ((.stack 28), (s.fr.rsp - 312), (AddGraph.w2233 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment124 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_124 b_l10a410_125 := by
  replay_segment 124
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5176, ⟨64, (AddGraph.w1572 s.p s.q)⟩),
      (5180, ⟨64, (AddGraph.w1557 s.p s.q)⟩),
      (5193, ⟨64, (AddGraph.w1562 s.p s.q)⟩),
      (5213, ⟨64, (AddGraph.w1556 s.p s.q)⟩),
      (5261, ⟨64, (AddGraph.w2268 s.p s.q)⟩),
      (5264, ⟨64, (AddGraph.w2271 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w1549 s.p s.q)),
      ((.stack 24), (s.fr.rsp - 344), (AddGraph.w1567 s.p s.q)),
      ((.stack 26), (s.fr.rsp - 328), (AddGraph.w1550 s.p s.q))]
    stores [((.stack 13), 2273, (s.fr.rsp - 432), (AddGraph.w2273 s.p s.q)),
      ((.stack 28), 2277, (s.fr.rsp - 312), (AddGraph.w2277 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment125 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_125 b_l10a410_126 := by
  replay_segment 125
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5242, ⟨64, (AddGraph.w2261 s.p s.q)⟩),
      (5259, ⟨64, (AddGraph.w2267 s.p s.q)⟩),
      (5278, ⟨64, (AddGraph.w2274 s.p s.q)⟩),
      (5285, ⟨64, (AddGraph.w2276 s.p s.q)⟩),
      (5287, ⟨64, (AddGraph.w2275 s.p s.q)⟩),
      (5299, ⟨64, (AddGraph.w2278 s.p s.q)⟩),
      (5301, ⟨64, (AddGraph.w2279 s.p s.q)⟩),
      (5305, ⟨64, (AddGraph.w1567 s.p s.q)⟩)]
    loads [((.stack 3), (s.fr.rsp - 512), (AddGraph.w1573 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w1561 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w1566 s.p s.q)),
      ((.stack 13), (s.fr.rsp - 432), (AddGraph.w2273 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment126 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_126 b_l10a410_127 := by
  replay_segment 126
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5266, ⟨64, (AddGraph.w2272 s.p s.q)⟩),
      (5272, ⟨64, (AddGraph.w1550 s.p s.q)⟩),
      (5331, ⟨64, (AddGraph.w2292 s.p s.q)⟩),
      (5334, ⟨64, (AddGraph.w2295 s.p s.q)⟩),
      (5345, ⟨64, (AddGraph.w2297 s.p s.q)⟩),
      (5350, ⟨64, (AddGraph.w2302 s.p s.q)⟩),
      (5352, ⟨64, (AddGraph.w2303 s.p s.q)⟩),
      (5353, Value.ofBool (addSpec (AddGraph.w2299 s.p s.q) (AddGraph.w2298 s.p s.q)).2.CF)]
    loads [((.stack 5), (s.fr.rsp - 496), (AddGraph.w1556 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w1561 s.p s.q)),
      ((.stack 14), (s.fr.rsp - 424), (AddGraph.w1562 s.p s.q)),
      ((.stack 22), (s.fr.rsp - 360), (AddGraph.w1557 s.p s.q))]
    stores [((.stack 6), 2315, (s.fr.rsp - 488), (AddGraph.w2315 s.p s.q)),
      ((.stack 13), 2316, (s.fr.rsp - 432), (AddGraph.w2316 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment127 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_127 b_l10a410_128 := by
  replay_segment 127
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5303, ⟨64, (AddGraph.w1567 s.p s.q)⟩),
      (5338, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (5366, ⟨64, (AddGraph.w2311 s.p s.q)⟩),
      (5368, ⟨64, (AddGraph.w2312 s.p s.q)⟩),
      (5376, ⟨64, (AddGraph.w2307 s.p s.q)⟩),
      (5394, ⟨64, (AddGraph.w1562 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w1549 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w1573 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w1572 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w1566 s.p s.q))]
    stores [((.stack 1), 2321, (s.fr.rsp - 528), (AddGraph.w2321 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment128 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_128 b_l10a410_129 := by
  replay_segment 128
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5372, ⟨64, (AddGraph.w2313 s.p s.q)⟩),
      (5374, ⟨64, (AddGraph.w2314 s.p s.q)⟩),
      (5390, ⟨64, (AddGraph.w2317 s.p s.q)⟩),
      (5392, ⟨64, (AddGraph.w2318 s.p s.q)⟩),
      (5399, ⟨64, (AddGraph.w2320 s.p s.q)⟩),
      (5401, ⟨64, (AddGraph.w2319 s.p s.q)⟩),
      (5429, ⟨64, (AddGraph.w2330 s.p s.q)⟩),
      (5432, ⟨64, (AddGraph.w2333 s.p s.q)⟩),
      (5436, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (5438, ⟨64, (AddGraph.w2334 s.p s.q)⟩)]
    loads [((.stack 6), (s.fr.rsp - 488), (AddGraph.w2315 s.p s.q)),
      ((.stack 13), (s.fr.rsp - 432), (AddGraph.w2316 s.p s.q))]
    stores [((.stack 11), 2357, (s.fr.rsp - 448), (AddGraph.w2357 s.p s.q))]

theorem segments119To128 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_119 b_l10a410_129 :=
  BodySegment.trans (BodySegment.trans (BodySegment.trans (segment119 inc s r)
        (segment120 inc s r))
      (BodySegment.trans (segment121 inc s r)
        (BodySegment.trans (segment122 inc s r)
          (segment123 inc s r))))
    (BodySegment.trans (BodySegment.trans (segment124 inc s r)
        (segment125 inc s r))
      (BodySegment.trans (segment126 inc s r)
        (BodySegment.trans (segment127 inc s r)
          (segment128 inc s r))))

end K256.Proofs.Generate.Generator.Multiply.AddReplay
