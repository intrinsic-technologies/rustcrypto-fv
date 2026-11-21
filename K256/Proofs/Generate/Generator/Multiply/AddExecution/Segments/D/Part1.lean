import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point
  K256.Proofs.Generate.Generator.Multiply.AddGraph K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment129 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_129 b_l10a410_130 := by
  replay_segment 129
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5436, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (5467, ⟨64, (AddGraph.w2354 s.p s.q)⟩),
      (5471, ⟨64, (AddGraph.w2355 s.p s.q)⟩),
      (5473, ⟨64, (AddGraph.w2356 s.p s.q)⟩),
      (5480, ⟨64, (AddGraph.w82 s.p s.q)⟩),
      (5482, ⟨64, (AddGraph.w2359 s.p s.q)⟩),
      (5483, ⟨64, (AddGraph.w2358 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w1501 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w1499 s.p s.q)),
      ((.stack 21), (s.fr.rsp - 368), (AddGraph.w2184 s.p s.q)),
      ((.stack 41), (s.fr.rsp - 208), (AddGraph.w1689 s.p s.q)),
      ((.stack 43), (s.fr.rsp - 192), (AddGraph.w1694 s.p s.q))]
    stores [((.stack 21), 2366, (s.fr.rsp - 368), (AddGraph.w2366 s.p s.q)),
      ((.stack 6), 2371, (s.fr.rsp - 488), (AddGraph.w2371 s.p s.q)),
      ((.stack 5), 2372, (s.fr.rsp - 496), (AddGraph.w2372 s.p s.q)),
      ((.stack 13), 2374, (s.fr.rsp - 432), (AddGraph.w2374 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment130 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_130 b_l10a410_131 := by
  replay_segment 130
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5522, ⟨64, (AddGraph.w2373 s.p s.q)⟩)]
    loads [((.stack 2), (s.fr.rsp - 520), (AddGraph.w1505 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w1485 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w1497 s.p s.q)),
      ((.stack 25), (s.fr.rsp - 336), (AddGraph.w2227 s.p s.q)),
      ((.stack 32), (s.fr.rsp - 280), (AddGraph.w1683 s.p s.q)),
      ((.stack 39), (s.fr.rsp - 224), (AddGraph.w1705 s.p s.q)),
      ((.stack 40), (s.fr.rsp - 216), (AddGraph.w1701 s.p s.q))]
    stores [((.stack 9), 2373, (s.fr.rsp - 464), (AddGraph.w2373 s.p s.q)),
      ((.stack 19), 2378, (s.fr.rsp - 384), (AddGraph.w2378 s.p s.q)),
      ((.stack 27), 2379, (s.fr.rsp - 320), (AddGraph.w2379 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment131 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_131 b_l10a410_132 := by
  replay_segment 131
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5504, ⟨64, (AddGraph.w2370 s.p s.q)⟩),
      (5508, ⟨64, (AddGraph.w1689 s.p s.q)⟩),
      (5530, ⟨64, (AddGraph.w2375 s.p s.q)⟩),
      (5539, ⟨64, (AddGraph.w2376 s.p s.q)⟩),
      (5541, ⟨64, (AddGraph.w2377 s.p s.q)⟩),
      (5556, ⟨64, (AddGraph.w1505 s.p s.q)⟩),
      (5558, ⟨64, (AddGraph.w2381 s.p s.q)⟩),
      (5561, ⟨64, (AddGraph.w2381 s.p s.q)⟩),
      (5563, ⟨64, (AddGraph.w2380 s.p s.q)⟩)]
    loads [((.stack 5), (s.fr.rsp - 496), (AddGraph.w2372 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w2371 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w2373 s.p s.q)),
      ((.stack 13), (s.fr.rsp - 432), (AddGraph.w2374 s.p s.q)),
      ((.stack 19), (s.fr.rsp - 384), (AddGraph.w2378 s.p s.q)),
      ((.stack 21), (s.fr.rsp - 368), (AddGraph.w2366 s.p s.q)),
      ((.stack 27), (s.fr.rsp - 320), (AddGraph.w2379 s.p s.q))]
    stores [((.stack 25), 2382, (s.fr.rsp - 336), (AddGraph.w2382 s.p s.q)),
      ((.stack 21), 2387, (s.fr.rsp - 368), (AddGraph.w2387 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment132 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_132 b_l10a410_133 := by
  replay_segment 132
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5515, ⟨64, (AddGraph.w1694 s.p s.q)⟩),
      (5519, ⟨64, (AddGraph.w1499 s.p s.q)⟩),
      (5532, ⟨64, (AddGraph.w1701 s.p s.q)⟩),
      (5543, ⟨64, (AddGraph.w1705 s.p s.q)⟩),
      (5552, ⟨64, (AddGraph.w1683 s.p s.q)⟩),
      (5598, ⟨64, (AddGraph.w2404 s.p s.q)⟩),
      (5606, ⟨64, (AddGraph.w2407 s.p s.q)⟩),
      (5607, ⟨64, (AddGraph.w2406 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w1501 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w1485 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w1497 s.p s.q))]
    stores [((.stack 6), 2406, (s.fr.rsp - 488), (AddGraph.w2406 s.p s.q)),
      ((.stack 5), 2407, (s.fr.rsp - 496), (AddGraph.w2407 s.p s.q)),
      ((.stack 9), 2408, (s.fr.rsp - 464), (AddGraph.w2408 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment133 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_133 b_l10a410_134 := by
  replay_segment 133
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5600, ⟨64, (AddGraph.w2403 s.p s.q)⟩),
      (5602, ⟨64, (AddGraph.w2405 s.p s.q)⟩),
      (5617, ⟨64, (AddGraph.w2409 s.p s.q)⟩),
      (5624, ⟨64, (AddGraph.w2410 s.p s.q)⟩),
      (5626, ⟨64, (AddGraph.w2411 s.p s.q)⟩),
      (5633, ⟨64, (AddGraph.w2412 s.p s.q)⟩),
      (5635, ⟨64, (AddGraph.w2413 s.p s.q)⟩),
      (5639, ⟨64, (AddGraph.w1485 s.p s.q)⟩),
      (5644, ⟨64, (AddGraph.w2414 s.p s.q)⟩),
      (5646, ⟨64, (AddGraph.w2415 s.p s.q)⟩),
      (5648, ⟨64, (AddGraph.w2404 s.p s.q)⟩)]
    loads [((.stack 5), (s.fr.rsp - 496), (AddGraph.w2407 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w2406 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w2408 s.p s.q)),
      ((.stack 41), (s.fr.rsp - 208), (AddGraph.w1689 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment134 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_134 b_l10a410_135 := by
  replay_segment 134
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5682, ⟨64, (AddGraph.w2439 s.p s.q)⟩),
      (5695, ⟨64, (AddGraph.w2446 s.p s.q)⟩),
      (5696, ⟨64, (AddGraph.w2445 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w1501 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w1505 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w1497 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w1499 s.p s.q)),
      ((.stack 32), (s.fr.rsp - 280), (AddGraph.w1683 s.p s.q)),
      ((.stack 39), (s.fr.rsp - 224), (AddGraph.w1705 s.p s.q)),
      ((.stack 40), (s.fr.rsp - 216), (AddGraph.w1701 s.p s.q)),
      ((.stack 43), (s.fr.rsp - 192), (AddGraph.w1694 s.p s.q))]
    stores [((.stack 6), 2445, (s.fr.rsp - 488), (AddGraph.w2445 s.p s.q)),
      ((.stack 5), 2446, (s.fr.rsp - 496), (AddGraph.w2446 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment135 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_135 b_l10a410_136 := by
  replay_segment 135
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5689, ⟨64, (AddGraph.w2443 s.p s.q)⟩),
      (5691, ⟨64, (AddGraph.w2444 s.p s.q)⟩),
      (5707, ⟨64, (AddGraph.w2448 s.p s.q)⟩),
      (5709, ⟨64, (AddGraph.w2447 s.p s.q)⟩),
      (5713, ⟨64, (AddGraph.w2449 s.p s.q)⟩),
      (5720, ⟨64, (AddGraph.w2450 s.p s.q)⟩),
      (5722, ⟨64, (AddGraph.w2451 s.p s.q)⟩),
      (5729, ⟨64, (AddGraph.w2452 s.p s.q)⟩),
      (5731, ⟨64, (AddGraph.w2453 s.p s.q)⟩),
      (5737, ⟨64, (AddGraph.w2455 s.p s.q)⟩),
      (5738, ⟨64, (AddGraph.w2454 s.p s.q)⟩)]
    loads [((.stack 5), (s.fr.rsp - 496), (AddGraph.w2446 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment136 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_136 b_l10a410_137 := by
  replay_segment 136
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5702, ⟨64, (AddGraph.w1694 s.p s.q)⟩),
      (5735, ⟨64, (AddGraph.w1497 s.p s.q)⟩),
      (5781, ⟨64, (AddGraph.w2478 s.p s.q)⟩),
      (5783, ⟨64, (AddGraph.w2480 s.p s.q)⟩),
      (5784, Value.ofBool (addSpec (AddGraph.w2479 s.p s.q) (AddGraph.w2446 s.p s.q)).2.CF)]
    loads [((.stack 2), (s.fr.rsp - 520), (AddGraph.w1505 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w2445 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w1485 s.p s.q)),
      ((.stack 40), (s.fr.rsp - 216), (AddGraph.w1701 s.p s.q)),
      ((.stack 41), (s.fr.rsp - 208), (AddGraph.w1689 s.p s.q))]
    stores [((.stack 5), 2486, (s.fr.rsp - 496), (AddGraph.w2486 s.p s.q)),
      ((.stack 9), 2487, (s.fr.rsp - 464), (AddGraph.w2487 s.p s.q)),
      ((.stack 6), 2490, (s.fr.rsp - 488), (AddGraph.w2490 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment137 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_137 b_l10a410_138 := by
  replay_segment 137
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5764, ⟨64, (AddGraph.w2473 s.p s.q)⟩),
      (5774, ⟨64, (AddGraph.w2477 s.p s.q)⟩),
      (5808, ⟨64, (AddGraph.w2489 s.p s.q)⟩),
      (5810, ⟨64, (AddGraph.w2488 s.p s.q)⟩),
      (5822, ⟨64, (AddGraph.w2491 s.p s.q)⟩),
      (5824, ⟨64, (AddGraph.w2492 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w1501 s.p s.q)),
      ((.stack 5), (s.fr.rsp - 496), (AddGraph.w2486 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w2487 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w1499 s.p s.q)),
      ((.stack 32), (s.fr.rsp - 280), (AddGraph.w1683 s.p s.q)),
      ((.stack 39), (s.fr.rsp - 224), (AddGraph.w1705 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment138 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_138 b_l10a410_139 := by
  replay_segment 138
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5790, ⟨64, (AddGraph.w2484 s.p s.q)⟩),
      (5792, ⟨64, (AddGraph.w2485 s.p s.q)⟩),
      (5852, ⟨64, (AddGraph.w2505 s.p s.q)⟩),
      (5855, ⟨64, (AddGraph.w2508 s.p s.q)⟩),
      (5865, ⟨64, (AddGraph.w2511 s.p s.q)⟩),
      (5866, ⟨64, (AddGraph.w2510 s.p s.q)⟩),
      (5868, ⟨64, (AddGraph.w2512 s.p s.q)⟩),
      (5871, ⟨64, (AddGraph.w2515 s.p s.q)⟩)]
    loads [((.stack 7), (s.fr.rsp - 480), (AddGraph.w1485 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w1497 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w1499 s.p s.q)),
      ((.stack 40), (s.fr.rsp - 216), (AddGraph.w1701 s.p s.q)),
      ((.stack 41), (s.fr.rsp - 208), (AddGraph.w1689 s.p s.q)),
      ((.stack 43), (s.fr.rsp - 192), (AddGraph.w1694 s.p s.q))]
    stores [((.stack 16), 2528, (s.fr.rsp - 408), (AddGraph.w2528 s.p s.q)),
      ((.stack 5), 2529, (s.fr.rsp - 496), (AddGraph.w2529 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment139 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_139 b_l10a410_140 := by
  replay_segment 139
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5859, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (5878, ⟨64, (AddGraph.w2520 s.p s.q)⟩),
      (5885, ⟨64, (AddGraph.w2524 s.p s.q)⟩),
      (5887, ⟨64, (AddGraph.w2525 s.p s.q)⟩),
      (5913, ⟨64, (AddGraph.w2533 s.p s.q)⟩),
      (5914, ⟨64, (AddGraph.w2532 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w1501 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w1505 s.p s.q)),
      ((.stack 32), (s.fr.rsp - 280), (AddGraph.w1683 s.p s.q)),
      ((.stack 39), (s.fr.rsp - 224), (AddGraph.w1705 s.p s.q))]
    stores [((.stack 10), 2533, (s.fr.rsp - 456), (AddGraph.w2533 s.p s.q)),
      ((.stack 7), 2532, (s.fr.rsp - 480), (AddGraph.w2532 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment140 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_140 b_l10a410_141 := by
  replay_segment 140
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5593, ⟨64, (AddGraph.w2400 s.p s.q)⟩),
      (5891, ⟨64, (AddGraph.w2526 s.p s.q)⟩),
      (5893, ⟨64, (AddGraph.w2527 s.p s.q)⟩),
      (5907, ⟨64, (AddGraph.w2530 s.p s.q)⟩),
      (5909, ⟨64, (AddGraph.w2531 s.p s.q)⟩),
      (5943, ⟨64, (AddGraph.w2543 s.p s.q)⟩),
      (5946, ⟨64, (AddGraph.w2546 s.p s.q)⟩),
      (5950, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (5954, ⟨64, (AddGraph.w82 s.p s.q)⟩),
      (5956, ⟨64, (AddGraph.w2549 s.p s.q)⟩),
      (5957, ⟨64, (AddGraph.w2548 s.p s.q)⟩)]
    loads [((.stack 5), (s.fr.rsp - 496), (AddGraph.w2529 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w2532 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w2533 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w2528 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment141 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_141 b_l10a410_142 := by
  replay_segment 141
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (5682, ⟨64, (AddGraph.w2439 s.p s.q)⟩),
      (5918, ⟨64, (AddGraph.w2534 s.p s.q)⟩),
      (5950, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (5985, ⟨64, (AddGraph.w2568 s.p s.q)⟩),
      (5987, ⟨64, (AddGraph.w2569 s.p s.q)⟩),
      (5989, ⟨64, (AddGraph.w2570 s.p s.q)⟩),
      (6000, ⟨64, (AddGraph.w2575 s.p s.q)⟩),
      (6003, ⟨64, (AddGraph.w2578 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w2321 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w2490 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w2357 s.p s.q)),
      ((.stack 21), (s.fr.rsp - 368), (AddGraph.w2387 s.p s.q)),
      ((.stack 25), (s.fr.rsp - 336), (AddGraph.w2382 s.p s.q)),
      ((.stack 28), (s.fr.rsp - 312), (AddGraph.w2277 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment142 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_142 b_l10a410_143 := by
  replay_segment 142
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6014, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (6016, ⟨64, (AddGraph.w2585 s.p s.q)⟩),
      (6018, ⟨64, (AddGraph.w308 s.p s.q)⟩),
      (6024, ⟨64, (AddGraph.w2590 s.p s.q)⟩),
      (6030, ⟨64, (AddGraph.w2594 s.p s.q)⟩),
      (6032, ⟨64, (AddGraph.w2596 s.p s.q)⟩),
      (6042, ⟨64, (AddGraph.w2600 s.p s.q)⟩),
      (6044, ⟨64, (AddGraph.w2600 s.p s.q)⟩)]
    loads [((.stack 18), (s.fr.rsp - 392), (AddGraph.w1269 s.p s.q)),
      ((.stack 24), (s.fr.rsp - 344), (AddGraph.w1567 s.p s.q))]
    stores [((.stack 7), 2609, (s.fr.rsp - 480), (AddGraph.w2609 s.p s.q)),
      ((.stack 16), 2613, (s.fr.rsp - 408), (AddGraph.w2613 s.p s.q)),
      ((.stack 5), 2615, (s.fr.rsp - 496), (AddGraph.w2615 s.p s.q))]

theorem segmentsD1 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_129 b_l10a410_143 := by
  refine BodySegment.trans (@segment129 code inc s r) ?_
  refine BodySegment.trans (@segment130 code inc s r) ?_
  refine BodySegment.trans (@segment131 code inc s r) ?_
  refine BodySegment.trans (@segment132 code inc s r) ?_
  refine BodySegment.trans (@segment133 code inc s r) ?_
  refine BodySegment.trans (@segment134 code inc s r) ?_
  refine BodySegment.trans (@segment135 code inc s r) ?_
  refine BodySegment.trans (@segment136 code inc s r) ?_
  refine BodySegment.trans (@segment137 code inc s r) ?_
  refine BodySegment.trans (@segment138 code inc s r) ?_
  refine BodySegment.trans (@segment139 code inc s r) ?_
  refine BodySegment.trans (@segment140 code inc s r) ?_
  refine BodySegment.trans (@segment141 code inc s r) ?_
  exact @segment142 code inc s r

end K256.Proofs.Generate.Generator.Multiply.AddReplay
