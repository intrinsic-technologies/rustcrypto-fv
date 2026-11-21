import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point
  K256.Proofs.Generate.Generator.Multiply.AddGraph K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment143 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_143 b_l10a410_144 := by
  replay_segment 143
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6014, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (6054, ⟨64, (AddGraph.w2603 s.p s.q)⟩),
      (6079, ⟨64, (AddGraph.w1567 s.p s.q)⟩),
      (6081, ⟨64, (AddGraph.w1269 s.p s.q)⟩)]
    loads [((.stack 4), (s.fr.rsp - 504), (AddGraph.w1285 s.p s.q)),
      ((.stack 14), (s.fr.rsp - 424), (AddGraph.w1562 s.p s.q)),
      ((.stack 15), (s.fr.rsp - 416), (AddGraph.w1271 s.p s.q)),
      ((.stack 22), (s.fr.rsp - 360), (AddGraph.w1557 s.p s.q)),
      ((.stack 26), (s.fr.rsp - 328), (AddGraph.w1550 s.p s.q)),
      ((.stack 30), (s.fr.rsp - 296), (AddGraph.w1277 s.p s.q))]
    stores [((.stack 0), 2616, (s.fr.rsp - 536), (AddGraph.w2616 s.p s.q)),
      ((.stack 2), 2617, (s.fr.rsp - 520), (AddGraph.w2617 s.p s.q)),
      ((.stack 11), 2619, (s.fr.rsp - 448), (AddGraph.w2619 s.p s.q)),
      ((.stack 1), 2618, (s.fr.rsp - 528), (AddGraph.w2618 s.p s.q)),
      ((.stack 6), 2620, (s.fr.rsp - 488), (AddGraph.w2620 s.p s.q)),
      ((.stack 9), 2621, (s.fr.rsp - 464), (AddGraph.w2621 s.p s.q)),
      ((.stack 32), 2622, (s.fr.rsp - 280), (AddGraph.w2622 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment144 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_144 b_l10a410_145 := by
  replay_segment 144
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6058, ⟨64, (AddGraph.w2606 s.p s.q)⟩),
      (6117, ⟨64, (AddGraph.w2624 s.p s.q)⟩),
      (6118, ⟨64, (AddGraph.w2623 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w2618 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w1573 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w2609 s.p s.q)),
      ((.stack 8), (s.fr.rsp - 472), (AddGraph.w1290 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w2621 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w2619 s.p s.q)),
      ((.stack 32), (s.fr.rsp - 280), (AddGraph.w2622 s.p s.q))]
    stores [((.stack 10), 2627, (s.fr.rsp - 456), (AddGraph.w2627 s.p s.q)),
      ((.stack 7), 2631, (s.fr.rsp - 480), (AddGraph.w2631 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment145 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_145 b_l10a410_146 := by
  replay_segment 145
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6081, ⟨64, (AddGraph.w1269 s.p s.q)⟩),
      (6088, ⟨64, (AddGraph.w1562 s.p s.q)⟩),
      (6092, ⟨64, (AddGraph.w1271 s.p s.q)⟩),
      (6102, ⟨64, (AddGraph.w1557 s.p s.q)⟩),
      (6106, ⟨64, (AddGraph.w1277 s.p s.q)⟩),
      (6115, ⟨64, (AddGraph.w1285 s.p s.q)⟩),
      (6124, ⟨64, (AddGraph.w1573 s.p s.q)⟩),
      (6133, ⟨64, (AddGraph.w2626 s.p s.q)⟩),
      (6135, ⟨64, (AddGraph.w2625 s.p s.q)⟩),
      (6148, ⟨64, (AddGraph.w2630 s.p s.q)⟩),
      (6149, ⟨64, (AddGraph.w2629 s.p s.q)⟩),
      (6157, ⟨64, (AddGraph.w2636 s.p s.q)⟩),
      (6160, ⟨64, (AddGraph.w2639 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w2616 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w2617 s.p s.q)),
      ((.stack 24), (s.fr.rsp - 344), (AddGraph.w1567 s.p s.q))]
    stores [((.stack 2), 2644, (s.fr.rsp - 520), (AddGraph.w2644 s.p s.q)),
      ((.stack 0), 2649, (s.fr.rsp - 536), (AddGraph.w2649 s.p s.q)),
      ((.stack 1), 2650, (s.fr.rsp - 528), (AddGraph.w2650 s.p s.q)),
      ((.stack 11), 2651, (s.fr.rsp - 448), (AddGraph.w2651 s.p s.q)),
      ((.stack 9), 2652, (s.fr.rsp - 464), (AddGraph.w2652 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment146 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_146 b_l10a410_147 := by
  replay_segment 146
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6128, ⟨64, (AddGraph.w1290 s.p s.q)⟩),
      (6135, ⟨64, (AddGraph.w2625 s.p s.q)⟩),
      (6167, ⟨64, (AddGraph.w2644 s.p s.q)⟩),
      (6171, ⟨64, (AddGraph.w2647 s.p s.q)⟩),
      (6173, ⟨64, (AddGraph.w2648 s.p s.q)⟩),
      (6194, ⟨64, (AddGraph.w2653 s.p s.q)⟩),
      (6196, ⟨64, (AddGraph.w2654 s.p s.q)⟩),
      (6200, ⟨64, (AddGraph.w2656 s.p s.q)⟩),
      (6201, ⟨64, (AddGraph.w2655 s.p s.q)⟩)]
    loads [((.stack 26), (s.fr.rsp - 328), (AddGraph.w1550 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment147 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_147 b_l10a410_148 := by
  replay_segment 147
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6207, ⟨64, (AddGraph.w1550 s.p s.q)⟩),
      (6226, ⟨64, (AddGraph.w2662 s.p s.q)⟩),
      (6229, ⟨64, (AddGraph.w2663 s.p s.q)⟩),
      (6233, ⟨64, (AddGraph.w2665 s.p s.q)⟩),
      (6235, ⟨64, (AddGraph.w2666 s.p s.q)⟩),
      (6242, ⟨64, (AddGraph.w2671 s.p s.q)⟩),
      (6245, ⟨64, (AddGraph.w2674 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w2649 s.p s.q)),
      ((.stack 1), (s.fr.rsp - 528), (AddGraph.w2650 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w1573 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w2652 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w2651 s.p s.q)),
      ((.stack 15), (s.fr.rsp - 416), (AddGraph.w1271 s.p s.q)),
      ((.stack 18), (s.fr.rsp - 392), (AddGraph.w1269 s.p s.q))]
    stores [((.stack 11), 2687, (s.fr.rsp - 448), (AddGraph.w2687 s.p s.q)),
      ((.stack 0), 2694, (s.fr.rsp - 536), (AddGraph.w2694 s.p s.q)),
      ((.stack 1), 2695, (s.fr.rsp - 528), (AddGraph.w2695 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment148 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_148 b_l10a410_149 := by
  replay_segment 148
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6276, ⟨64, (AddGraph.w2693 s.p s.q)⟩),
      (6285, ⟨64, (AddGraph.w1573 s.p s.q)⟩),
      (6287, ⟨64, (AddGraph.w1271 s.p s.q)⟩)]
    loads [((.stack 4), (s.fr.rsp - 504), (AddGraph.w1285 s.p s.q)),
      ((.stack 8), (s.fr.rsp - 472), (AddGraph.w1290 s.p s.q)),
      ((.stack 14), (s.fr.rsp - 424), (AddGraph.w1562 s.p s.q)),
      ((.stack 22), (s.fr.rsp - 360), (AddGraph.w1557 s.p s.q)),
      ((.stack 24), (s.fr.rsp - 344), (AddGraph.w1567 s.p s.q)),
      ((.stack 30), (s.fr.rsp - 296), (AddGraph.w1277 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment149 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_149 b_l10a410_150 := by
  replay_segment 149
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6270, ⟨64, (AddGraph.w2691 s.p s.q)⟩),
      (6272, ⟨64, (AddGraph.w2692 s.p s.q)⟩),
      (6292, ⟨64, (AddGraph.w2696 s.p s.q)⟩),
      (6294, ⟨64, (AddGraph.w2697 s.p s.q)⟩),
      (6305, ⟨64, (AddGraph.w2698 s.p s.q)⟩),
      (6307, ⟨64, (AddGraph.w2700 s.p s.q)⟩),
      (6330, ⟨64, (AddGraph.w2708 s.p s.q)⟩),
      (6332, ⟨64, (AddGraph.w2709 s.p s.q)⟩),
      (6333, Value.ofBool (addSpec (AddGraph.w2705 s.p s.q) (AddGraph.w2699 s.p s.q)).2.CF)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w2694 s.p s.q)),
      ((.stack 1), (s.fr.rsp - 528), (AddGraph.w2695 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment150 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_150 b_l10a410_151 := by
  replay_segment 150
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6287, ⟨64, (AddGraph.w1271 s.p s.q)⟩),
      (6298, ⟨64, (AddGraph.w1277 s.p s.q)⟩),
      (6318, ⟨64, (AddGraph.w1557 s.p s.q)⟩),
      (6368, ⟨64, (AddGraph.w2728 s.p s.q)⟩)]
    loads [((.stack 3), (s.fr.rsp - 512), (AddGraph.w1573 s.p s.q)),
      ((.stack 4), (s.fr.rsp - 504), (AddGraph.w1285 s.p s.q)),
      ((.stack 18), (s.fr.rsp - 392), (AddGraph.w1269 s.p s.q)),
      ((.stack 24), (s.fr.rsp - 344), (AddGraph.w1567 s.p s.q)),
      ((.stack 26), (s.fr.rsp - 328), (AddGraph.w1550 s.p s.q))]
    stores [((.stack 0), 2734, (s.fr.rsp - 536), (AddGraph.w2734 s.p s.q)),
      ((.stack 1), 2735, (s.fr.rsp - 528), (AddGraph.w2735 s.p s.q)),
      ((.stack 9), 2740, (s.fr.rsp - 464), (AddGraph.w2740 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment151 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_151 b_l10a410_152 := by
  replay_segment 151
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6322, ⟨64, (AddGraph.w1290 s.p s.q)⟩),
      (6349, ⟨64, (AddGraph.w2721 s.p s.q)⟩),
      (6359, ⟨64, (AddGraph.w2725 s.p s.q)⟩),
      (6377, ⟨64, (AddGraph.w2733 s.p s.q)⟩),
      (6393, ⟨64, (AddGraph.w2736 s.p s.q)⟩),
      (6395, ⟨64, (AddGraph.w2737 s.p s.q)⟩),
      (6402, ⟨64, (AddGraph.w2739 s.p s.q)⟩),
      (6404, ⟨64, (AddGraph.w2738 s.p s.q)⟩),
      (6416, ⟨64, (AddGraph.w2741 s.p s.q)⟩),
      (6418, ⟨64, (AddGraph.w2742 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w2734 s.p s.q)),
      ((.stack 1), (s.fr.rsp - 528), (AddGraph.w2735 s.p s.q)),
      ((.stack 14), (s.fr.rsp - 424), (AddGraph.w1562 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment152 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_152 b_l10a410_153 := by
  replay_segment 152
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6375, ⟨64, (AddGraph.w2732 s.p s.q)⟩),
      (6420, ⟨64, (AddGraph.w1562 s.p s.q)⟩),
      (6439, ⟨64, (AddGraph.w2753 s.p s.q)⟩),
      (6442, ⟨64, (AddGraph.w2756 s.p s.q)⟩),
      (6463, ⟨64, (AddGraph.w2767 s.p s.q)⟩),
      (6465, ⟨64, (AddGraph.w2768 s.p s.q)⟩),
      (6466, Value.ofBool (addSpec (AddGraph.w2764 s.p s.q) (AddGraph.w2733 s.p s.q)).2.CF)]
    loads [((.stack 15), (s.fr.rsp - 416), (AddGraph.w1271 s.p s.q)),
      ((.stack 18), (s.fr.rsp - 392), (AddGraph.w1269 s.p s.q)),
      ((.stack 22), (s.fr.rsp - 360), (AddGraph.w1557 s.p s.q)),
      ((.stack 26), (s.fr.rsp - 328), (AddGraph.w1550 s.p s.q)),
      ((.stack 30), (s.fr.rsp - 296), (AddGraph.w1277 s.p s.q))]
    stores [((.stack 0), 2776, (s.fr.rsp - 536), (AddGraph.w2776 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment153 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_153 b_l10a410_154 := by
  replay_segment 153
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6446, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (6468, ⟨64, (AddGraph.w2768 s.p s.q)⟩),
      (6474, ⟨64, (AddGraph.w2772 s.p s.q)⟩),
      (6476, ⟨64, (AddGraph.w2773 s.p s.q)⟩),
      (6499, ⟨64, (AddGraph.w2779 s.p s.q)⟩),
      (6506, ⟨64, (AddGraph.w2781 s.p s.q)⟩)]
    loads [((.stack 3), (s.fr.rsp - 512), (AddGraph.w1573 s.p s.q)),
      ((.stack 4), (s.fr.rsp - 504), (AddGraph.w1285 s.p s.q)),
      ((.stack 8), (s.fr.rsp - 472), (AddGraph.w1290 s.p s.q)),
      ((.stack 24), (s.fr.rsp - 344), (AddGraph.w1567 s.p s.q))]
    stores [((.stack 18), 2782, (s.fr.rsp - 392), (AddGraph.w2782 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment154 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_154 b_l10a410_155 := by
  replay_segment 154
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6480, ⟨64, (AddGraph.w2774 s.p s.q)⟩),
      (6482, ⟨64, (AddGraph.w2775 s.p s.q)⟩),
      (6490, ⟨64, (AddGraph.w2777 s.p s.q)⟩),
      (6497, ⟨64, (AddGraph.w2778 s.p s.q)⟩),
      (6508, ⟨64, (AddGraph.w2780 s.p s.q)⟩),
      (6536, ⟨64, (AddGraph.w2791 s.p s.q)⟩),
      (6539, ⟨64, (AddGraph.w2794 s.p s.q)⟩),
      (6543, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (6547, ⟨64, (AddGraph.w82 s.p s.q)⟩),
      (6549, ⟨64, (AddGraph.w2797 s.p s.q)⟩),
      (6550, ⟨64, (AddGraph.w2796 s.p s.q)⟩),
      (6552, ⟨64, (AddGraph.w2798 s.p s.q)⟩),
      (6553, Value.ofBool (addSpec (AddGraph.w2781 s.p s.q) (AddGraph.w2779 s.p s.q)).2.CF)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w2776 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w2644 s.p s.q))]
    stores [((.stack 24), 2818, (s.fr.rsp - 344), (AddGraph.w2818 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment155 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_155 b_l10a410_156 := by
  replay_segment 155
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6578, ⟨64, (AddGraph.w2816 s.p s.q)⟩),
      (6580, ⟨64, (AddGraph.w2817 s.p s.q)⟩),
      (6588, ⟨64, (AddGraph.w2819 s.p s.q)⟩),
      (6590, ⟨64, (AddGraph.w2821 s.p s.q)⟩),
      (6596, ⟨64, (AddGraph.w2823 s.p s.q)⟩),
      (6597, Value.ofBool (addSpec (AddGraph.w2822 s.p s.q) (AddGraph.w2820 s.p s.q)).2.CF)]
    loads [((.stack 33), (s.fr.rsp - 272), (AddGraph.w1005 s.p s.q)),
      ((.stack 44), (s.fr.rsp - 184), (AddGraph.w236 s.p s.q)),
      ((.stack 47), (s.fr.rsp - 160), (AddGraph.w320 s.p s.q)),
      ((.stack 52), (s.fr.rsp - 120), (AddGraph.w270 s.p s.q)),
      ((.stack 53), (s.fr.rsp - 112), (AddGraph.w195 s.p s.q))]
    stores [((.stack 8), 2832, (s.fr.rsp - 472), (AddGraph.w2832 s.p s.q)),
      ((.stack 4), 2834, (s.fr.rsp - 504), (AddGraph.w2834 s.p s.q)),
      ((.stack 3), 2836, (s.fr.rsp - 512), (AddGraph.w2836 s.p s.q)),
      ((.stack 1), 2838, (s.fr.rsp - 528), (AddGraph.w2838 s.p s.q)),
      ((.stack 26), 2839, (s.fr.rsp - 328), (AddGraph.w2839 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment156 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_156 b_l10a410_157 := by
  replay_segment 156
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6608, ⟨64, (AddGraph.w2832 s.p s.q)⟩),
      (6613, ⟨64, (AddGraph.w2834 s.p s.q)⟩),
      (6618, ⟨64, (AddGraph.w2836 s.p s.q)⟩),
      (6623, ⟨64, (AddGraph.w2838 s.p s.q)⟩),
      (6633, ⟨64, (AddGraph.w1005 s.p s.q)⟩)]
    loads [((.stack 12), (s.fr.rsp - 440), (AddGraph.w998 s.p s.q)),
      ((.stack 35), (s.fr.rsp - 256), (AddGraph.w1003 s.p s.q)),
      ((.stack 36), (s.fr.rsp - 248), (AddGraph.w1001 s.p s.q)),
      ((.stack 50), (s.fr.rsp - 136), (AddGraph.w315 s.p s.q))]
    stores [((.stack 15), 2840, (s.fr.rsp - 416), (AddGraph.w2840 s.p s.q)),
      ((.stack 14), 2841, (s.fr.rsp - 424), (AddGraph.w2841 s.p s.q)),
      ((.stack 0), 2845, (s.fr.rsp - 536), (AddGraph.w2845 s.p s.q))]

theorem segmentsD2 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_143 b_l10a410_157 := by
  refine BodySegment.trans (@segment143 code inc s r) ?_
  refine BodySegment.trans (@segment144 code inc s r) ?_
  refine BodySegment.trans (@segment145 code inc s r) ?_
  refine BodySegment.trans (@segment146 code inc s r) ?_
  refine BodySegment.trans (@segment147 code inc s r) ?_
  refine BodySegment.trans (@segment148 code inc s r) ?_
  refine BodySegment.trans (@segment149 code inc s r) ?_
  refine BodySegment.trans (@segment150 code inc s r) ?_
  refine BodySegment.trans (@segment151 code inc s r) ?_
  refine BodySegment.trans (@segment152 code inc s r) ?_
  refine BodySegment.trans (@segment153 code inc s r) ?_
  refine BodySegment.trans (@segment154 code inc s r) ?_
  refine BodySegment.trans (@segment155 code inc s r) ?_
  exact @segment156 code inc s r

end K256.Proofs.Generate.Generator.Multiply.AddReplay
