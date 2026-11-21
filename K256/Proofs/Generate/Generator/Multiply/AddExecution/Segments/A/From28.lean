import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point
  K256.Proofs.Generate.Generator.Multiply.AddGraph K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment28 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_28 b_l10a410_29 := by
  replay_segment 28
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1140, ⟨64, (AddGraph.w22 s.p s.q)⟩),
      (1152, ⟨64, (AddGraph.w23 s.p s.q)⟩),
      (1201, ⟨64, (AddGraph.w567 s.p s.q)⟩),
      (1220, ⟨64, (AddGraph.w572 s.p s.q)⟩),
      (1224, ⟨64, (AddGraph.w36 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w35 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w34 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w21 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment29 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_29 b_l10a410_30 := by
  replay_segment 29
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1203, ⟨64, (AddGraph.w568 s.p s.q)⟩),
      (1214, ⟨64, (AddGraph.w20 s.p s.q)⟩),
      (1242, ⟨64, (AddGraph.w34 s.p s.q)⟩),
      (1257, ⟨64, (AddGraph.w580 s.p s.q)⟩),
      (1258, ⟨64, (AddGraph.w579 s.p s.q)⟩),
      (1268, ⟨64, (AddGraph.w588 s.p s.q)⟩),
      (1270, ⟨64, (AddGraph.w589 s.p s.q)⟩),
      (1271, Value.ofBool (addSpec (AddGraph.w585 s.p s.q) (AddGraph.w572 s.p s.q)).2.CF)]
    loads [((.stack 4), (s.fr.rsp - 504), (AddGraph.w570 s.p s.q)),
      ((.stack 8), (s.fr.rsp - 472), (AddGraph.w571 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w38 s.p s.q)),
      ((.stack 12), (s.fr.rsp - 440), (AddGraph.w569 s.p s.q)),
      ((.stack 26), (s.fr.rsp - 328), (AddGraph.w19 s.p s.q))]
    stores [((.stack 19), 601, (s.fr.rsp - 384), (AddGraph.w601 s.p s.q)),
      ((.stack 12), 608, (s.fr.rsp - 440), (AddGraph.w608 s.p s.q)),
      ((.stack 4), 609, (s.fr.rsp - 504), (AddGraph.w609 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment30 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_30 b_l10a410_31 := by
  replay_segment 30
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1222, ⟨64, (AddGraph.w36 s.p s.q)⟩),
      (1295, ⟨64, (AddGraph.w607 s.p s.q)⟩),
      (1311, ⟨64, (AddGraph.w610 s.p s.q)⟩),
      (1313, ⟨64, (AddGraph.w611 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w35 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w37 s.p s.q)),
      ((.stack 14), (s.fr.rsp - 424), (AddGraph.w23 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w21 s.p s.q)),
      ((.stack 24), (s.fr.rsp - 344), (AddGraph.w22 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment31 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_31 b_l10a410_32 := by
  replay_segment 31
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1291, ⟨64, (AddGraph.w606 s.p s.q)⟩),
      (1299, ⟨64, (AddGraph.w19 s.p s.q)⟩),
      (1328, ⟨64, (AddGraph.w614 s.p s.q)⟩),
      (1339, ⟨64, (AddGraph.w35 s.p s.q)⟩),
      (1356, ⟨64, (AddGraph.w627 s.p s.q)⟩),
      (1359, ⟨64, (AddGraph.w630 s.p s.q)⟩)]
    loads [((.stack 3), (s.fr.rsp - 512), (AddGraph.w34 s.p s.q)),
      ((.stack 4), (s.fr.rsp - 504), (AddGraph.w609 s.p s.q)),
      ((.stack 12), (s.fr.rsp - 440), (AddGraph.w608 s.p s.q)),
      ((.stack 23), (s.fr.rsp - 352), (AddGraph.w20 s.p s.q))]
    stores [((.stack 12), 646, (s.fr.rsp - 440), (AddGraph.w646 s.p s.q)),
      ((.stack 4), 647, (s.fr.rsp - 504), (AddGraph.w647 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment32 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_32 b_l10a410_33 := by
  replay_segment 32
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1315, ⟨64, (AddGraph.w37 s.p s.q)⟩),
      (1319, ⟨64, (AddGraph.w21 s.p s.q)⟩),
      (1390, ⟨64, (AddGraph.w641 s.p s.q)⟩),
      (1399, ⟨64, (AddGraph.w34 s.p s.q)⟩),
      (1401, ⟨64, (AddGraph.w20 s.p s.q)⟩)]
    loads [((.stack 6), (s.fr.rsp - 488), (AddGraph.w36 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w38 s.p s.q)),
      ((.stack 14), (s.fr.rsp - 424), (AddGraph.w23 s.p s.q)),
      ((.stack 24), (s.fr.rsp - 344), (AddGraph.w22 s.p s.q))]
    stores [((.stack 13), 649, (s.fr.rsp - 432), (AddGraph.w649 s.p s.q)),
      ((.stack 59), 653, (s.fr.rsp - 64), (AddGraph.w653 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment33 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_33 b_l10a410_34 := by
  replay_segment 33
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1366, ⟨64, (AddGraph.w635 s.p s.q)⟩),
      (1388, ⟨64, (AddGraph.w645 s.p s.q)⟩),
      (1406, ⟨64, (AddGraph.w648 s.p s.q)⟩),
      (1416, ⟨64, (AddGraph.w652 s.p s.q)⟩),
      (1418, ⟨64, (AddGraph.w651 s.p s.q)⟩),
      (1420, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (1432, ⟨64, (AddGraph.w655 s.p s.q)⟩),
      (1434, ⟨64, (AddGraph.w656 s.p s.q)⟩),
      (1436, ⟨64, (AddGraph.w36 s.p s.q)⟩),
      (1442, ⟨64, (AddGraph.w658 s.p s.q)⟩),
      (1443, ⟨64, (AddGraph.w657 s.p s.q)⟩)]
    loads [((.stack 4), (s.fr.rsp - 504), (AddGraph.w647 s.p s.q)),
      ((.stack 12), (s.fr.rsp - 440), (AddGraph.w646 s.p s.q)),
      ((.stack 13), (s.fr.rsp - 432), (AddGraph.w649 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment34 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_34 b_l10a410_35 := by
  replay_segment 34
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1401, ⟨64, (AddGraph.w20 s.p s.q)⟩),
      (1409, ⟨64, (AddGraph.w38 s.p s.q)⟩),
      (1427, ⟨64, (AddGraph.w22 s.p s.q)⟩),
      (1440, ⟨64, (AddGraph.w23 s.p s.q)⟩),
      (1488, ⟨64, (AddGraph.w683 s.p s.q)⟩),
      (1490, ⟨64, (AddGraph.w36 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w35 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w34 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w37 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w21 s.p s.q)),
      ((.stack 26), (s.fr.rsp - 328), (AddGraph.w19 s.p s.q))]
    stores [((.stack 13), 694, (s.fr.rsp - 432), (AddGraph.w694 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment35 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_35 b_l10a410_36 := by
  replay_segment 35
    regs [(1460, ⟨64, (AddGraph.w671 s.p s.q)⟩),
      (1486, ⟨64, (AddGraph.w687 s.p s.q)⟩),
      (1495, ⟨64, (AddGraph.w688 s.p s.q)⟩),
      (1497, ⟨64, (AddGraph.w689 s.p s.q)⟩),
      (1504, ⟨64, (AddGraph.w690 s.p s.q)⟩),
      (1506, ⟨64, (AddGraph.w691 s.p s.q)⟩),
      (1513, ⟨64, (AddGraph.w693 s.p s.q)⟩),
      (1515, ⟨64, (AddGraph.w692 s.p s.q)⟩),
      (1517, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (1527, ⟨64, (AddGraph.w695 s.p s.q)⟩),
      (1529, ⟨64, (AddGraph.w696 s.p s.q)⟩),
      (1533, ⟨64, (AddGraph.w698 s.p s.q)⟩),
      (1534, ⟨64, (AddGraph.w697 s.p s.q)⟩)]
    loads []
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment36 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_36 b_l10a410_37 := by
  replay_segment 36
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1517, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (1552, ⟨64, (AddGraph.w82 s.p s.q)⟩),
      (1577, ⟨64, (AddGraph.w726 s.p s.q)⟩),
      (1579, ⟨64, (AddGraph.w727 s.p s.q)⟩),
      (1581, ⟨64, (AddGraph.w728 s.p s.q)⟩)]
    loads [((.stack 7), (s.fr.rsp - 480), (AddGraph.w32 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w14 s.p s.q)),
      ((.stack 21), (s.fr.rsp - 368), (AddGraph.w9 s.p s.q)),
      ((.stack 25), (s.fr.rsp - 336), (AddGraph.w27 s.p s.q)),
      ((.stack 27), (s.fr.rsp - 320), (AddGraph.w562 s.p s.q))]
    stores [((.stack 58), 728, (s.fr.rsp - 72), (AddGraph.w728 s.p s.q)),
      ((.stack 38), 744, (s.fr.rsp - 232), (AddGraph.w744 s.p s.q)),
      ((.stack 18), 746, (s.fr.rsp - 392), (AddGraph.w746 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment37 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_37 b_l10a410_38 := by
  replay_segment 37
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1621, ⟨64, (AddGraph.w750 s.p s.q)⟩),
      (1622, ⟨64, (AddGraph.w749 s.p s.q)⟩)]
    loads [((.stack 2), (s.fr.rsp - 520), (AddGraph.w30 s.p s.q)),
      ((.stack 5), (s.fr.rsp - 496), (AddGraph.w16 s.p s.q)),
      ((.stack 15), (s.fr.rsp - 416), (AddGraph.w31 s.p s.q)),
      ((.stack 20), (s.fr.rsp - 376), (AddGraph.w26 s.p s.q)),
      ((.stack 22), (s.fr.rsp - 360), (AddGraph.w15 s.p s.q)),
      ((.stack 31), (s.fr.rsp - 288), (AddGraph.w10 s.p s.q)),
      ((.stack 41), (s.fr.rsp - 208), (AddGraph.w25 s.p s.q)),
      ((.stack 43), (s.fr.rsp - 192), (AddGraph.w11 s.p s.q))]
    stores [((.stack 29), 750, (s.fr.rsp - 304), (AddGraph.w750 s.p s.q)),
      ((.stack 12), 749, (s.fr.rsp - 440), (AddGraph.w749 s.p s.q)),
      ((.stack 33), 753, (s.fr.rsp - 272), (AddGraph.w753 s.p s.q)),
      ((.stack 46), 752, (s.fr.rsp - 168), (AddGraph.w752 s.p s.q)),
      ((.stack 49), 757, (s.fr.rsp - 144), (AddGraph.w757 s.p s.q)),
      ((.stack 54), 756, (s.fr.rsp - 104), (AddGraph.w756 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment38 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_38 b_l10a410_39 := by
  replay_segment 38
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1649, ⟨64, (AddGraph.w762 s.p s.q)⟩),
      (1655, ⟨64, (AddGraph.w764 s.p s.q)⟩),
      (1657, ⟨64, (AddGraph.w764 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w29 s.p s.q)),
      ((.stack 17), (s.fr.rsp - 400), (AddGraph.w17 s.p s.q)),
      ((.stack 19), (s.fr.rsp - 384), (AddGraph.w601 s.p s.q)),
      ((.stack 28), (s.fr.rsp - 312), (AddGraph.w12 s.p s.q)),
      ((.stack 40), (s.fr.rsp - 216), (AddGraph.w24 s.p s.q)),
      ((.stack 56), (s.fr.rsp - 88), (AddGraph.w13 s.p s.q))]
    stores [((.stack 35), 764, (s.fr.rsp - 256), (AddGraph.w764 s.p s.q)),
      ((.stack 51), 762, (s.fr.rsp - 128), (AddGraph.w762 s.p s.q)),
      ((.stack 57), 770, (s.fr.rsp - 80), (AddGraph.w770 s.p s.q)),
      ((.stack 8), 772, (s.fr.rsp - 472), (AddGraph.w772 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment39 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_39 b_l10a410_40 := by
  replay_segment 39
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1600, ⟨64, (AddGraph.w737 s.p s.q)⟩),
      (1605, ⟨64, (AddGraph.w741 s.p s.q)⟩),
      (1664, ⟨64, (AddGraph.w767 s.p s.q)⟩),
      (1685, ⟨64, (AddGraph.w775 s.p s.q)⟩),
      (1693, ⟨64, (AddGraph.w776 s.p s.q)⟩),
      (1695, ⟨64, (AddGraph.w13 s.p s.q)⟩)]
    loads [((.stack 30), (s.fr.rsp - 296), (AddGraph.w18 s.p s.q)),
      ((.stack 32), (s.fr.rsp - 280), (AddGraph.w33 s.p s.q)),
      ((.stack 34), (s.fr.rsp - 264), (AddGraph.w28 s.p s.q))]
    stores [((.stack 4), 778, (s.fr.rsp - 504), (AddGraph.w778 s.p s.q)),
      ((.stack 36), 780, (s.fr.rsp - 248), (AddGraph.w780 s.p s.q)),
      ((.stack 19), 784, (s.fr.rsp - 384), (AddGraph.w784 s.p s.q)),
      ((.stack 27), 789, (s.fr.rsp - 320), (AddGraph.w789 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment40 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_40 b_l10a410_41 := by
  replay_segment 40
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1630, ⟨64, (AddGraph.w752 s.p s.q)⟩),
      (1666, ⟨64, (AddGraph.w766 s.p s.q)⟩),
      (1687, ⟨64, (AddGraph.w774 s.p s.q)⟩),
      (1706, ⟨64, (AddGraph.w780 s.p s.q)⟩),
      (1714, ⟨64, (AddGraph.w783 s.p s.q)⟩),
      (1716, ⟨64, (AddGraph.w782 s.p s.q)⟩),
      (1727, ⟨64, (AddGraph.w788 s.p s.q)⟩),
      (1728, ⟨64, (AddGraph.w787 s.p s.q)⟩),
      (1733, ⟨64, (AddGraph.w790 s.p s.q)⟩),
      (1734, Value.ofBool (addSpec (AddGraph.w775 s.p s.q) (AddGraph.w767 s.p s.q)).2.CF)]
    loads [((.stack 12), (s.fr.rsp - 440), (AddGraph.w749 s.p s.q)),
      ((.stack 18), (s.fr.rsp - 392), (AddGraph.w746 s.p s.q)),
      ((.stack 29), (s.fr.rsp - 304), (AddGraph.w750 s.p s.q)),
      ((.stack 33), (s.fr.rsp - 272), (AddGraph.w753 s.p s.q)),
      ((.stack 38), (s.fr.rsp - 232), (AddGraph.w744 s.p s.q)),
      ((.stack 49), (s.fr.rsp - 144), (AddGraph.w757 s.p s.q)),
      ((.stack 54), (s.fr.rsp - 104), (AddGraph.w756 s.p s.q))]
    stores [((.stack 54), 802, (s.fr.rsp - 104), (AddGraph.w802 s.p s.q)),
      ((.stack 12), 808, (s.fr.rsp - 440), (AddGraph.w808 s.p s.q)),
      ((.stack 29), 809, (s.fr.rsp - 304), (AddGraph.w809 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment41 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_41 b_l10a410_42 := by
  replay_segment 41
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1649, ⟨64, (AddGraph.w762 s.p s.q)⟩),
      (1655, ⟨64, (AddGraph.w764 s.p s.q)⟩),
      (1754, ⟨64, (AddGraph.w806 s.p s.q)⟩),
      (1776, ⟨64, (AddGraph.w753 s.p s.q)⟩)]
    loads [((.stack 4), (s.fr.rsp - 504), (AddGraph.w778 s.p s.q)),
      ((.stack 8), (s.fr.rsp - 472), (AddGraph.w772 s.p s.q)),
      ((.stack 57), (s.fr.rsp - 80), (AddGraph.w770 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment42 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_42 b_l10a410_43 := by
  replay_segment 42
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1756, ⟨64, (AddGraph.w807 s.p s.q)⟩),
      (1760, ⟨64, (AddGraph.w744 s.p s.q)⟩),
      (1772, ⟨64, (AddGraph.w810 s.p s.q)⟩),
      (1774, ⟨64, (AddGraph.w811 s.p s.q)⟩),
      (1796, ⟨64, (AddGraph.w772 s.p s.q)⟩),
      (1811, ⟨64, (AddGraph.w819 s.p s.q)⟩),
      (1812, ⟨64, (AddGraph.w818 s.p s.q)⟩),
      (1819, ⟨64, (AddGraph.w824 s.p s.q)⟩),
      (1822, ⟨64, (AddGraph.w827 s.p s.q)⟩)]
    loads [((.stack 12), (s.fr.rsp - 440), (AddGraph.w808 s.p s.q)),
      ((.stack 29), (s.fr.rsp - 304), (AddGraph.w809 s.p s.q)),
      ((.stack 36), (s.fr.rsp - 248), (AddGraph.w780 s.p s.q)),
      ((.stack 46), (s.fr.rsp - 168), (AddGraph.w752 s.p s.q))]
    stores [((.stack 29), 840, (s.fr.rsp - 304), (AddGraph.w840 s.p s.q)),
      ((.stack 12), 847, (s.fr.rsp - 440), (AddGraph.w847 s.p s.q))]

theorem segments28To42 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_28 b_l10a410_43 :=
  BodySegment.trans
    (BodySegment.trans
      (BodySegment.trans
        (segment28 inc s r)
        (BodySegment.trans
          (segment29 inc s r)
          (segment30 inc s r)))
      (BodySegment.trans
        (BodySegment.trans
          (segment31 inc s r)
          (segment32 inc s r))
        (BodySegment.trans
          (segment33 inc s r)
          (segment34 inc s r))))
    (BodySegment.trans
      (BodySegment.trans
        (BodySegment.trans
          (segment35 inc s r)
          (segment36 inc s r))
        (BodySegment.trans
          (segment37 inc s r)
          (segment38 inc s r)))
      (BodySegment.trans
        (BodySegment.trans
          (segment39 inc s r)
          (segment40 inc s r))
        (BodySegment.trans
          (segment41 inc s r)
          (segment42 inc s r))))

end K256.Proofs.Generate.Generator.Multiply.AddReplay
