import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment86 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_86 b_l10a410_87 := by
  replay_segment 86
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3430, ⟨64, (AddGraph.w315 s.p s.q)⟩),
      (3517, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (3581, ⟨64, (AddGraph.w308 s.p s.q)⟩),
      (3619, ⟨64, (AddGraph.w1595 s.p s.q)⟩),
      (3631, ⟨64, (AddGraph.w1604 s.p s.q)⟩),
      (3637, ⟨64, (AddGraph.w180 s.p s.q)⟩),
      (3655, ⟨64, (AddGraph.w1617 s.p s.q)⟩),
      (3657, ⟨64, (AddGraph.w1613 s.p s.q)⟩)]
    loads [((.stack 53), (s.fr.rsp - 112), (AddGraph.w195 s.p s.q))]
    stores [((.stack 28), 1629, (s.fr.rsp - 312), (AddGraph.w1629 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment87 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_87 b_l10a410_88 := by
  replay_segment 87
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3581, ⟨64, (AddGraph.w308 s.p s.q)⟩),
      (3686, ⟨64, (AddGraph.w1632 s.p s.q)⟩),
      (3692, ⟨64, (AddGraph.w1634 s.p s.q)⟩),
      (3696, ⟨64, (AddGraph.w195 s.p s.q)⟩)]
    loads [((.stack 44), (s.fr.rsp - 184), (AddGraph.w236 s.p s.q)),
      ((.stack 47), (s.fr.rsp - 160), (AddGraph.w320 s.p s.q)),
      ((.stack 52), (s.fr.rsp - 120), (AddGraph.w270 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment88 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_88 b_l10a410_89 := by
  replay_segment 88
    regs [(3517, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (3694, ⟨64, (AddGraph.w180 s.p s.q)⟩),
      (3700, ⟨64, (AddGraph.w1637 s.p s.q)⟩),
      (3710, ⟨64, (AddGraph.w1642 s.p s.q)⟩),
      (3720, ⟨64, (AddGraph.w1647 s.p s.q)⟩),
      (3732, ⟨64, (AddGraph.w1654 s.p s.q)⟩),
      (3736, ⟨64, (AddGraph.w1652 s.p s.q)⟩)]
    loads []
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment89 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_89 b_l10a410_90 := by
  replay_segment 89
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3517, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (3641, ⟨64, (AddGraph.w1607 s.p s.q)⟩),
      (3651, ⟨64, (AddGraph.w1613 s.p s.q)⟩),
      (3669, ⟨64, (AddGraph.w1619 s.p s.q)⟩),
      (3679, ⟨64, (AddGraph.w1625 s.p s.q)⟩),
      (3730, ⟨64, (AddGraph.w1652 s.p s.q)⟩),
      (3734, ⟨64, (AddGraph.w308 s.p s.q)⟩),
      (3744, ⟨64, (AddGraph.w1659 s.p s.q)⟩),
      (3770, ⟨64, (AddGraph.w1671 s.p s.q)⟩),
      (3776, ⟨64, (AddGraph.w1674 s.p s.q)⟩)]
    loads []
    stores [((.stack 32), 1683, (s.fr.rsp - 280), (AddGraph.w1683 s.p s.q)),
      ((.stack 13), 1685, (s.fr.rsp - 432), (AddGraph.w1685 s.p s.q)),
      ((.stack 31), 1686, (s.fr.rsp - 288), (AddGraph.w1686 s.p s.q)),
      ((.stack 21), 1687, (s.fr.rsp - 368), (AddGraph.w1687 s.p s.q)),
      ((.stack 25), 1688, (s.fr.rsp - 336), (AddGraph.w1688 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment90 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_90 b_l10a410_91 := by
  replay_segment 90
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3517, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (3551, ⟨64, (AddGraph.w1566 s.p s.q)⟩),
      (3762, ⟨64, (AddGraph.w1665 s.p s.q)⟩),
      (3768, ⟨64, (AddGraph.w1670 s.p s.q)⟩)]
    loads [((.stack 5), (s.fr.rsp - 496), (AddGraph.w1556 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w1561 s.p s.q)),
      ((.stack 12), (s.fr.rsp - 440), (AddGraph.w998 s.p s.q)),
      ((.stack 35), (s.fr.rsp - 256), (AddGraph.w1003 s.p s.q)),
      ((.stack 36), (s.fr.rsp - 248), (AddGraph.w1001 s.p s.q))]
    stores [((.stack 41), 1689, (s.fr.rsp - 208), (AddGraph.w1689 s.p s.q)),
      ((.stack 23), 1690, (s.fr.rsp - 352), (AddGraph.w1690 s.p s.q)),
      ((.stack 17), 1691, (s.fr.rsp - 400), (AddGraph.w1691 s.p s.q)),
      ((.stack 34), 1693, (s.fr.rsp - 264), (AddGraph.w1693 s.p s.q)),
      ((.stack 20), 1692, (s.fr.rsp - 376), (AddGraph.w1692 s.p s.q)),
      ((.stack 43), 1694, (s.fr.rsp - 192), (AddGraph.w1694 s.p s.q)),
      ((.stack 19), 1695, (s.fr.rsp - 384), (AddGraph.w1695 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment91 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_91 b_l10a410_92 := by
  replay_segment 91
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3778, ⟨64, (AddGraph.w1675 s.p s.q)⟩),
      (3794, ⟨64, (AddGraph.w1680 s.p s.q)⟩),
      (3845, ⟨64, (AddGraph.w1696 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w1549 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w1572 s.p s.q)),
      ((.stack 29), (s.fr.rsp - 304), (AddGraph.w1041 s.p s.q)),
      ((.stack 33), (s.fr.rsp - 272), (AddGraph.w1005 s.p s.q))]
    stores [((.stack 27), 1696, (s.fr.rsp - 320), (AddGraph.w1696 s.p s.q)),
      ((.stack 40), 1701, (s.fr.rsp - 216), (AddGraph.w1701 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment92 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_92 b_l10a410_93 := by
  replay_segment 92
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3820, ⟨64, (AddGraph.w998 s.p s.q)⟩),
      (3829, ⟨64, (AddGraph.w1001 s.p s.q)⟩),
      (3857, ⟨64, (AddGraph.w1697 s.p s.q)⟩),
      (3859, ⟨64, (AddGraph.w1698 s.p s.q)⟩),
      (3861, ⟨64, (AddGraph.w1572 s.p s.q)⟩),
      (3870, ⟨64, (AddGraph.w1700 s.p s.q)⟩),
      (3872, ⟨64, (AddGraph.w1699 s.p s.q)⟩),
      (3885, ⟨64, (AddGraph.w1704 s.p s.q)⟩),
      (3886, ⟨64, (AddGraph.w1703 s.p s.q)⟩),
      (3888, ⟨64, (AddGraph.w1705 s.p s.q)⟩)]
    loads [((.stack 6), (s.fr.rsp - 488), (AddGraph.w1561 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w1566 s.p s.q)),
      ((.stack 17), (s.fr.rsp - 400), (AddGraph.w1691 s.p s.q)),
      ((.stack 19), (s.fr.rsp - 384), (AddGraph.w1695 s.p s.q)),
      ((.stack 20), (s.fr.rsp - 376), (AddGraph.w1692 s.p s.q)),
      ((.stack 23), (s.fr.rsp - 352), (AddGraph.w1690 s.p s.q)),
      ((.stack 27), (s.fr.rsp - 320), (AddGraph.w1696 s.p s.q)),
      ((.stack 34), (s.fr.rsp - 264), (AddGraph.w1693 s.p s.q))]
    stores [((.stack 39), 1705, (s.fr.rsp - 224), (AddGraph.w1705 s.p s.q)),
      ((.stack 23), 1718, (s.fr.rsp - 352), (AddGraph.w1718 s.p s.q)),
      ((.stack 17), 1723, (s.fr.rsp - 400), (AddGraph.w1723 s.p s.q)),
      ((.stack 20), 1724, (s.fr.rsp - 376), (AddGraph.w1724 s.p s.q)),
      ((.stack 34), 1725, (s.fr.rsp - 264), (AddGraph.w1725 s.p s.q)),
      ((.stack 19), 1726, (s.fr.rsp - 384), (AddGraph.w1726 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment93 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_93 b_l10a410_94 := by
  replay_segment 93
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3839, ⟨64, (AddGraph.w1556 s.p s.q)⟩),
      (3843, ⟨64, (AddGraph.w1003 s.p s.q)⟩),
      (3852, ⟨64, (AddGraph.w1005 s.p s.q)⟩),
      (3865, ⟨64, (AddGraph.w1041 s.p s.q)⟩),
      (3872, ⟨64, (AddGraph.w1699 s.p s.q)⟩),
      (3910, ⟨64, (AddGraph.w1721 s.p s.q)⟩),
      (3912, ⟨64, (AddGraph.w1722 s.p s.q)⟩),
      (3928, ⟨64, (AddGraph.w1561 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w1549 s.p s.q)),
      ((.stack 23), (s.fr.rsp - 352), (AddGraph.w1718 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment94 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_94 b_l10a410_95 := by
  replay_segment 94
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3910, ⟨64, (AddGraph.w1721 s.p s.q)⟩),
      (3933, ⟨64, (AddGraph.w1727 s.p s.q)⟩),
      (3935, ⟨64, (AddGraph.w1728 s.p s.q)⟩),
      (3942, ⟨64, (AddGraph.w1729 s.p s.q)⟩),
      (3944, ⟨64, (AddGraph.w1730 s.p s.q)⟩),
      (3953, ⟨64, (AddGraph.w1732 s.p s.q)⟩),
      (3955, ⟨64, (AddGraph.w1731 s.p s.q)⟩),
      (3965, ⟨64, (AddGraph.w1736 s.p s.q)⟩),
      (3968, ⟨64, (AddGraph.w1737 s.p s.q)⟩),
      (3970, ⟨64, (AddGraph.w1721 s.p s.q)⟩),
      (3972, ⟨64, (AddGraph.w1718 s.p s.q)⟩)]
    loads [((.stack 17), (s.fr.rsp - 400), (AddGraph.w1723 s.p s.q)),
      ((.stack 19), (s.fr.rsp - 384), (AddGraph.w1726 s.p s.q)),
      ((.stack 20), (s.fr.rsp - 376), (AddGraph.w1724 s.p s.q)),
      ((.stack 34), (s.fr.rsp - 264), (AddGraph.w1725 s.p s.q))]
    stores [((.stack 19), 1761, (s.fr.rsp - 384), (AddGraph.w1761 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment95 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_95 b_l10a410_96 := by
  replay_segment 95
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (3946, ⟨64, (AddGraph.w1549 s.p s.q)⟩),
      (4017, ⟨64, (AddGraph.w1767 s.p s.q)⟩)]
    loads [((.stack 5), (s.fr.rsp - 496), (AddGraph.w1556 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w1561 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w1572 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w1566 s.p s.q)),
      ((.stack 12), (s.fr.rsp - 440), (AddGraph.w998 s.p s.q)),
      ((.stack 33), (s.fr.rsp - 272), (AddGraph.w1005 s.p s.q)),
      ((.stack 35), (s.fr.rsp - 256), (AddGraph.w1003 s.p s.q)),
      ((.stack 36), (s.fr.rsp - 248), (AddGraph.w1001 s.p s.q))]
    stores [((.stack 17), 1768, (s.fr.rsp - 400), (AddGraph.w1768 s.p s.q)),
      ((.stack 20), 1769, (s.fr.rsp - 376), (AddGraph.w1769 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment96 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_96 b_l10a410_97 := by
  replay_segment 96
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4011, ⟨64, (AddGraph.w1765 s.p s.q)⟩),
      (4013, ⟨64, (AddGraph.w1766 s.p s.q)⟩),
      (4033, ⟨64, (AddGraph.w1770 s.p s.q)⟩),
      (4035, ⟨64, (AddGraph.w1771 s.p s.q)⟩),
      (4042, ⟨64, (AddGraph.w1773 s.p s.q)⟩),
      (4044, ⟨64, (AddGraph.w1772 s.p s.q)⟩),
      (4046, ⟨64, (AddGraph.w1774 s.p s.q)⟩),
      (4055, ⟨64, (AddGraph.w1775 s.p s.q)⟩),
      (4057, ⟨64, (AddGraph.w1776 s.p s.q)⟩),
      (4059, ⟨64, (AddGraph.w1556 s.p s.q)⟩)]
    loads [((.stack 29), (s.fr.rsp - 304), (AddGraph.w1041 s.p s.q))]
    stores []

theorem segments86To96 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_86 b_l10a410_97 :=
  BodySegment.trans (BodySegment.trans (BodySegment.trans (segment86 inc s r)
        (segment87 inc s r))
      (BodySegment.trans (segment88 inc s r)
        (BodySegment.trans (segment89 inc s r)
          (segment90 inc s r))))
    (BodySegment.trans (BodySegment.trans (segment91 inc s r)
        (BodySegment.trans (segment92 inc s r)
          (segment93 inc s r)))
      (BodySegment.trans (segment94 inc s r)
        (BodySegment.trans (segment95 inc s r)
          (segment96 inc s r))))

end K256.Proofs.Generate.Generator.Multiply.AddReplay
