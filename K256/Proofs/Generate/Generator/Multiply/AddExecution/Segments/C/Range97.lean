import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment97 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_97 b_l10a410_98 := by
  replay_segment 97
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4021, ⟨64, (AddGraph.w998 s.p s.q)⟩),
      (4059, ⟨64, (AddGraph.w1556 s.p s.q)⟩),
      (4104, ⟨64, (AddGraph.w1801 s.p s.q)⟩),
      (4105, ⟨64, (AddGraph.w1800 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w1549 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w1572 s.p s.q)),
      ((.stack 17), (s.fr.rsp - 400), (AddGraph.w1768 s.p s.q)),
      ((.stack 20), (s.fr.rsp - 376), (AddGraph.w1769 s.p s.q)),
      ((.stack 35), (s.fr.rsp - 256), (AddGraph.w1003 s.p s.q)),
      ((.stack 36), (s.fr.rsp - 248), (AddGraph.w1001 s.p s.q))]
    stores [((.stack 20), 1808, (s.fr.rsp - 376), (AddGraph.w1808 s.p s.q)),
      ((.stack 27), 1809, (s.fr.rsp - 320), (AddGraph.w1809 s.p s.q)),
      ((.stack 17), 1811, (s.fr.rsp - 400), (AddGraph.w1811 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment98 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_98 b_l10a410_99 := by
  replay_segment 98
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4050, ⟨64, (AddGraph.w1005 s.p s.q)⟩),
      (4063, ⟨64, (AddGraph.w1041 s.p s.q)⟩),
      (4090, ⟨64, (AddGraph.w1795 s.p s.q)⟩),
      (4100, ⟨64, (AddGraph.w1799 s.p s.q)⟩),
      (4120, ⟨64, (AddGraph.w1802 s.p s.q)⟩),
      (4144, ⟨64, (AddGraph.w1813 s.p s.q)⟩),
      (4146, ⟨64, (AddGraph.w1812 s.p s.q)⟩)]
    loads [((.stack 6), (s.fr.rsp - 488), (AddGraph.w1561 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w1566 s.p s.q))]
    stores [((.stack 34), 1814, (s.fr.rsp - 264), (AddGraph.w1814 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment99 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_99 b_l10a410_100 := by
  replay_segment 99
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4116, ⟨64, (AddGraph.w1806 s.p s.q)⟩),
      (4118, ⟨64, (AddGraph.w1807 s.p s.q)⟩),
      (4134, ⟨64, (AddGraph.w1810 s.p s.q)⟩),
      (4162, ⟨64, (AddGraph.w1561 s.p s.q)⟩),
      (4183, ⟨64, (AddGraph.w1827 s.p s.q)⟩),
      (4186, ⟨64, (AddGraph.w1830 s.p s.q)⟩),
      (4188, ⟨64, (AddGraph.w1827 s.p s.q)⟩),
      (4190, ⟨64, (AddGraph.w80 s.p s.q)⟩)]
    loads [((.stack 12), (s.fr.rsp - 440), (AddGraph.w998 s.p s.q)),
      ((.stack 17), (s.fr.rsp - 400), (AddGraph.w1811 s.p s.q)),
      ((.stack 20), (s.fr.rsp - 376), (AddGraph.w1808 s.p s.q)),
      ((.stack 27), (s.fr.rsp - 320), (AddGraph.w1809 s.p s.q))]
    stores [((.stack 20), 1850, (s.fr.rsp - 376), (AddGraph.w1850 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment100 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_100 b_l10a410_101 := by
  replay_segment 100
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4139, ⟨64, (AddGraph.w1003 s.p s.q)⟩),
      (4169, ⟨64, (AddGraph.w1041 s.p s.q)⟩),
      (4190, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (4226, ⟨64, (AddGraph.w1842 s.p s.q)⟩),
      (4232, ⟨64, (AddGraph.w1851 s.p s.q)⟩)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w1549 s.p s.q)),
      ((.stack 5), (s.fr.rsp - 496), (AddGraph.w1556 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w1572 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w1566 s.p s.q)),
      ((.stack 33), (s.fr.rsp - 272), (AddGraph.w1005 s.p s.q)),
      ((.stack 36), (s.fr.rsp - 248), (AddGraph.w1001 s.p s.q))]
    stores [((.stack 27), 1851, (s.fr.rsp - 320), (AddGraph.w1851 s.p s.q)),
      ((.stack 17), 1856, (s.fr.rsp - 400), (AddGraph.w1856 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment101 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_101 b_l10a410_102 := by
  replay_segment 101
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4218, ⟨64, (AddGraph.w1846 s.p s.q)⟩),
      (4220, ⟨64, (AddGraph.w1847 s.p s.q)⟩),
      (4224, ⟨64, (AddGraph.w1848 s.p s.q)⟩),
      (4228, ⟨64, (AddGraph.w1849 s.p s.q)⟩),
      (4242, ⟨64, (AddGraph.w1852 s.p s.q)⟩),
      (4244, ⟨64, (AddGraph.w1853 s.p s.q)⟩),
      (4251, ⟨64, (AddGraph.w1855 s.p s.q)⟩),
      (4253, ⟨64, (AddGraph.w1854 s.p s.q)⟩),
      (4263, ⟨64, (AddGraph.w1857 s.p s.q)⟩),
      (4272, ⟨64, (AddGraph.w1859 s.p s.q)⟩),
      (4276, ⟨64, (AddGraph.w1861 s.p s.q)⟩),
      (4277, Value.ofBool (addSpec (AddGraph.w1860 s.p s.q) (AddGraph.w1858 s.p s.q)).2.CF)]
    loads [((.stack 20), (s.fr.rsp - 376), (AddGraph.w1850 s.p s.q)),
      ((.stack 27), (s.fr.rsp - 320), (AddGraph.w1851 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment102 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_102 b_l10a410_103 := by
  replay_segment 102
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4288, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (4292, ⟨64, (AddGraph.w82 s.p s.q)⟩),
      (4312, ⟨64, (AddGraph.w1884 s.p s.q)⟩),
      (4315, ⟨64, (AddGraph.w1887 s.p s.q)⟩),
      (4317, ⟨64, (AddGraph.w1888 s.p s.q)⟩),
      (4319, ⟨64, (AddGraph.w1889 s.p s.q)⟩),
      (4323, ⟨64, (AddGraph.w1890 s.p s.q)⟩)]
    loads [((.stack 19), (s.fr.rsp - 384), (AddGraph.w1761 s.p s.q)),
      ((.stack 23), (s.fr.rsp - 352), (AddGraph.w1718 s.p s.q))]
    stores [((.stack 20), 1892, (s.fr.rsp - 376), (AddGraph.w1892 s.p s.q)),
      ((.stack 19), 1907, (s.fr.rsp - 384), (AddGraph.w1907 s.p s.q)),
      ((.stack 23), 1909, (s.fr.rsp - 352), (AddGraph.w1909 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment103 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_103 b_l10a410_104 := by
  replay_segment 103
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w1501 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w1497 s.p s.q)),
      ((.stack 13), (s.fr.rsp - 432), (AddGraph.w1685 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w1499 s.p s.q)),
      ((.stack 21), (s.fr.rsp - 368), (AddGraph.w1687 s.p s.q)),
      ((.stack 31), (s.fr.rsp - 288), (AddGraph.w1686 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment104 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_104 b_l10a410_105 := by
  replay_segment 104
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4288, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (4405, ⟨64, (AddGraph.w1920 s.p s.q)⟩),
      (4408, ⟨64, (AddGraph.w1923 s.p s.q)⟩)]
    loads [((.stack 2), (s.fr.rsp - 520), (AddGraph.w1505 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w1485 s.p s.q)),
      ((.stack 25), (s.fr.rsp - 336), (AddGraph.w1688 s.p s.q)),
      ((.stack 28), (s.fr.rsp - 312), (AddGraph.w1629 s.p s.q))]
    stores [((.stack 27), 1936, (s.fr.rsp - 320), (AddGraph.w1936 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment105 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_105 b_l10a410_106 := by
  replay_segment 105
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4365, ⟨64, (AddGraph.w1685 s.p s.q)⟩),
      (4369, ⟨64, (AddGraph.w1501 s.p s.q)⟩),
      (4378, ⟨64, (AddGraph.w1686 s.p s.q)⟩),
      (4396, ⟨64, (AddGraph.w1497 s.p s.q)⟩),
      (4410, ⟨64, (AddGraph.w1688 s.p s.q)⟩),
      (4426, ⟨64, (AddGraph.w1929 s.p s.q)⟩),
      (4432, ⟨64, (AddGraph.w1505 s.p s.q)⟩),
      (4448, ⟨64, (AddGraph.w1934 s.p s.q)⟩),
      (4450, ⟨64, (AddGraph.w1936 s.p s.q)⟩),
      (4451, Value.ofBool (addSpec (AddGraph.w1935 s.p s.q) (AddGraph.w1926 s.p s.q)).2.CF)]
    loads [((.stack 16), (s.fr.rsp - 408), (AddGraph.w1499 s.p s.q)),
      ((.stack 21), (s.fr.rsp - 368), (AddGraph.w1687 s.p s.q))]
    stores [((.stack 42), 1941, (s.fr.rsp - 200), (AddGraph.w1941 s.p s.q)),
      ((.stack 37), 1942, (s.fr.rsp - 240), (AddGraph.w1942 s.p s.q)),
      ((.stack 45), 1945, (s.fr.rsp - 176), (AddGraph.w1945 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment106 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_106 b_l10a410_107 := by
  replay_segment 106
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4414, ⟨64, (AddGraph.w1485 s.p s.q)⟩),
      (4428, ⟨64, (AddGraph.w1629 s.p s.q)⟩),
      (4439, ⟨64, (AddGraph.w1932 s.p s.q)⟩),
      (4456, ⟨64, (AddGraph.w1939 s.p s.q)⟩),
      (4458, ⟨64, (AddGraph.w1940 s.p s.q)⟩),
      (4472, ⟨64, (AddGraph.w1943 s.p s.q)⟩),
      (4474, ⟨64, (AddGraph.w1944 s.p s.q)⟩),
      (4484, ⟨64, (AddGraph.w1946 s.p s.q)⟩),
      (4491, ⟨64, (AddGraph.w1947 s.p s.q)⟩),
      (4493, ⟨64, (AddGraph.w1948 s.p s.q)⟩)]
    loads [((.stack 37), (s.fr.rsp - 240), (AddGraph.w1942 s.p s.q)),
      ((.stack 42), (s.fr.rsp - 200), (AddGraph.w1941 s.p s.q)),
      ((.stack 45), (s.fr.rsp - 176), (AddGraph.w1945 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment107 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_107 b_l10a410_108 := by
  replay_segment 107
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (4476, ⟨64, (AddGraph.w1687 s.p s.q)⟩),
      (4500, ⟨64, (AddGraph.w1485 s.p s.q)⟩),
      (4513, ⟨64, (AddGraph.w1953 s.p s.q)⟩),
      (4538, ⟨64, (AddGraph.w1973 s.p s.q)⟩),
      (4540, ⟨64, (AddGraph.w1974 s.p s.q)⟩),
      (4541, Value.ofBool (addSpec (AddGraph.w1970 s.p s.q) (AddGraph.w1940 s.p s.q)).2.CF)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w1501 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w1505 s.p s.q)),
      ((.stack 13), (s.fr.rsp - 432), (AddGraph.w1685 s.p s.q)),
      ((.stack 25), (s.fr.rsp - 336), (AddGraph.w1688 s.p s.q)),
      ((.stack 31), (s.fr.rsp - 288), (AddGraph.w1686 s.p s.q))]
    stores [((.stack 42), 1980, (s.fr.rsp - 200), (AddGraph.w1980 s.p s.q)),
      ((.stack 37), 1981, (s.fr.rsp - 240), (AddGraph.w1981 s.p s.q))]

theorem segments97To107 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_97 b_l10a410_108 :=
  BodySegment.trans (BodySegment.trans (BodySegment.trans (segment97 inc s r)
        (segment98 inc s r))
      (BodySegment.trans (segment99 inc s r)
        (BodySegment.trans (segment100 inc s r)
          (segment101 inc s r))))
    (BodySegment.trans (BodySegment.trans (segment102 inc s r)
        (BodySegment.trans (segment103 inc s r)
          (segment104 inc s r)))
      (BodySegment.trans (segment105 inc s r)
        (BodySegment.trans (segment106 inc s r)
          (segment107 inc s r))))

end K256.Proofs.Generate.Generator.Multiply.AddReplay
