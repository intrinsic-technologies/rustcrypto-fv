import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point
  K256.Proofs.Generate.Generator.Multiply.AddGraph K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment43 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_43 b_l10a410_44 := by
  replay_segment 43
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1787, ⟨64, (AddGraph.w770 s.p s.q)⟩),
      (1849, ⟨64, (AddGraph.w845 s.p s.q)⟩),
      (1865, ⟨64, (AddGraph.w849 s.p s.q)⟩),
      (1866, ⟨64, (AddGraph.w848 s.p s.q)⟩)]
    loads [((.stack 4), (s.fr.rsp - 504), (AddGraph.w778 s.p s.q)),
      ((.stack 18), (s.fr.rsp - 392), (AddGraph.w746 s.p s.q)),
      ((.stack 33), (s.fr.rsp - 272), (AddGraph.w753 s.p s.q)),
      ((.stack 35), (s.fr.rsp - 256), (AddGraph.w764 s.p s.q)),
      ((.stack 51), (s.fr.rsp - 128), (AddGraph.w762 s.p s.q))]
    stores [((.stack 49), 848, (s.fr.rsp - 144), (AddGraph.w848 s.p s.q)),
      ((.stack 60), 849, (s.fr.rsp - 56), (AddGraph.w849 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment44 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_44 b_l10a410_45 := by
  replay_segment 44
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1760, ⟨64, (AddGraph.w744 s.p s.q)⟩),
      (1847, ⟨64, (AddGraph.w844 s.p s.q)⟩),
      (1856, ⟨64, (AddGraph.w846 s.p s.q)⟩),
      (1883, ⟨64, (AddGraph.w853 s.p s.q)⟩),
      (1894, ⟨64, (AddGraph.w764 s.p s.q)⟩),
      (1906, ⟨64, (AddGraph.w862 s.p s.q)⟩),
      (1909, ⟨64, (AddGraph.w865 s.p s.q)⟩)]
    loads [((.stack 8), (s.fr.rsp - 472), (AddGraph.w772 s.p s.q)),
      ((.stack 12), (s.fr.rsp - 440), (AddGraph.w847 s.p s.q)),
      ((.stack 49), (s.fr.rsp - 144), (AddGraph.w848 s.p s.q)),
      ((.stack 60), (s.fr.rsp - 56), (AddGraph.w849 s.p s.q))]
    stores [((.stack 49), 885, (s.fr.rsp - 144), (AddGraph.w885 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment45 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_45 b_l10a410_46 := by
  replay_segment 45
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1859, ⟨64, (AddGraph.w780 s.p s.q)⟩),
      (1863, ⟨64, (AddGraph.w752 s.p s.q)⟩),
      (1870, ⟨64, (AddGraph.w746 s.p s.q)⟩),
      (1874, ⟨64, (AddGraph.w762 s.p s.q)⟩),
      (1943, ⟨64, (AddGraph.w880 s.p s.q)⟩),
      (1953, ⟨64, (AddGraph.w772 s.p s.q)⟩)]
    loads [((.stack 4), (s.fr.rsp - 504), (AddGraph.w778 s.p s.q)),
      ((.stack 33), (s.fr.rsp - 272), (AddGraph.w753 s.p s.q)),
      ((.stack 57), (s.fr.rsp - 80), (AddGraph.w770 s.p s.q))]
    stores [((.stack 12), 891, (s.fr.rsp - 440), (AddGraph.w891 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment46 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_46 b_l10a410_47 := by
  replay_segment 46
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1921, ⟨64, (AddGraph.w874 s.p s.q)⟩),
      (1941, ⟨64, (AddGraph.w884 s.p s.q)⟩),
      (1951, ⟨64, (AddGraph.w886 s.p s.q)⟩),
      (1958, ⟨64, (AddGraph.w887 s.p s.q)⟩),
      (1960, ⟨64, (AddGraph.w888 s.p s.q)⟩),
      (1967, ⟨64, (AddGraph.w890 s.p s.q)⟩),
      (1969, ⟨64, (AddGraph.w889 s.p s.q)⟩),
      (1971, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (1983, ⟨64, (AddGraph.w892 s.p s.q)⟩),
      (1987, ⟨64, (AddGraph.w753 s.p s.q)⟩),
      (1994, ⟨64, (AddGraph.w894 s.p s.q)⟩),
      (1996, ⟨64, (AddGraph.w896 s.p s.q)⟩),
      (1997, Value.ofBool (addSpec (AddGraph.w895 s.p s.q) (AddGraph.w893 s.p s.q)).2.CF)]
    loads [((.stack 38), (s.fr.rsp - 232), (AddGraph.w744 s.p s.q)),
      ((.stack 49), (s.fr.rsp - 144), (AddGraph.w885 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment47 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_47 b_l10a410_48 := by
  replay_segment 47
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (1978, ⟨64, (AddGraph.w770 s.p s.q)⟩),
      (1991, ⟨64, (AddGraph.w778 s.p s.q)⟩),
      (2015, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (2034, ⟨64, (AddGraph.w920 s.p s.q)⟩),
      (2043, ⟨64, (AddGraph.w926 s.p s.q)⟩),
      (2044, ⟨64, (AddGraph.w925 s.p s.q)⟩)]
    loads [((.stack 8), (s.fr.rsp - 472), (AddGraph.w772 s.p s.q)),
      ((.stack 18), (s.fr.rsp - 392), (AddGraph.w746 s.p s.q)),
      ((.stack 35), (s.fr.rsp - 256), (AddGraph.w764 s.p s.q)),
      ((.stack 36), (s.fr.rsp - 248), (AddGraph.w780 s.p s.q)),
      ((.stack 46), (s.fr.rsp - 168), (AddGraph.w752 s.p s.q)),
      ((.stack 51), (s.fr.rsp - 128), (AddGraph.w762 s.p s.q))]
    stores [((.stack 33), 925, (s.fr.rsp - 272), (AddGraph.w925 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment48 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_48 b_l10a410_49 := by
  replay_segment 48
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2011, ⟨64, (AddGraph.w908 s.p s.q)⟩),
      (2039, ⟨64, (AddGraph.w924 s.p s.q)⟩),
      (2047, ⟨64, (AddGraph.w926 s.p s.q)⟩),
      (2054, ⟨64, (AddGraph.w927 s.p s.q)⟩),
      (2056, ⟨64, (AddGraph.w928 s.p s.q)⟩),
      (2063, ⟨64, (AddGraph.w930 s.p s.q)⟩),
      (2065, ⟨64, (AddGraph.w929 s.p s.q)⟩),
      (2085, ⟨64, (AddGraph.w936 s.p s.q)⟩),
      (2088, ⟨64, (AddGraph.w939 s.p s.q)⟩)]
    loads [((.stack 33), (s.fr.rsp - 272), (AddGraph.w925 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment49 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_49 b_l10a410_50 := by
  replay_segment 49
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2097, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (2123, ⟨64, (AddGraph.w959 s.p s.q)⟩),
      (2130, ⟨64, (AddGraph.w964 s.p s.q)⟩),
      (2134, ⟨64, (AddGraph.w966 s.p s.q)⟩),
      (2135, ⟨64, (AddGraph.w965 s.p s.q)⟩)]
    loads [((.stack 12), (s.fr.rsp - 440), (AddGraph.w891 s.p s.q)),
      ((.stack 29), (s.fr.rsp - 304), (AddGraph.w840 s.p s.q)),
      ((.stack 42), (s.fr.rsp - 200), (AddGraph.w424 s.p s.q)),
      ((.stack 53), (s.fr.rsp - 112), (AddGraph.w195 s.p s.q)),
      ((.stack 54), (s.fr.rsp - 104), (AddGraph.w802 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment50 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_50 b_l10a410_51 := by
  replay_segment 50
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2067, ⟨64, (AddGraph.w931 s.p s.q)⟩),
      (2141, ⟨64, (AddGraph.w967 s.p s.q)⟩),
      (2147, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (2161, ⟨64, (AddGraph.w973 s.p s.q)⟩),
      (2169, ⟨64, (AddGraph.w979 s.p s.q)⟩),
      (2175, ⟨64, (AddGraph.w981 s.p s.q)⟩),
      (2177, ⟨64, (AddGraph.w891 s.p s.q)⟩)]
    loads [((.stack 37), (s.fr.rsp - 240), (AddGraph.w465 s.p s.q)),
      ((.stack 39), (s.fr.rsp - 224), (AddGraph.w543 s.p s.q)),
      ((.stack 44), (s.fr.rsp - 184), (AddGraph.w236 s.p s.q)),
      ((.stack 45), (s.fr.rsp - 176), (AddGraph.w500 s.p s.q)),
      ((.stack 47), (s.fr.rsp - 160), (AddGraph.w320 s.p s.q)),
      ((.stack 50), (s.fr.rsp - 136), (AddGraph.w315 s.p s.q)),
      ((.stack 52), (s.fr.rsp - 120), (AddGraph.w270 s.p s.q)),
      ((.stack 55), (s.fr.rsp - 96), (AddGraph.w548 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment51 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_51 b_l10a410_52 := by
  replay_segment 51
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2179, ⟨64, (AddGraph.w983 s.p s.q)⟩),
      (2187, ⟨64, (AddGraph.w986 s.p s.q)⟩),
      (2195, ⟨64, (AddGraph.w989 s.p s.q)⟩),
      (2205, ⟨64, (AddGraph.w993 s.p s.q)⟩),
      (2217, ⟨64, (AddGraph.w997 s.p s.q)⟩)]
    loads [((.stack 5), (s.fr.rsp - 496), (AddGraph.w16 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w14 s.p s.q)),
      ((.stack 14), (s.fr.rsp - 424), (AddGraph.w23 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w21 s.p s.q)),
      ((.stack 17), (s.fr.rsp - 400), (AddGraph.w17 s.p s.q)),
      ((.stack 22), (s.fr.rsp - 360), (AddGraph.w15 s.p s.q)),
      ((.stack 23), (s.fr.rsp - 352), (AddGraph.w20 s.p s.q)),
      ((.stack 24), (s.fr.rsp - 344), (AddGraph.w22 s.p s.q)),
      ((.stack 26), (s.fr.rsp - 328), (AddGraph.w19 s.p s.q)),
      ((.stack 30), (s.fr.rsp - 296), (AddGraph.w18 s.p s.q))]
    stores [((.stack 12), 998, (s.fr.rsp - 440), (AddGraph.w998 s.p s.q)),
      ((.stack 36), 1001, (s.fr.rsp - 248), (AddGraph.w1001 s.p s.q)),
      ((.stack 35), 1003, (s.fr.rsp - 256), (AddGraph.w1003 s.p s.q)),
      ((.stack 33), 1005, (s.fr.rsp - 272), (AddGraph.w1005 s.p s.q)),
      ((.stack 5), 1011, (s.fr.rsp - 496), (AddGraph.w1011 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment52 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_52 b_l10a410_53 := by
  replay_segment 52
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2235, ⟨64, (AddGraph.w1007 s.p s.q)⟩),
      (2239, ⟨64, (AddGraph.w1009 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w29 s.p s.q)),
      ((.stack 1), (s.fr.rsp - 528), (AddGraph.w35 s.p s.q)),
      ((.stack 2), (s.fr.rsp - 520), (AddGraph.w30 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w34 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w36 s.p s.q)),
      ((.stack 7), (s.fr.rsp - 480), (AddGraph.w32 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w37 s.p s.q)),
      ((.stack 15), (s.fr.rsp - 416), (AddGraph.w31 s.p s.q))]
    stores [((.stack 0), 1017, (s.fr.rsp - 536), (AddGraph.w1017 s.p s.q)),
      ((.stack 2), 1019, (s.fr.rsp - 520), (AddGraph.w1019 s.p s.q)),
      ((.stack 15), 1021, (s.fr.rsp - 416), (AddGraph.w1021 s.p s.q)),
      ((.stack 7), 1023, (s.fr.rsp - 480), (AddGraph.w1023 s.p s.q)),
      ((.stack 10), 1007, (s.fr.rsp - 456), (AddGraph.w1007 s.p s.q)),
      ((.stack 4), 1025, (s.fr.rsp - 504), (AddGraph.w1025 s.p s.q)),
      ((.stack 8), 1026, (s.fr.rsp - 472), (AddGraph.w1026 s.p s.q)),
      ((.stack 22), 1009, (s.fr.rsp - 360), (AddGraph.w1009 s.p s.q)),
      ((.stack 38), 1028, (s.fr.rsp - 232), (AddGraph.w1028 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment53 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_53 b_l10a410_54 := by
  replay_segment 53
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (2243, ⟨64, (AddGraph.w1011 s.p s.q)⟩),
      (2248, ⟨64, (AddGraph.w1013 s.p s.q)⟩),
      (2252, ⟨64, (AddGraph.w1015 s.p s.q)⟩),
      (2256, ⟨64, (AddGraph.w1017 s.p s.q)⟩),
      (2261, ⟨64, (AddGraph.w1019 s.p s.q)⟩),
      (2283, ⟨64, (AddGraph.w1027 s.p s.q)⟩)]
    loads [((.stack 9), (s.fr.rsp - 464), (AddGraph.w38 s.p s.q)),
      ((.stack 32), (s.fr.rsp - 280), (AddGraph.w33 s.p s.q))]
    stores [((.stack 18), 1027, (s.fr.rsp - 392), (AddGraph.w1027 s.p s.q)),
      ((.stack 17), 1013, (s.fr.rsp - 400), (AddGraph.w1013 s.p s.q)),
      ((.stack 32), 1029, (s.fr.rsp - 280), (AddGraph.w1029 s.p s.q)),
      ((.stack 30), 1015, (s.fr.rsp - 296), (AddGraph.w1015 s.p s.q))]


theorem segments43To53 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_43 b_l10a410_54 :=
  BodySegment.trans (segment43 inc s r) <|
    BodySegment.trans (segment44 inc s r) <|
    BodySegment.trans (segment45 inc s r) <|
    BodySegment.trans (segment46 inc s r) <|
    BodySegment.trans (segment47 inc s r) <|
    BodySegment.trans (segment48 inc s r) <|
    BodySegment.trans (segment49 inc s r) <|
    BodySegment.trans (segment50 inc s r) <|
    BodySegment.trans (segment51 inc s r) <|
    BodySegment.trans (segment52 inc s r) <|
    segment53 inc s r

end K256.Proofs.Generate.Generator.Multiply.AddReplay
