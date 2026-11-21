import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddReplay

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Point
  K256.Proofs.Generate.Generator.Multiply.AddGraph K256.Proofs.Sec1.Affine.Uncompressed

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment157 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_157 b_l10a410_158 := by
  replay_segment 157
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6629, ⟨64, (AddGraph.w2827 s.p s.q)⟩),
      (6647, ⟨64, (AddGraph.w2843 s.p s.q)⟩),
      (6649, ⟨64, (AddGraph.w2842 s.p s.q)⟩),
      (6653, ⟨64, (AddGraph.w2845 s.p s.q)⟩),
      (6663, ⟨64, (AddGraph.w2846 s.p s.q)⟩),
      (6665, ⟨64, (AddGraph.w2847 s.p s.q)⟩),
      (6672, ⟨64, (AddGraph.w2848 s.p s.q)⟩),
      (6674, ⟨64, (AddGraph.w2849 s.p s.q)⟩)]
    loads [((.stack 11), (s.fr.rsp - 448), (AddGraph.w2687 s.p s.q)),
      ((.stack 14), (s.fr.rsp - 424), (AddGraph.w2841 s.p s.q)),
      ((.stack 15), (s.fr.rsp - 416), (AddGraph.w2840 s.p s.q)),
      ((.stack 29), (s.fr.rsp - 304), (AddGraph.w1041 s.p s.q))]
    stores [((.stack 2), 2852, (s.fr.rsp - 520), (AddGraph.w2852 s.p s.q)),
      ((.stack 11), 2856, (s.fr.rsp - 448), (AddGraph.w2856 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment158 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_158 b_l10a410_159 := by
  replay_segment 158
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6631, ⟨64, (AddGraph.w1005 s.p s.q)⟩),
      (6640, ⟨64, (AddGraph.w1003 s.p s.q)⟩),
      (6656, ⟨64, (AddGraph.w1001 s.p s.q)⟩),
      (6676, ⟨64, (AddGraph.w1041 s.p s.q)⟩),
      (6683, ⟨64, (AddGraph.w2851 s.p s.q)⟩),
      (6685, ⟨64, (AddGraph.w2850 s.p s.q)⟩),
      (6697, ⟨64, (AddGraph.w2854 s.p s.q)⟩),
      (6715, ⟨64, (AddGraph.w2868 s.p s.q)⟩),
      (6718, Value.ofBool (addSpec (AddGraph.w2865 s.p s.q) (AddGraph.w2855 s.p s.q)).2.CF)]
    loads [((.stack 1), (s.fr.rsp - 528), (AddGraph.w2838 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w2836 s.p s.q)),
      ((.stack 4), (s.fr.rsp - 504), (AddGraph.w2834 s.p s.q)),
      ((.stack 8), (s.fr.rsp - 472), (AddGraph.w2832 s.p s.q))]
    stores [((.stack 15), 2874, (s.fr.rsp - 416), (AddGraph.w2874 s.p s.q)),
      ((.stack 14), 2875, (s.fr.rsp - 424), (AddGraph.w2875 s.p s.q)),
      ((.stack 22), 2876, (s.fr.rsp - 360), (AddGraph.w2876 s.p s.q)),
      ((.stack 30), 2877, (s.fr.rsp - 296), (AddGraph.w2877 s.p s.q)),
      ((.stack 44), 2878, (s.fr.rsp - 184), (AddGraph.w2878 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment159 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_159 b_l10a410_160 := by
  replay_segment 159
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6685, ⟨64, (AddGraph.w2850 s.p s.q)⟩),
      (6717, ⟨64, (AddGraph.w2869 s.p s.q)⟩),
      (6720, ⟨64, (AddGraph.w2872 s.p s.q)⟩),
      (6722, ⟨64, (AddGraph.w2873 s.p s.q)⟩),
      (6750, ⟨64, (AddGraph.w2879 s.p s.q)⟩),
      (6754, ⟨64, (AddGraph.w2881 s.p s.q)⟩),
      (6757, ⟨64, (AddGraph.w2880 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w2845 s.p s.q)),
      ((.stack 12), (s.fr.rsp - 440), (AddGraph.w998 s.p s.q)),
      ((.stack 30), (s.fr.rsp - 296), (AddGraph.w2877 s.p s.q)),
      ((.stack 44), (s.fr.rsp - 184), (AddGraph.w2878 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment160 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_160 b_l10a410_161 := by
  replay_segment 160
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6726, ⟨64, (AddGraph.w2832 s.p s.q)⟩),
      (6761, ⟨64, (AddGraph.w998 s.p s.q)⟩),
      (6780, ⟨64, (AddGraph.w2887 s.p s.q)⟩),
      (6783, ⟨64, (AddGraph.w2888 s.p s.q)⟩),
      (6787, ⟨64, (AddGraph.w2890 s.p s.q)⟩),
      (6789, ⟨64, (AddGraph.w2891 s.p s.q)⟩),
      (6799, ⟨64, (AddGraph.w2899 s.p s.q)⟩),
      (6801, ⟨64, (AddGraph.w2900 s.p s.q)⟩),
      (6802, Value.ofBool (addSpec (AddGraph.w2896 s.p s.q) (AddGraph.w2877 s.p s.q)).2.CF)]
    loads [((.stack 14), (s.fr.rsp - 424), (AddGraph.w2875 s.p s.q)),
      ((.stack 15), (s.fr.rsp - 416), (AddGraph.w2874 s.p s.q)),
      ((.stack 17), (s.fr.rsp - 400), (AddGraph.w2160 s.p s.q)),
      ((.stack 22), (s.fr.rsp - 360), (AddGraph.w2876 s.p s.q)),
      ((.stack 34), (s.fr.rsp - 264), (AddGraph.w2155 s.p s.q)),
      ((.stack 48), (s.fr.rsp - 152), s.fr.rdi)]
    stores [((.left 0), 2155, s.fr.rdi, (AddGraph.w2155 s.p s.q)),
      ((.left 1), 2160, (s.fr.rdi + 8), (AddGraph.w2160 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment161 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_161 b_l10a410_162 := by
  replay_segment 161
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6735, ⟨64, (AddGraph.w2834 s.p s.q)⟩),
      (6744, ⟨64, (AddGraph.w2836 s.p s.q)⟩),
      (6837, ⟨64, (AddGraph.w2918 s.p s.q)⟩),
      (6843, ⟨64, (AddGraph.w2920 s.p s.q)⟩),
      (6844, ⟨64, (AddGraph.w2919 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w2845 s.p s.q)),
      ((.stack 1), (s.fr.rsp - 528), (AddGraph.w2838 s.p s.q)),
      ((.stack 29), (s.fr.rsp - 304), (AddGraph.w1041 s.p s.q)),
      ((.stack 33), (s.fr.rsp - 272), (AddGraph.w1005 s.p s.q)),
      ((.stack 35), (s.fr.rsp - 256), (AddGraph.w1003 s.p s.q)),
      ((.stack 36), (s.fr.rsp - 248), (AddGraph.w1001 s.p s.q))]
    stores [((.stack 15), 2919, (s.fr.rsp - 416), (AddGraph.w2919 s.p s.q)),
      ((.stack 14), 2920, (s.fr.rsp - 424), (AddGraph.w2920 s.p s.q)),
      ((.stack 22), 2921, (s.fr.rsp - 360), (AddGraph.w2921 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment162 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_162 b_l10a410_163 := by
  replay_segment 162
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6831, ⟨64, (AddGraph.w2916 s.p s.q)⟩),
      (6833, ⟨64, (AddGraph.w2917 s.p s.q)⟩),
      (6854, ⟨64, (AddGraph.w2922 s.p s.q)⟩),
      (6861, ⟨64, (AddGraph.w2924 s.p s.q)⟩),
      (6863, ⟨64, (AddGraph.w2923 s.p s.q)⟩),
      (6865, ⟨64, (AddGraph.w2925 s.p s.q)⟩),
      (6874, ⟨64, (AddGraph.w2926 s.p s.q)⟩),
      (6883, ⟨64, (AddGraph.w2928 s.p s.q)⟩),
      (6885, ⟨64, (AddGraph.w2930 s.p s.q)⟩),
      (6886, Value.ofBool (addSpec (AddGraph.w2929 s.p s.q) (AddGraph.w2927 s.p s.q)).2.CF)]
    loads [((.stack 20), (s.fr.rsp - 376), (AddGraph.w2167 s.p s.q)),
      ((.stack 22), (s.fr.rsp - 360), (AddGraph.w2921 s.p s.q)),
      ((.stack 23), (s.fr.rsp - 352), (AddGraph.w2171 s.p s.q)),
      ((.stack 31), (s.fr.rsp - 288), (AddGraph.w2153 s.p s.q)),
      ((.stack 48), (s.fr.rsp - 152), s.fr.rdi)]
    stores [((.left 2), 2167, (s.fr.rdi + 16), (AddGraph.w2167 s.p s.q)),
      ((.left 3), 2171, (s.fr.rdi + 24), (AddGraph.w2171 s.p s.q)),
      ((.left 4), 2153, (s.fr.rdi + 32), (AddGraph.w2153 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment163 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_163 b_l10a410_164 := by
  replay_segment 163
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6841, ⟨64, (AddGraph.w2832 s.p s.q)⟩),
      (6878, ⟨64, (AddGraph.w1001 s.p s.q)⟩),
      (6916, ⟨64, (AddGraph.w2945 s.p s.q)⟩),
      (6926, ⟨64, (AddGraph.w2949 s.p s.q)⟩)]
    loads [((.stack 3), (s.fr.rsp - 512), (AddGraph.w2836 s.p s.q)),
      ((.stack 4), (s.fr.rsp - 504), (AddGraph.w2834 s.p s.q)),
      ((.stack 12), (s.fr.rsp - 440), (AddGraph.w998 s.p s.q)),
      ((.stack 14), (s.fr.rsp - 424), (AddGraph.w2920 s.p s.q)),
      ((.stack 15), (s.fr.rsp - 416), (AddGraph.w2919 s.p s.q)),
      ((.stack 29), (s.fr.rsp - 304), (AddGraph.w1041 s.p s.q))]
    stores [((.stack 15), 2959, (s.fr.rsp - 416), (AddGraph.w2959 s.p s.q)),
      ((.stack 14), 2960, (s.fr.rsp - 424), (AddGraph.w2960 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment164 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_164 b_l10a410_165 := by
  replay_segment 164
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6869, ⟨64, (AddGraph.w2838 s.p s.q)⟩),
      (6918, ⟨64, (AddGraph.w2946 s.p s.q)⟩),
      (6948, ⟨64, (AddGraph.w2953 s.p s.q)⟩),
      (6968, ⟨64, (AddGraph.w2964 s.p s.q)⟩),
      (6969, ⟨64, (AddGraph.w2963 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w2845 s.p s.q)),
      ((.stack 5), (s.fr.rsp - 496), (AddGraph.w2615 s.p s.q)),
      ((.stack 33), (s.fr.rsp - 272), (AddGraph.w1005 s.p s.q)),
      ((.stack 35), (s.fr.rsp - 256), (AddGraph.w1003 s.p s.q)),
      ((.stack 48), (s.fr.rsp - 152), s.fr.rdi)]
    stores [((.stack 23), 2965, (s.fr.rsp - 352), (AddGraph.w2965 s.p s.q)),
      ((.left 5), 2615, (s.fr.rdi + 40), (AddGraph.w2615 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment165 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_165 b_l10a410_166 := by
  replay_segment 165
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6928, ⟨64, (AddGraph.w2950 s.p s.q)⟩),
      (6944, ⟨64, (AddGraph.w2957 s.p s.q)⟩),
      (6946, ⟨64, (AddGraph.w2958 s.p s.q)⟩),
      (6962, ⟨64, (AddGraph.w2961 s.p s.q)⟩),
      (6964, ⟨64, (AddGraph.w2962 s.p s.q)⟩),
      (7009, ⟨64, (AddGraph.w2977 s.p s.q)⟩),
      (7011, ⟨64, (AddGraph.w2978 s.p s.q)⟩),
      (7012, Value.ofBool (addSpec (AddGraph.w2974 s.p s.q) (AddGraph.w2946 s.p s.q)).2.CF)]
    loads [((.stack 8), (s.fr.rsp - 472), (AddGraph.w2832 s.p s.q)),
      ((.stack 14), (s.fr.rsp - 424), (AddGraph.w2960 s.p s.q)),
      ((.stack 15), (s.fr.rsp - 416), (AddGraph.w2959 s.p s.q)),
      ((.stack 35), (s.fr.rsp - 256), (AddGraph.w1003 s.p s.q))]
    stores []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment166 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_166 b_l10a410_167 := by
  replay_segment 166
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (7018, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (7037, ⟨64, (AddGraph.w2993 s.p s.q)⟩),
      (7056, ⟨64, (AddGraph.w3002 s.p s.q)⟩),
      (7057, ⟨64, (AddGraph.w3001 s.p s.q)⟩)]
    loads [((.stack 0), (s.fr.rsp - 536), (AddGraph.w2845 s.p s.q)),
      ((.stack 1), (s.fr.rsp - 528), (AddGraph.w2838 s.p s.q)),
      ((.stack 3), (s.fr.rsp - 512), (AddGraph.w2836 s.p s.q)),
      ((.stack 4), (s.fr.rsp - 504), (AddGraph.w2834 s.p s.q)),
      ((.stack 12), (s.fr.rsp - 440), (AddGraph.w998 s.p s.q)),
      ((.stack 29), (s.fr.rsp - 304), (AddGraph.w1041 s.p s.q)),
      ((.stack 33), (s.fr.rsp - 272), (AddGraph.w1005 s.p s.q)),
      ((.stack 36), (s.fr.rsp - 248), (AddGraph.w1001 s.p s.q))]
    stores [((.stack 8), 3001, (s.fr.rsp - 472), (AddGraph.w3001 s.p s.q)),
      ((.stack 35), 3002, (s.fr.rsp - 256), (AddGraph.w3002 s.p s.q)),
      ((.stack 4), 3003, (s.fr.rsp - 504), (AddGraph.w3003 s.p s.q)),
      ((.stack 36), 3004, (s.fr.rsp - 248), (AddGraph.w3004 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment167 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_167 b_l10a410_168 := by
  replay_segment 167
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (7044, ⟨64, (AddGraph.w2997 s.p s.q)⟩),
      (7046, ⟨64, (AddGraph.w2998 s.p s.q)⟩),
      (7052, ⟨64, (AddGraph.w3000 s.p s.q)⟩),
      (7073, ⟨64, (AddGraph.w3006 s.p s.q)⟩),
      (7075, ⟨64, (AddGraph.w3005 s.p s.q)⟩),
      (7084, ⟨64, (AddGraph.w3008 s.p s.q)⟩),
      (7093, ⟨64, (AddGraph.w3010 s.p s.q)⟩),
      (7097, ⟨64, (AddGraph.w3012 s.p s.q)⟩),
      (7098, Value.ofBool (addSpec (AddGraph.w3011 s.p s.q) (AddGraph.w3009 s.p s.q)).2.CF)]
    loads [((.stack 4), (s.fr.rsp - 504), (AddGraph.w3003 s.p s.q)),
      ((.stack 6), (s.fr.rsp - 488), (AddGraph.w2620 s.p s.q)),
      ((.stack 8), (s.fr.rsp - 472), (AddGraph.w3001 s.p s.q)),
      ((.stack 10), (s.fr.rsp - 456), (AddGraph.w2627 s.p s.q)),
      ((.stack 35), (s.fr.rsp - 256), (AddGraph.w3002 s.p s.q)),
      ((.stack 36), (s.fr.rsp - 248), (AddGraph.w3004 s.p s.q)),
      ((.stack 48), (s.fr.rsp - 152), s.fr.rdi)]
    stores [((.left 6), 2620, (s.fr.rdi + 48), (AddGraph.w2620 s.p s.q)),
      ((.left 7), 2627, (s.fr.rdi + 56), (AddGraph.w2627 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment168 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_168 b_l10a410_169 := by
  replay_segment 168
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6717, ⟨64, (AddGraph.w2869 s.p s.q)⟩),
      (7050, ⟨64, (AddGraph.w2999 s.p s.q)⟩),
      (7102, ⟨64, (AddGraph.w3016 s.p s.q)⟩),
      (7105, ⟨64, (AddGraph.w3019 s.p s.q)⟩),
      (7109, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (7113, ⟨64, (AddGraph.w82 s.p s.q)⟩),
      (7120, ⟨64, s.fr.rdi⟩),
      (7136, ⟨64, (AddGraph.w3034 s.p s.q)⟩),
      (7141, ⟨64, (AddGraph.w3035 s.p s.q)⟩),
      (7142, Value.ofBool (addSpec (AddGraph.w3031 s.p s.q) (AddGraph.w3000 s.p s.q)).2.CF)]
    loads [((.stack 7), (s.fr.rsp - 480), (AddGraph.w2631 s.p s.q)),
      ((.stack 16), (s.fr.rsp - 408), (AddGraph.w2613 s.p s.q))]
    stores [((.left 8), 2631, (s.fr.rdi + 64), (AddGraph.w2631 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment169 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_169 b_l10a410_170 := by
  replay_segment 169
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (6821, ⟨64, (AddGraph.w2912 s.p s.q)⟩),
      (7077, ⟨64, (AddGraph.w3007 s.p s.q)⟩),
      (7109, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (7120, ⟨64, s.fr.rdi⟩),
      (7168, ⟨64, (AddGraph.w3046 s.p s.q)⟩),
      (7177, ⟨64, (AddGraph.w3052 s.p s.q)⟩),
      (7182, ⟨64, (AddGraph.w3056 s.p s.q)⟩),
      (7184, ⟨64, (AddGraph.w2613 s.p s.q)⟩)]
    loads [((.stack 2), (s.fr.rsp - 520), (AddGraph.w2852 s.p s.q)),
      ((.stack 9), (s.fr.rsp - 464), (AddGraph.w2740 s.p s.q)),
      ((.stack 11), (s.fr.rsp - 448), (AddGraph.w2856 s.p s.q)),
      ((.stack 18), (s.fr.rsp - 392), (AddGraph.w2782 s.p s.q)),
      ((.stack 23), (s.fr.rsp - 352), (AddGraph.w2965 s.p s.q)),
      ((.stack 24), (s.fr.rsp - 344), (AddGraph.w2818 s.p s.q)),
      ((.stack 26), (s.fr.rsp - 328), (AddGraph.w2839 s.p s.q))]
    stores [((.left 9), 2613, (s.fr.rdi + 72), (AddGraph.w2613 s.p s.q))]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2200000 in
theorem segment170 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_170 b_l10a410_171 := by
  replay_segment 170
    regs [(65, ⟨64, (s.fr.rsp - 536)⟩),
      (7109, ⟨64, (AddGraph.w80 s.p s.q)⟩),
      (7149, ⟨64, s.fr.rdi⟩),
      (7189, ⟨64, (AddGraph.w3058 s.p s.q)⟩),
      (7205, ⟨64, (AddGraph.w3069 s.p s.q)⟩),
      (7207, ⟨64, (AddGraph.w3071 s.p s.q)⟩),
      (7211, ⟨64, (AddGraph.w3073 s.p s.q)⟩),
      (7219, ⟨64, (AddGraph.w3076 s.p s.q)⟩),
      (7223, ⟨64, (AddGraph.w3078 s.p s.q)⟩)]
    loads []
    stores [((.left 10), 3090, (s.fr.rdi + 80), (AddGraph.w3090 s.p s.q)),
      ((.left 11), 3091, (s.fr.rdi + 88), (AddGraph.w3091 s.p s.q)),
      ((.left 12), 3092, (s.fr.rdi + 96), (AddGraph.w3092 s.p s.q)),
      ((.left 13), 3093, (s.fr.rdi + 104), (AddGraph.w3093 s.p s.q)),
      ((.left 14), 3088, (s.fr.rdi + 112), (AddGraph.w3088 s.p s.q))]

theorem segmentsD3 {code : CodeMap} (inc : ∀ a ∈ fnCode, a ∈ code) (s : Inputs) (r : Ready s) :
    Segment code s b_l10a410_157 b_l10a410_171 := by
  refine BodySegment.trans (@segment157 code inc s r) ?_
  refine BodySegment.trans (@segment158 code inc s r) ?_
  refine BodySegment.trans (@segment159 code inc s r) ?_
  refine BodySegment.trans (@segment160 code inc s r) ?_
  refine BodySegment.trans (@segment161 code inc s r) ?_
  refine BodySegment.trans (@segment162 code inc s r) ?_
  refine BodySegment.trans (@segment163 code inc s r) ?_
  refine BodySegment.trans (@segment164 code inc s r) ?_
  refine BodySegment.trans (@segment165 code inc s r) ?_
  refine BodySegment.trans (@segment166 code inc s r) ?_
  refine BodySegment.trans (@segment167 code inc s r) ?_
  refine BodySegment.trans (@segment168 code inc s r) ?_
  refine BodySegment.trans (@segment169 code inc s r) ?_
  exact @segment170 code inc s r

end K256.Proofs.Generate.Generator.Multiply.AddReplay
