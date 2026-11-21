import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.Segment

namespace K256.Proofs.Sec1.Affine.Uncompressed

open X86.UserProcess K256.Proofs.Sec1.LIR

set_option maxRecDepth 4096 in
theorem arithmeticPrefix0 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6 b_l11f8f6_1 inputs0 inputs1 arithmeticStep0 := by
  arithmetic_segment cover inputs0 8 [arithmeticStep0First, arithmeticStep0Last, arithmeticStep0]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix1 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_1 b_l11f8f6_2 inputs1 inputs2 arithmeticStep1 := by
  arithmetic_segment cover inputs1 8 [arithmeticStep1]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix2 {code : CodeMap} (_cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_2 b_l11f8f6_3 inputs2 inputs3 arithmeticStep2 := by
  arithmetic_segment _cover inputs2 12 [arithmeticStep2]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix3 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_3 b_l11f8f6_4 inputs3 inputs4 arithmeticStep3 := by
  arithmetic_segment cover inputs3 10 [arithmeticStep3]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix4 {code : CodeMap} (_cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_4 b_l11f8f6_5 inputs4 inputs5 arithmeticStep4 := by
  arithmetic_segment _cover inputs4 15 [arithmeticStep4]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix5 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_5 b_l11f8f6_6 inputs5 inputs6 arithmeticStep5 := by
  arithmetic_segment cover inputs5 11 [arithmeticStep5]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix6 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_6 b_l11f8f6_7 inputs6 inputs7 arithmeticStep6 := by
  arithmetic_segment cover inputs6 13 [arithmeticStep6]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix7 {code : CodeMap} (_cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_7 b_l11f8f6_8 inputs7 inputs8 arithmeticStep7 := by
  arithmetic_segment _cover inputs7 11 [arithmeticStep7]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix8 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_8 b_l11f8f6_9 inputs8 inputs9 arithmeticStep8 := by
  arithmetic_segment cover inputs8 11 [arithmeticStep8]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix9 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_9 b_l11f8f6_10 inputs9 inputs10 arithmeticStep9 := by
  arithmetic_segment cover inputs9 5 [arithmeticStep9First, arithmeticStep9Last, arithmeticStep9]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix10 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_10 b_l11f8f6_11 inputs10 inputs11 arithmeticStep10 := by
  arithmetic_segment cover inputs10 10 [arithmeticStep10]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix11 {code : CodeMap} (_cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_11 b_l11f8f6_12 inputs11 inputs12 arithmeticStep11 := by
  arithmetic_segment _cover inputs11 12 [arithmeticStep11]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix12 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_12 b_l11f8f6_13 inputs12 inputs13 arithmeticStep12 := by
  arithmetic_segment cover inputs12 11 [arithmeticStep12]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix13 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_13 b_l11f8f6_14 inputs13 inputs14 arithmeticStep13 := by
  arithmetic_segment cover inputs13 15 [arithmeticStep13]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix14 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_14 b_l11f8f6_15 inputs14 inputs15 arithmeticStep14 := by
  arithmetic_segment cover inputs14 9 [arithmeticStep14]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix15 {code : CodeMap} (_cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_15 b_l11f8f6_16 inputs15 inputs16 arithmeticStep15 := by
  arithmetic_segment _cover inputs15 11 [arithmeticStep15]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix16 {code : CodeMap} (_cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_16 b_l11f8f6_17 inputs16 inputs17 arithmeticStep16 := by
  arithmetic_segment _cover inputs16 13 [arithmeticStep16]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix17 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_17 b_l11f8f6_18 inputs17 inputs18 arithmeticStep17 := by
  arithmetic_segment cover inputs17 10 [arithmeticStep17]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix18 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_18 b_l11f8f6_19 inputs18 inputs19 arithmeticStep18 := by
  arithmetic_segment cover inputs18 10 [arithmeticStep18First, arithmeticStep18Last, arithmeticStep18]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix19 {code : CodeMap} (_cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_19 b_l11f8f6_20 inputs19 inputs20 arithmeticStep19 := by
  arithmetic_segment _cover inputs19 12 [arithmeticStep19]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix20 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_20 b_l11f8f6_21 inputs20 inputs21 arithmeticStep20 := by
  arithmetic_segment cover inputs20 12 [arithmeticStep20]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix21 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_21 b_l11f8f6_22 inputs21 inputs22 arithmeticStep21 := by
  arithmetic_segment cover inputs21 13 [arithmeticStep21]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix22 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_22 b_l11f8f6_23 inputs22 inputs23 arithmeticStep22 := by
  arithmetic_segment cover inputs22 14 [arithmeticStep22]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix23 {code : CodeMap} (_cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_23 b_l11f8f6_24 inputs23 inputs24 arithmeticStep23 := by
  arithmetic_segment _cover inputs23 8 [arithmeticStep23]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix24 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_24 b_l11f8f6_25 inputs24 inputs25 arithmeticStep24 := by
  arithmetic_segment cover inputs24 10 [arithmeticStep24]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix25 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_25 b_l11f8f6_26 inputs25 inputs26 arithmeticStep25 := by
  arithmetic_segment cover inputs25 9 [arithmeticStep25]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix26 {code : CodeMap} (_cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_26 b_l11f8f6_27 inputs26 inputs27 arithmeticStep26 := by
  arithmetic_segment _cover inputs26 13 [arithmeticStep26]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix27 {code : CodeMap} (cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_27 b_l11f8f6_28 inputs27 inputs28 arithmeticStep27 := by
  arithmetic_segment cover inputs27 10 [arithmeticStep27]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix28 {code : CodeMap} (_cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_28 b_l11f8f6_29 inputs28 inputs29 arithmeticStep28 := by
  arithmetic_segment _cover inputs28 14 [arithmeticStep28]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix29 {code : CodeMap} (_cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_29 b_l11f8f6_30 inputs29 inputs30 arithmeticStep29 := by
  arithmetic_segment _cover inputs29 10 [arithmeticStep29First, arithmeticStep29Last, arithmeticStep29]

set_option maxRecDepth 4096 in
theorem arithmeticPrefix30 {code : CodeMap} (_cover : ∀ v ∈ fnCode, v ∈ code) :
    PrefixRuns code b_l11f8f6_30 b_l11f8f6_31 inputs30 inputs31 arithmeticStep30 := by
  arithmetic_segment _cover inputs30 7 [arithmeticStep30]

end K256.Proofs.Sec1.Affine.Uncompressed
