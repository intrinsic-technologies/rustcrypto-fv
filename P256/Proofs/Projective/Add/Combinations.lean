import P256.Proofs.Projective.Add.Values
import P256.Proofs.Projective.Add.Combinations.BZZStep
import P256.Proofs.Projective.Add.Combinations.XZMinusBZZStep
import P256.Proofs.Projective.Add.Combinations.DoubleXZMinusBZZStep
import P256.Proofs.Projective.Add.Combinations.BZZ3Step
import P256.Proofs.Projective.Add.Combinations.YYMinusStep
import P256.Proofs.Projective.Add.Combinations.YYPlusStep
import P256.Proofs.Projective.Add.Combinations.DoubleZZStep
import P256.Proofs.Projective.Add.Combinations.ZZ3Step
import P256.Proofs.Projective.Add.Combinations.BXZStep
import P256.Proofs.Projective.Add.Combinations.ZZ3PlusXXStep
import P256.Proofs.Projective.Add.Combinations.BXZMinusStep
import P256.Proofs.Projective.Add.Combinations.DoubleBXZMinusStep
import P256.Proofs.Projective.Add.Combinations.BXZ3Step
import P256.Proofs.Projective.Add.Combinations.DoubleXXStep
import P256.Proofs.Projective.Add.Combinations.XX3Step
import P256.Proofs.Projective.Add.Combinations.XXMinusStep

set_option autoImplicit false


namespace P256.Proofs.Projective.Add

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Combinations

theorem combinations_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {left right : Projective}
    (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (state : FrameState s t 96 920 632) (rip : t.RIP = 0x10573e)
    (input : CrossTermsAt s t left right) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧
      u.RIP = 0x105af0 ∧ CombinationsAt s u left right := by
  obtain ⟨fuel1, t1, run1, frame1, rip1, value1, registers1, keep1⟩ :=
    BZZ_step pre state rip input.zz
  have rbx1 := (registers1.1).trans input.rbx
  have rbp1 := (registers1.2.1).trans input.rbp
  have r121 := registers1.2.2.1
  have r141 := registers1.2.2.2.2.1
  have value1_336 := keep1 336 _ (by decide) (by decide) (by decide) input.xz
  have value1_368 := keep1 368 _ (by decide) (by decide) (by decide) input.yz
  have value1_400 := keep1 400 _ (by decide) (by decide) (by decide) input.xy
  have value1_464 := keep1 464 _ (by decide) (by decide) (by decide) input.yy
  have value1_528 := keep1 528 _ (by decide) (by decide) (by decide) input.zz
  have value1_560 := keep1 560 _ (by decide) (by decide) (by decide) input.xx
  obtain ⟨fuel2, t2, run2, frame2, rip2, value2, registers2, keep2⟩ :=
    XZMinusBZZ_step pre frame1 rip1 r141 value1_336 value1
  have rbx2 := (registers2.1).trans rbx1
  have rbp2 := (registers2.2.1).trans rbp1
  have r122 := (registers2.2.2.1).trans r121
  have r152 := registers2.2.2.2.2.2
  have value2_336 := keep2 336 _ (by decide) (by decide) (by decide) value1_336
  have value2_368 := keep2 368 _ (by decide) (by decide) (by decide) value1_368
  have value2_400 := keep2 400 _ (by decide) (by decide) (by decide) value1_400
  have value2_464 := keep2 464 _ (by decide) (by decide) (by decide) value1_464
  have value2_528 := keep2 528 _ (by decide) (by decide) (by decide) value1_528
  have value2_560 := keep2 560 _ (by decide) (by decide) (by decide) value1_560
  obtain ⟨fuel3, t3, run3, frame3, rip3, value3, registers3, keep3⟩ :=
    DoubleXZMinusBZZ_step pre frame2 rip2 r152 value2
  have rbx3 := (registers3.1).trans rbx2
  have rbp3 := (registers3.2.1).trans rbp2
  have r123 := (registers3.2.2.1).trans r122
  have r143 := registers3.2.2.2.2.1
  have value3_240 := keep3 240 _ (by decide) (by decide) (by decide) value2
  have value3_336 := keep3 336 _ (by decide) (by decide) (by decide) value2_336
  have value3_368 := keep3 368 _ (by decide) (by decide) (by decide) value2_368
  have value3_400 := keep3 400 _ (by decide) (by decide) (by decide) value2_400
  have value3_464 := keep3 464 _ (by decide) (by decide) (by decide) value2_464
  have value3_528 := keep3 528 _ (by decide) (by decide) (by decide) value2_528
  have value3_560 := keep3 560 _ (by decide) (by decide) (by decide) value2_560
  obtain ⟨fuel4, t4, run4, frame4, rip4, value4, registers4, keep4⟩ :=
    BZZ3_step pre frame3 rip3 r143 value3 value3_240
  have rbx4 := (registers4.1).trans rbx3
  have rbp4 := (registers4.2.1).trans rbp3
  have r124 := (registers4.2.2.1).trans r123
  have r134 := registers4.2.2.2.1
  have value4_336 := keep4 336 _ (by decide) (by decide) (by decide) value3_336
  have value4_368 := keep4 368 _ (by decide) (by decide) (by decide) value3_368
  have value4_400 := keep4 400 _ (by decide) (by decide) (by decide) value3_400
  have value4_464 := keep4 464 _ (by decide) (by decide) (by decide) value3_464
  have value4_528 := keep4 528 _ (by decide) (by decide) (by decide) value3_528
  have value4_560 := keep4 560 _ (by decide) (by decide) (by decide) value3_560
  obtain ⟨fuel5, t5, run5, frame5, rip5, value5, registers5, keep5⟩ :=
    YYMinus_step pre frame4 rip4 value4_464 value4
  have rbx5 := (registers5.1).trans rbx4
  have rbp5 := (registers5.2.1).trans rbp4
  have r125 := (registers5.2.2.1).trans r124
  have r135 := (registers5.2.2.2.1).trans r134
  have value5_208 := keep5 208 _ (by decide) (by decide) (by decide) value4
  have value5_336 := keep5 336 _ (by decide) (by decide) (by decide) value4_336
  have value5_368 := keep5 368 _ (by decide) (by decide) (by decide) value4_368
  have value5_400 := keep5 400 _ (by decide) (by decide) (by decide) value4_400
  have value5_464 := keep5 464 _ (by decide) (by decide) (by decide) value4_464
  have value5_528 := keep5 528 _ (by decide) (by decide) (by decide) value4_528
  have value5_560 := keep5 560 _ (by decide) (by decide) (by decide) value4_560
  obtain ⟨fuel6, t6, run6, frame6, rip6, value6, registers6, keep6⟩ :=
    YYPlus_step pre frame5 rip5 r135 value5_464 value5_208
  have rbx6 := (registers6.1).trans rbx5
  have rbp6 := (registers6.2.1).trans rbp5
  have r126 := (registers6.2.2.1).trans r125
  have value6_304 := keep6 304 _ (by decide) (by decide) (by decide) value5
  have value6_336 := keep6 336 _ (by decide) (by decide) (by decide) value5_336
  have value6_368 := keep6 368 _ (by decide) (by decide) (by decide) value5_368
  have value6_400 := keep6 400 _ (by decide) (by decide) (by decide) value5_400
  have value6_528 := keep6 528 _ (by decide) (by decide) (by decide) value5_528
  have value6_560 := keep6 560 _ (by decide) (by decide) (by decide) value5_560
  obtain ⟨fuel7, t7, run7, frame7, rip7, value7, registers7, keep7⟩ :=
    DoubleZZ_step pre frame6 rip6 rbp6 value6_528
  have rbx7 := (registers7.1).trans rbx6
  have r127 := (registers7.2.2.1).trans r126
  have r137 := registers7.2.2.2.1
  have value7_272 := keep7 272 _ (by decide) (by decide) (by decide) value6
  have value7_304 := keep7 304 _ (by decide) (by decide) (by decide) value6_304
  have value7_336 := keep7 336 _ (by decide) (by decide) (by decide) value6_336
  have value7_368 := keep7 368 _ (by decide) (by decide) (by decide) value6_368
  have value7_400 := keep7 400 _ (by decide) (by decide) (by decide) value6_400
  have value7_528 := keep7 528 _ (by decide) (by decide) (by decide) value6_528
  have value7_560 := keep7 560 _ (by decide) (by decide) (by decide) value6_560
  obtain ⟨fuel8, t8, run8, frame8, rip8, value8, registers8, keep8⟩ :=
    ZZ3_step pre frame7 rip7 r137 value7 value7_528
  have rbx8 := (registers8.1).trans rbx7
  have rbp8 := registers8.2.1
  have r128 := (registers8.2.2.1).trans r127
  have value8_272 := keep8 272 _ (by decide) (by decide) (by decide) value7_272
  have value8_304 := keep8 304 _ (by decide) (by decide) (by decide) value7_304
  have value8_336 := keep8 336 _ (by decide) (by decide) (by decide) value7_336
  have value8_368 := keep8 368 _ (by decide) (by decide) (by decide) value7_368
  have value8_400 := keep8 400 _ (by decide) (by decide) (by decide) value7_400
  have value8_560 := keep8 560 _ (by decide) (by decide) (by decide) value7_560
  obtain ⟨fuel9, t9, run9, frame9, rip9, value9, registers9, keep9⟩ :=
    BXZ_step pre frame8 rip8 r128 value8_336
  have rbx9 := (registers9.1).trans rbx8
  have rbp9 := (registers9.2.1).trans rbp8
  have r139 := registers9.2.2.2.1
  have value9_176 := keep9 176 _ (by decide) (by decide) (by decide) value8
  have value9_272 := keep9 272 _ (by decide) (by decide) (by decide) value8_272
  have value9_304 := keep9 304 _ (by decide) (by decide) (by decide) value8_304
  have value9_368 := keep9 368 _ (by decide) (by decide) (by decide) value8_368
  have value9_400 := keep9 400 _ (by decide) (by decide) (by decide) value8_400
  have value9_560 := keep9 560 _ (by decide) (by decide) (by decide) value8_560
  obtain ⟨fuel10, t10, run10, frame10, rip10, value10, registers10, keep10⟩ :=
    ZZ3PlusXX_step pre frame9 rip9 value9_176 value9_560
  have rbx10 := (registers10.1).trans rbx9
  have rbp10 := (registers10.2.1).trans rbp9
  have r1210 := registers10.2.2.1
  have r1310 := (registers10.2.2.2.1).trans r139
  have value10_80 := keep10 80 _ (by decide) (by decide) (by decide) value9
  have value10_176 := keep10 176 _ (by decide) (by decide) (by decide) value9_176
  have value10_272 := keep10 272 _ (by decide) (by decide) (by decide) value9_272
  have value10_304 := keep10 304 _ (by decide) (by decide) (by decide) value9_304
  have value10_368 := keep10 368 _ (by decide) (by decide) (by decide) value9_368
  have value10_400 := keep10 400 _ (by decide) (by decide) (by decide) value9_400
  have value10_560 := keep10 560 _ (by decide) (by decide) (by decide) value9_560
  obtain ⟨fuel11, t11, run11, frame11, rip11, value11, registers11, keep11⟩ :=
    BXZMinus_step pre frame10 rip10 r1310 r1210 value10_80 value10
  have rbx11 := (registers11.1).trans rbx10
  have rbp11 := (registers11.2.1).trans rbp10
  have r1411 := registers11.2.2.2.2.1
  have value11_176 := keep11 176 _ (by decide) (by decide) (by decide) value10_176
  have value11_272 := keep11 272 _ (by decide) (by decide) (by decide) value10_272
  have value11_304 := keep11 304 _ (by decide) (by decide) (by decide) value10_304
  have value11_368 := keep11 368 _ (by decide) (by decide) (by decide) value10_368
  have value11_400 := keep11 400 _ (by decide) (by decide) (by decide) value10_400
  have value11_560 := keep11 560 _ (by decide) (by decide) (by decide) value10_560
  obtain ⟨fuel12, t12, run12, frame12, rip12, value12, registers12, keep12⟩ :=
    DoubleBXZMinus_step pre frame11 rip11 r1411 value11
  have rbx12 := (registers12.1).trans rbx11
  have rbp12 := (registers12.2.1).trans rbp11
  have r1312 := registers12.2.2.2.1
  have value12_144 := keep12 144 _ (by decide) (by decide) (by decide) value11
  have value12_176 := keep12 176 _ (by decide) (by decide) (by decide) value11_176
  have value12_272 := keep12 272 _ (by decide) (by decide) (by decide) value11_272
  have value12_304 := keep12 304 _ (by decide) (by decide) (by decide) value11_304
  have value12_368 := keep12 368 _ (by decide) (by decide) (by decide) value11_368
  have value12_400 := keep12 400 _ (by decide) (by decide) (by decide) value11_400
  have value12_560 := keep12 560 _ (by decide) (by decide) (by decide) value11_560
  obtain ⟨fuel13, t13, run13, frame13, rip13, value13, registers13, keep13⟩ :=
    BXZ3_step pre frame12 rip12 r1312 value12 value12_144
  have rbx13 := (registers13.1).trans rbx12
  have rbp13 := (registers13.2.1).trans rbp12
  have r1213 := registers13.2.2.1
  have value13_176 := keep13 176 _ (by decide) (by decide) (by decide) value12_176
  have value13_272 := keep13 272 _ (by decide) (by decide) (by decide) value12_272
  have value13_304 := keep13 304 _ (by decide) (by decide) (by decide) value12_304
  have value13_368 := keep13 368 _ (by decide) (by decide) (by decide) value12_368
  have value13_400 := keep13 400 _ (by decide) (by decide) (by decide) value12_400
  have value13_560 := keep13 560 _ (by decide) (by decide) (by decide) value12_560
  obtain ⟨fuel14, t14, run14, frame14, rip14, value14, registers14, keep14⟩ :=
    DoubleXX_step pre frame13 rip13 value13_560
  have rbx14 := (registers14.1).trans rbx13
  have rbp14 := (registers14.2.1).trans rbp13
  have r1214 := (registers14.2.2.1).trans r1213
  have r1414 := registers14.2.2.2.2.1
  have value14_112 := keep14 112 _ (by decide) (by decide) (by decide) value13
  have value14_176 := keep14 176 _ (by decide) (by decide) (by decide) value13_176
  have value14_272 := keep14 272 _ (by decide) (by decide) (by decide) value13_272
  have value14_304 := keep14 304 _ (by decide) (by decide) (by decide) value13_304
  have value14_368 := keep14 368 _ (by decide) (by decide) (by decide) value13_368
  have value14_400 := keep14 400 _ (by decide) (by decide) (by decide) value13_400
  have value14_560 := keep14 560 _ (by decide) (by decide) (by decide) value13_560
  obtain ⟨fuel15, t15, run15, frame15, rip15, value15, registers15, keep15⟩ :=
    XX3_step pre frame14 rip14 r1414 value14 value14_560
  have rbx15 := (registers15.1).trans rbx14
  have rbp15 := (registers15.2.1).trans rbp14
  have r1215 := (registers15.2.2.1).trans r1214
  have r1515 := registers15.2.2.2.2.2
  have value15_112 := keep15 112 _ (by decide) (by decide) (by decide) value14_112
  have value15_176 := keep15 176 _ (by decide) (by decide) (by decide) value14_176
  have value15_272 := keep15 272 _ (by decide) (by decide) (by decide) value14_272
  have value15_304 := keep15 304 _ (by decide) (by decide) (by decide) value14_304
  have value15_368 := keep15 368 _ (by decide) (by decide) (by decide) value14_368
  have value15_400 := keep15 400 _ (by decide) (by decide) (by decide) value14_400
  obtain ⟨fuel16, t16, run16, frame16, rip16, value16, registers16, keep16⟩ :=
    XXMinus_step pre frame15 rip15 r1515 rbp15 value15 value15_176
  have rbx16 := (registers16.1).trans rbx15
  have rbp16 := (registers16.2.1).trans rbp15
  have r1216 := (registers16.2.2.1).trans r1215
  have r1316 := registers16.2.2.2.1
  have value16_112 := keep16 112 _ (by decide) (by decide) (by decide) value15_112
  have value16_272 := keep16 272 _ (by decide) (by decide) (by decide) value15_272
  have value16_304 := keep16 304 _ (by decide) (by decide) (by decide) value15_304
  have value16_368 := keep16 368 _ (by decide) (by decide) (by decide) value15_368
  have value16_400 := keep16 400 _ (by decide) (by decide) (by decide) value15_400
  refine ⟨_, t16, (((((((((((((((run1).trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16, frame16, rip16, ?_⟩
  exact ⟨rbx16, r1216, r1316, rbp16, value16_400, value16_368, value16_304, value16_272, value16_112, value16⟩

end P256.Proofs.Projective.Add
