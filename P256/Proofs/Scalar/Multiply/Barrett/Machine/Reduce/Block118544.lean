import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l118544_1 [Bindings] (code : CodeMap) :
    Rest (n := 98) code lifted (codeRange 0x112a64 bytes_l118544) [(0, 91), (1, 1), (2, 92), (3, 94), (4, 4), (5, 5), (6, 85), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 96), (13, 60), (14, 82), (15, 15), (22, 22), (39, 39), (51, 51)]
      17 0x112ab8 bytes_l118544_1 b_l118544_1 := by
  have f20 : InstrSpec 0x112ab8 [0x4D, 0x01, 0xD7] (fun s => s.RIP = 0x112ab8) (addR64R64Effect 0x112ab8 15 10)
      [.gpr 15, .gpr 10] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112ab8 15 10).toInstrSpec (add_r64_r64_effect_step 0x112ab8 0x4d 0xd7 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x112abb [0x0F, 0xB6, 0xC9] (fun s => s.RIP = 0x112abb) (movzxR32R8Effect 0x112abb 3 1 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x112abb 3 1 1).toInstrSpec (movzx_r32_r8_effect_step 0x112abb 0xc9 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x112abe [0x4D, 0x11, 0xC3] (fun s => s.RIP = 0x112abe) (atFlags StatusFlags.CF (adcR64R64Effect 0x112abe 11 8))
      [.gpr 11, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112abe 11 8).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112abe 0x4d 0xc3 c (by decide) (by decide))) pre_rip
  have f23 : InstrSpec 0x112ac1 [0x4C, 0x11, 0xC9] (fun s => s.RIP = 0x112ac1) (atFlags StatusFlags.CF (adcR64R64Effect 0x112ac1 1 9))
      [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112ac1 1 9).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112ac1 0x4c 0xc9 c (by decide) (by decide))) pre_rip
  have f24 : InstrSpec 0x112ac4 [0x41, 0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x112ac4) (atFlags (condHolds 2) (setccR8Effect 0x112ac4 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x112ac4 4 8 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x112ac4 2 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  have f25 : InstrSpec 0x112ac8 [0x4C, 0x01, 0xFB] (fun s => s.RIP = 0x112ac8) (addR64R64Effect 0x112ac8 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112ac8 3 15).toInstrSpec (add_r64_r64_effect_step 0x112ac8 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x112acb [0x49, 0x83, 0xD4, 0x00] (fun s => s.RIP = 0x112acb) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112acb 12 0x0))
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112acb 12 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112acb 0x49 0xd4 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f27 : InstrSpec 0x112acf [0x48, 0x01, 0xF3] (fun s => s.RIP = 0x112acf) (addR64R64Effect 0x112acf 3 6)
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112acf 3 6).toInstrSpec (add_r64_r64_effect_step 0x112acf 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x112ad2 [0x49, 0x83, 0xD4, 0x00] (fun s => s.RIP = 0x112ad2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112ad2 12 0x0))
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112ad2 12 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112ad2 0x49 0xd4 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f29 : InstrSpec 0x112ad6 [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x112ad6) (movR64R64Effect 0x112ad6 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112ad6 0 9).toInstrSpec (mov_r64_r64_effect_step 0x112ad6 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x112ad9 [0xBA, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x112ad9) (movR32Imm32Effect 0x112ad9 5 2 0xffffffff)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x112ad9 5 2 0xffffffff).toInstrSpec (mov_r32_imm32_effect_step 0x112ad9 0xba (by decide) 0xffffffff) pre_rip
  have f31 : InstrSpec 0x112ade [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x112ade) (mulR64Effect 0x112ade 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112ade 2).toInstrSpec (mul_r64_effect_step 0x112ade 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x112ae1 [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x112ae1) (movR64R64Effect 0x112ae1 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x112ae1 15 0).toInstrSpec (mov_r64_r64_effect_step 0x112ae1 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x112ae4 [0x4D, 0x01, 0xDF] (fun s => s.RIP = 0x112ae4) (addR64R64Effect 0x112ae4 15 11)
      [.gpr 15, .gpr 11] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112ae4 15 11).toInstrSpec (add_r64_r64_effect_step 0x112ae4 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x112ae7 [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x112ae7) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112ae7 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112ae7 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112ae7 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f35 : InstrSpec 0x112aeb [0x4D, 0x01, 0xE7] (fun s => s.RIP = 0x112aeb) (addR64R64Effect 0x112aeb 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112aeb 15 12).toInstrSpec (add_r64_r64_effect_step 0x112aeb 0x4d 0xe7 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x112aee [0x41, 0x0F, 0xB6, 0xF0] (fun s => s.RIP = 0x112aee) (movzxR32R8Effect 0x112aee 4 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movzxR32R8Effect_footprint 0x112aee 4 6 8).toInstrSpec (movzx_r32_r8_rex_effect_step 0x112aee 0x41 (by decide) 0xf0 (by decide)) pre_rip
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f20 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 99) f20 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 100) (ρ' := [(0, 91), (1, 1), (2, 92), (3, 94), (4, 4), (5, 5), (6, 85), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 96), (13, 60), (14, 82), (15, 98), (16, 99), (22, 22), (39, 39), (51, 51)]) (p' := 0x112abb) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 91), (1, 101), (2, 92), (3, 94), (4, 4), (5, 5), (6, 85), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 96), (13, 60), (14, 82), (15, 98), (16, 99), (22, 22), (39, 39), (51, 51)]) (p' := 0x112abe) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f22 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 104) f22 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x112abe 11 8 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 105) (ρ' := [(0, 91), (1, 101), (2, 92), (3, 94), (4, 4), (5, 5), (6, 85), (7, 7), (8, 8), (9, 9), (10, 10), (11, 103), (12, 96), (13, 60), (14, 82), (15, 98), (16, 104), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ac1) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 107) f23 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x112ac1 1 9 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 108) (ρ' := [(0, 91), (1, 106), (2, 92), (3, 94), (4, 4), (5, 5), (6, 85), (7, 7), (8, 8), (9, 9), (10, 10), (11, 103), (12, 96), (13, 60), (14, 82), (15, 98), (16, 107), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ac4) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f24 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 91), (1, 106), (2, 92), (3, 94), (4, 4), (5, 5), (6, 85), (7, 7), (8, 109), (9, 9), (10, 10), (11, 103), (12, 96), (13, 60), (14, 82), (15, 98), (16, 107), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ac8) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f25 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 112) f25 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 113) (ρ' := [(0, 91), (1, 106), (2, 92), (3, 111), (4, 4), (5, 5), (6, 85), (7, 7), (8, 109), (9, 9), (10, 10), (11, 103), (12, 96), (13, 60), (14, 82), (15, 98), (16, 112), (22, 22), (39, 39), (51, 51)]) (p' := 0x112acb) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f26 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 91), (1, 106), (2, 92), (3, 111), (4, 4), (5, 5), (6, 85), (7, 7), (8, 109), (9, 9), (10, 10), (11, 103), (12, 114), (13, 60), (14, 82), (15, 98), (22, 22), (39, 39), (51, 51)]) (p' := 0x112acf) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f27 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 117) f27 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 118) (ρ' := [(0, 91), (1, 106), (2, 92), (3, 116), (4, 4), (5, 5), (6, 85), (7, 7), (8, 109), (9, 9), (10, 10), (11, 103), (12, 114), (13, 60), (14, 82), (15, 98), (16, 117), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ad2) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f28 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 91), (1, 106), (2, 92), (3, 116), (4, 4), (5, 5), (6, 85), (7, 7), (8, 109), (9, 9), (10, 10), (11, 103), (12, 119), (13, 60), (14, 82), (15, 98), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ad6) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 121), (1, 106), (2, 92), (3, 116), (4, 4), (5, 5), (6, 85), (7, 7), (8, 109), (9, 9), (10, 10), (11, 103), (12, 119), (13, 60), (14, 82), (15, 98), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ad9) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f30 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 121), (1, 106), (2, 123), (3, 116), (4, 4), (5, 5), (6, 85), (7, 7), (8, 109), (9, 9), (10, 10), (11, 103), (12, 119), (13, 60), (14, 82), (15, 98), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ade) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 126) f31 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 127) (ρ' := [(0, 125), (1, 106), (2, 126), (3, 116), (4, 4), (5, 5), (6, 85), (7, 7), (8, 109), (9, 9), (10, 10), (11, 103), (12, 119), (13, 60), (14, 82), (15, 98), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ae1) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f32 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 125), (1, 106), (2, 126), (3, 116), (4, 4), (5, 5), (6, 85), (7, 7), (8, 109), (9, 9), (10, 10), (11, 103), (12, 119), (13, 60), (14, 82), (15, 128), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ae4) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f33 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 131) f33 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 132) (ρ' := [(0, 125), (1, 106), (2, 126), (3, 116), (4, 4), (5, 5), (6, 85), (7, 7), (8, 109), (9, 9), (10, 10), (11, 103), (12, 119), (13, 60), (14, 82), (15, 130), (16, 131), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ae7) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f34 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 125), (1, 106), (2, 133), (3, 116), (4, 4), (5, 5), (6, 85), (7, 7), (8, 109), (9, 9), (10, 10), (11, 103), (12, 119), (13, 60), (14, 82), (15, 130), (22, 22), (39, 39), (51, 51)]) (p' := 0x112aeb) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f35 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 136) f35 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 137) (ρ' := [(0, 125), (1, 106), (2, 133), (3, 116), (4, 4), (5, 5), (6, 85), (7, 7), (8, 109), (9, 9), (10, 10), (11, 103), (12, 119), (13, 60), (14, 82), (15, 135), (16, 136), (22, 22), (39, 39), (51, 51)]) (p' := 0x112aee) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f36 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 125), (1, 106), (2, 133), (3, 116), (4, 4), (5, 5), (6, 138), (7, 7), (8, 109), (9, 9), (10, 10), (11, 103), (12, 119), (13, 60), (14, 82), (15, 135), (16, 136), (22, 22), (39, 39), (51, 51)]) (p' := 0x112af2) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 140) (by decide) rfl

theorem rest_l118544 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112a64 bytes_l118544) (entryMap (live .l118544))
      37 0x112a64 bytes_l118544 b_l118544 := by
  have f0 : InstrSpec 0x112a64 [0x48, 0xBA, 0xFE, 0x9B, 0xDF, 0xEE, 0x85, 0xFD, 0x2F, 0x01] (fun s => s.RIP = 0x112a64) (movR64Imm64Effect 0x112a64 2 0x12ffd85eedf9bfe)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x112a64 2 0x12ffd85eedf9bfe).toInstrSpec (mov_r64_imm64_effect_step 0x112a64 0x48 0xba (by decide) (by decide) 0x12ffd85eedf9bfe) pre_rip
  have f1 : InstrSpec 0x112a6e [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x112a6e) (mulR64Effect 0x112a6e 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112a6e 2).toInstrSpec (mul_r64_effect_step 0x112a6e 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112a71 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x112a71) (movR64R64Effect 0x112a71 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x112a71 12 0).toInstrSpec (mov_r64_r64_effect_step 0x112a71 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x112a74 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x112a74) (movR64R64Effect 0x112a74 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x112a74 13 2).toInstrSpec (mov_r64_r64_effect_step 0x112a74 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x112a77 [0x48, 0x83, 0xE3, 0xFE] (fun s => s.RIP = 0x112a77) (andR64Imm8Effect 0x112a77 3 0xfe)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x112a77 3 0xfe).toInstrSpec (and_r64_imm8_effect_step 0x112a77 0x48 0xe3 0xfe (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112a7b [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x112a7b) (movR64R64Effect 0x112a7b 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112a7b 0 9).toInstrSpec (mov_r64_r64_effect_step 0x112a7b 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112a7e [0x48, 0xBA, 0x21, 0x6C, 0x1A, 0xDF, 0x52, 0x05, 0x19, 0x43] (fun s => s.RIP = 0x112a7e) (movR64Imm64Effect 0x112a7e 2 0x43190552df1a6c21)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x112a7e 2 0x43190552df1a6c21).toInstrSpec (mov_r64_imm64_effect_step 0x112a7e 0x48 0xba (by decide) (by decide) 0x43190552df1a6c21) pre_rip
  have f7 : InstrSpec 0x112a88 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x112a88) (mulR64Effect 0x112a88 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112a88 2).toInstrSpec (mul_r64_effect_step 0x112a88 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x112a8b [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x112a8b) (movR64R64Effect 0x112a8b 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x112a8b 6 2).toInstrSpec (mov_r64_r64_effect_step 0x112a8b 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112a8e [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x112a8e) (movR64R64Effect 0x112a8e 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x112a8e 14 0).toInstrSpec (mov_r64_r64_effect_step 0x112a8e 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x112a91 [0x49, 0x01, 0xEE] (fun s => s.RIP = 0x112a91) (addR64R64Effect 0x112a91 14 5)
      [.gpr 14, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112a91 14 5).toInstrSpec (add_r64_r64_effect_step 0x112a91 0x49 0xee (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x112a94 [0x48, 0x83, 0xD6, 0x00] (fun s => s.RIP = 0x112a94) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a94 6 0x0))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112a94 6 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112a94 0x48 0xd6 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f12 : InstrSpec 0x112a98 [0x49, 0x01, 0xDC] (fun s => s.RIP = 0x112a98) (addR64R64Effect 0x112a98 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112a98 12 3).toInstrSpec (add_r64_r64_effect_step 0x112a98 0x49 0xdc (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x112a9b [0x4D, 0x11, 0xEE] (fun s => s.RIP = 0x112a9b) (atFlags StatusFlags.CF (adcR64R64Effect 0x112a9b 14 13))
      [.gpr 14, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112a9b 14 13).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112a9b 0x4d 0xee c (by decide) (by decide))) pre_rip
  have f14 : InstrSpec 0x112a9e [0x48, 0x83, 0xD6, 0x00] (fun s => s.RIP = 0x112a9e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a9e 6 0x0))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112a9e 6 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112a9e 0x48 0xd6 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f15 : InstrSpec 0x112aa2 [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x112aa2) (movR64R64Effect 0x112aa2 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112aa2 0 9).toInstrSpec (mov_r64_r64_effect_step 0x112aa2 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x112aa5 [0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x112aa5) (movR64Imm64Effect 0x112aa5 2 0xfffffffeffffffff)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x112aa5 2 0xfffffffeffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x112aa5 0x48 0xba (by decide) (by decide) 0xfffffffeffffffff) pre_rip
  have f17 : InstrSpec 0x112aaf [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x112aaf) (mulR64Effect 0x112aaf 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112aaf 2).toInstrSpec (mul_r64_effect_step 0x112aaf 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x112ab2 [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x112ab2) (movR64R64Effect 0x112ab2 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x112ab2 3 0).toInstrSpec (mov_r64_r64_effect_step 0x112ab2 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x112ab5 [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x112ab5) (movR64R64Effect 0x112ab5 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x112ab5 12 2).toInstrSpec (mov_r64_r64_effect_step 0x112ab5 0x49 0xd4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a6e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (2, 56), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a71) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 1), (2, 56), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a74) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 1), (2, 56), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 60), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a77) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 1), (2, 56), (3, 62), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 60), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a7b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 1), (2, 56), (3, 62), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 60), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a7e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 1), (2, 66), (3, 62), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 60), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a88) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 1), (2, 69), (3, 62), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 60), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a8b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 68), (1, 1), (2, 69), (3, 62), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 60), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a8e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 68), (1, 1), (2, 69), (3, 62), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 60), (14, 73), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a91) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 77) (ρ' := [(0, 68), (1, 1), (2, 69), (3, 62), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 60), (14, 75), (15, 15), (16, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a94) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 68), (1, 1), (2, 69), (3, 62), (4, 4), (5, 5), (6, 78), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 60), (14, 75), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a98) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f12 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 68), (1, 1), (2, 69), (3, 62), (4, 4), (5, 5), (6, 78), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 60), (14, 75), (15, 15), (16, 80), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a9b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f13 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 83) f13 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x112a9b 14 13 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 68), (1, 1), (2, 69), (3, 62), (4, 4), (5, 5), (6, 78), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 60), (14, 82), (15, 15), (16, 83), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a9e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 68), (1, 1), (2, 69), (3, 62), (4, 4), (5, 5), (6, 85), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 60), (14, 82), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112aa2) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 1), (2, 69), (3, 62), (4, 4), (5, 5), (6, 85), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 60), (14, 82), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112aa5) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 87), (1, 1), (2, 89), (3, 62), (4, 4), (5, 5), (6, 85), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 60), (14, 82), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112aaf) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 92) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 93) (ρ' := [(0, 91), (1, 1), (2, 92), (3, 62), (4, 4), (5, 5), (6, 85), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 60), (14, 82), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ab2) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f18 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 91), (1, 1), (2, 92), (3, 94), (4, 4), (5, 5), (6, 85), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 60), (14, 82), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ab5) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f19 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 91), (1, 1), (2, 92), (3, 94), (4, 4), (5, 5), (6, 85), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 96), (13, 60), (14, 82), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ab8) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l118544_1 code

theorem block_l118544 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l118544 :=
  Rest.liftedBlock (rest_l118544 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l118544 x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
