import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11839b_1 [Bindings] (code : CodeMap) :
    Rest (n := 96) code lifted (codeRange 0x1128bb bytes_l11839b) [(0, 77), (1, 55), (2, 78), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 71), (13, 94), (14, 91), (22, 22), (39, 39), (51, 51)]
      18 0x112900 bytes_l11839b_1 b_l11839b_1 := by
  have f20 : InstrSpec 0x112900 [0x48, 0x89, 0x4C, 0x24, 0x30] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112900 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x112900 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112900 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112900 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112900 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f21 : InstrSpec 0x112905 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x112905) (movR64R64Effect 0x112905 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112905 0 1).toInstrSpec (mov_r64_r64_effect_step 0x112905 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x112908 [0x48, 0xF7, 0xE5] (fun s => s.RIP = 0x112908) (mulR64Effect 0x112908 5)
      [.gpr 5, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112908 5).toInstrSpec (mul_r64_effect_step 0x112908 0x48 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x11290b [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x11290b) (movR64R64Effect 0x11290b 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x11290b 12 2).toInstrSpec (mov_r64_r64_effect_step 0x11290b 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x11290e [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x11290e) (movR64R64Effect 0x11290e 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x11290e 15 0).toInstrSpec (mov_r64_r64_effect_step 0x11290e 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x112911 [0x49, 0x01, 0xF7] (fun s => s.RIP = 0x112911) (addR64R64Effect 0x112911 15 6)
      [.gpr 15, .gpr 6] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112911 15 6).toInstrSpec (add_r64_r64_effect_step 0x112911 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x112914 [0x49, 0x83, 0xD4, 0x00] (fun s => s.RIP = 0x112914) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112914 12 0x0))
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112914 12 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112914 0x49 0xd4 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f27 : InstrSpec 0x112918 [0x4D, 0x01, 0xEF] (fun s => s.RIP = 0x112918) (addR64R64Effect 0x112918 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112918 15 13).toInstrSpec (add_r64_r64_effect_step 0x112918 0x4d 0xef (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x11291b [0x49, 0x83, 0xD4, 0x00] (fun s => s.RIP = 0x11291b) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11291b 12 0x0))
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x11291b 12 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x11291b 0x49 0xd4 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f29 : InstrSpec 0x11291f [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x11291f) (movR64R64Effect 0x11291f 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11291f 0 1).toInstrSpec (mov_r64_r64_effect_step 0x11291f 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x112922 [0xB9, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x112922) (movR32Imm32Effect 0x112922 5 1 0xffffffff)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x112922 5 1 0xffffffff).toInstrSpec (mov_r32_imm32_effect_step 0x112922 0xb9 (by decide) 0xffffffff) pre_rip
  have f31 : InstrSpec 0x112927 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x112927) (mulR64Effect 0x112927 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112927 1).toInstrSpec (mul_r64_effect_step 0x112927 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x11292a [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x11292a) (movR64R64Effect 0x11292a 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x11292a 3 2).toInstrSpec (mov_r64_r64_effect_step 0x11292a 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x11292d [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x11292d) (movR64R64Effect 0x11292d 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x11292d 10 0).toInstrSpec (mov_r64_r64_effect_step 0x11292d 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x112930 [0x4D, 0x01, 0xDA] (fun s => s.RIP = 0x112930) (addR64R64Effect 0x112930 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112930 10 11).toInstrSpec (add_r64_r64_effect_step 0x112930 0x4d 0xda (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x112933 [0x48, 0x83, 0xD3, 0x00] (fun s => s.RIP = 0x112933) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112933 3 0x0))
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112933 3 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112933 0x48 0xd3 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f36 : InstrSpec 0x112937 [0x4D, 0x8B, 0x68, 0x08] (LoadPre 0x112937 (fun s => AddrMode.addr (.base 8 (.d8 0x8)) s (0x112937 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112937 13 (.base 8 (.d8 0x8)))
      [.gpr 8] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x112937 13 (.base 8 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x112937 0x4d (by decide) 5 (.base 8 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x11293b [0x4C, 0x89, 0x44, 0x24, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11293b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11293b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11293b 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11293b 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x11293b 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 77), (1, 55), (2, 78), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 71), (13, 94), (14, 91), (22, 22), (39, 39), (51, 51)]) (p' := 0x112905) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 97), (1, 55), (2, 78), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 71), (13, 94), (14, 91), (22, 22), (39, 39), (51, 51)]) (p' := 0x112908) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 100) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 101) (ρ' := [(0, 99), (1, 55), (2, 100), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 71), (13, 94), (14, 91), (22, 22), (39, 39), (51, 51)]) (p' := 0x11290b) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f23 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 99), (1, 55), (2, 100), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 102), (13, 94), (14, 91), (22, 22), (39, 39), (51, 51)]) (p' := 0x11290e) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f24 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 99), (1, 55), (2, 100), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 102), (13, 94), (14, 91), (15, 104), (22, 22), (39, 39), (51, 51)]) (p' := 0x112911) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f25 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 107) f25 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 108) (ρ' := [(0, 99), (1, 55), (2, 100), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 102), (13, 94), (14, 91), (15, 106), (16, 107), (22, 22), (39, 39), (51, 51)]) (p' := 0x112914) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f26 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 99), (1, 55), (2, 100), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 109), (13, 94), (14, 91), (15, 106), (22, 22), (39, 39), (51, 51)]) (p' := 0x112918) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f27 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 112) f27 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 113) (ρ' := [(0, 99), (1, 55), (2, 100), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 109), (13, 94), (14, 91), (15, 111), (16, 112), (22, 22), (39, 39), (51, 51)]) (p' := 0x11291b) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f28 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 99), (1, 55), (2, 100), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 114), (13, 94), (14, 91), (15, 111), (22, 22), (39, 39), (51, 51)]) (p' := 0x11291f) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 116), (1, 55), (2, 100), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 114), (13, 94), (14, 91), (15, 111), (22, 22), (39, 39), (51, 51)]) (p' := 0x112922) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 116), (1, 118), (2, 100), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 114), (13, 94), (14, 91), (15, 111), (22, 22), (39, 39), (51, 51)]) (p' := 0x112927) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 121) f31 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 122) (ρ' := [(0, 120), (1, 118), (2, 121), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 114), (13, 94), (14, 91), (15, 111), (22, 22), (39, 39), (51, 51)]) (p' := 0x11292a) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f32 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 120), (1, 118), (2, 121), (3, 123), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 114), (13, 94), (14, 91), (15, 111), (22, 22), (39, 39), (51, 51)]) (p' := 0x11292d) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f33 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 120), (1, 118), (2, 121), (3, 123), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 125), (11, 11), (12, 114), (13, 94), (14, 91), (15, 111), (22, 22), (39, 39), (51, 51)]) (p' := 0x112930) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f34 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 128) f34 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 129) (ρ' := [(0, 120), (1, 118), (2, 121), (3, 123), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 127), (11, 11), (12, 114), (13, 94), (14, 91), (15, 111), (16, 128), (22, 22), (39, 39), (51, 51)]) (p' := 0x112933) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f35 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 120), (1, 118), (2, 121), (3, 130), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 127), (11, 11), (12, 114), (13, 94), (14, 91), (15, 111), (22, 22), (39, 39), (51, 51)]) (p' := 0x112937) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f36 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 120), (1, 118), (2, 121), (3, 130), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 127), (11, 11), (12, 114), (13, 132), (14, 91), (15, 111), (22, 22), (39, 39), (51, 51)]) (p' := 0x11293b) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.exec (n := 134) (ρ' := [(0, 120), (1, 118), (2, 121), (3, 130), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 127), (11, 11), (12, 114), (13, 132), (14, 91), (15, 111), (22, 22), (39, 39), (51, 51)]) (p' := 0x112940) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 135) (by decide) rfl

theorem rest_l11839b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1128bb bytes_l11839b) (entryMap (live .l11839b))
      38 0x1128bb bytes_l11839b b_l11839b := by
  have f0 : InstrSpec 0x1128bb [0x4D, 0x89, 0xE0] (fun s => s.RIP = 0x1128bb) (movR64R64Effect 0x1128bb 8 12)
      [.gpr 12] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1128bb 8 12).toInstrSpec (mov_r64_r64_effect_step 0x1128bb 0x4d 0xe0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1128be [0x49, 0x8B, 0x0C, 0x24] (LoadPre 0x1128be (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x1128be + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1128be 1 (.sib 12 none 0 .none))
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1128be 1 (.sib 12 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1128be 0x49 (by decide) 1 (.sib 12 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1128c2 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x1128c2) (movR64R64Effect 0x1128c2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1128c2 0 1).toInstrSpec (mov_r64_r64_effect_step 0x1128c2 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1128c5 [0x48, 0x83, 0xD0, 0x00] (fun s => s.RIP = 0x1128c5) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1128c5 0 0x0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x1128c5 0 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x1128c5 0x48 0xd0 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f4 : InstrSpec 0x1128c9 [0x48, 0x89, 0x44, 0x24, 0x18] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1128c9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1128c9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1128c9 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1128c9 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1128c9 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1128ce [0x0F, 0x92, 0x44, 0x24, 0x08] (StorePre 0x1128ce 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1128ce + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 2) (setccM8Effect 0x1128ce 5 (.sib 4 none 0 (.d8 0x8))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.rip] :=
    (setccM8Effect_footprint 0x1128ce 5 (.sib 4 none 0 (.d8 0x8)) 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x1128ce 2 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1128d3 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x1128d3) (movR64R64Effect 0x1128d3 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1128d3 0 1).toInstrSpec (mov_r64_r64_effect_step 0x1128d3 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1128d6 [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x1128d6) (mulR64Effect 0x1128d6 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1128d6 9).toInstrSpec (mul_r64_effect_step 0x1128d6 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1128d9 [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x1128d9) (movR64R64Effect 0x1128d9 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1128d9 15 0).toInstrSpec (mov_r64_r64_effect_step 0x1128d9 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1128dc [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x1128dc) (movR64R64Effect 0x1128dc 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1128dc 12 2).toInstrSpec (mov_r64_r64_effect_step 0x1128dc 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1128df [0x49, 0x83, 0xE2, 0xFE] (fun s => s.RIP = 0x1128df) (andR64Imm8Effect 0x1128df 10 0xfe)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x1128df 10 0xfe).toInstrSpec (and_r64_imm8_effect_step 0x1128df 0x49 0xe2 0xfe (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1128e3 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x1128e3) (movR64R64Effect 0x1128e3 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1128e3 0 1).toInstrSpec (mov_r64_r64_effect_step 0x1128e3 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1128e6 [0x49, 0xF7, 0xE5] (fun s => s.RIP = 0x1128e6) (mulR64Effect 0x1128e6 13)
      [.gpr 13, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1128e6 13).toInstrSpec (mul_r64_effect_step 0x1128e6 0x49 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1128e9 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x1128e9) (movR64R64Effect 0x1128e9 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1128e9 13 2).toInstrSpec (mov_r64_r64_effect_step 0x1128e9 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1128ec [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x1128ec) (movR64R64Effect 0x1128ec 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1128ec 14 0).toInstrSpec (mov_r64_r64_effect_step 0x1128ec 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1128ef [0x49, 0x01, 0xDE] (fun s => s.RIP = 0x1128ef) (addR64R64Effect 0x1128ef 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1128ef 14 3).toInstrSpec (add_r64_r64_effect_step 0x1128ef 0x49 0xde (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1128f2 [0x49, 0x83, 0xD5, 0x00] (fun s => s.RIP = 0x1128f2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1128f2 13 0x0))
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 13, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x1128f2 13 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x1128f2 0x49 0xd5 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f17 : InstrSpec 0x1128f6 [0x4D, 0x01, 0xD7] (fun s => s.RIP = 0x1128f6) (addR64R64Effect 0x1128f6 15 10)
      [.gpr 15, .gpr 10] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1128f6 15 10).toInstrSpec (add_r64_r64_effect_step 0x1128f6 0x4d 0xd7 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1128f9 [0x4D, 0x11, 0xE6] (fun s => s.RIP = 0x1128f9) (atFlags StatusFlags.CF (adcR64R64Effect 0x1128f9 14 12))
      [.gpr 14, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1128f9 14 12).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1128f9 0x4d 0xe6 c (by decide) (by decide))) pre_rip
  have f19 : InstrSpec 0x1128fc [0x49, 0x83, 0xD5, 0x00] (fun s => s.RIP = 0x1128fc) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1128fc 13 0x0))
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 13, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x1128fc 13 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x1128fc 0x49 0xd5 0x0 c (by decide) (by decide) (by decide))) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (16, 16), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128be) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (16, 16), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128c2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (16, 16), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128c5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 60) f3 .CF (fun _ => rfl) (adcR64Imm8Effect_fresh 0x1128c5 0 0x0 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (16, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128c9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (16, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128ce) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (16, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128d3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (16, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128d6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 55), (2, 67), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128d9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 66), (1, 55), (2, 67), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128dc) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 66), (1, 55), (2, 67), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 71), (13, 13), (15, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128df) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 66), (1, 55), (2, 67), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 71), (13, 13), (15, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128e3) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 55), (2, 67), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 71), (13, 13), (15, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128e6) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 78) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 79) (ρ' := [(0, 77), (1, 55), (2, 78), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 71), (13, 13), (15, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128e9) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f13 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 77), (1, 55), (2, 78), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 71), (13, 80), (15, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128ec) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f14 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 77), (1, 55), (2, 78), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 71), (13, 80), (14, 82), (15, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128ef) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f15 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 85) f15 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 86) (ρ' := [(0, 77), (1, 55), (2, 78), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 71), (13, 80), (14, 84), (15, 69), (16, 85), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128f2) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f16 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 77), (1, 55), (2, 78), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 71), (13, 87), (14, 84), (15, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128f6) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f17 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 77), (1, 55), (2, 78), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 71), (13, 87), (14, 84), (16, 89), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128f9) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f18 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 92) f18 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x1128f9 14 12 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 93) (ρ' := [(0, 77), (1, 55), (2, 78), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 71), (13, 87), (14, 91), (16, 92), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128fc) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f19 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 77), (1, 55), (2, 78), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 73), (11, 11), (12, 71), (13, 94), (14, 91), (22, 22), (39, 39), (51, 51)]) (p' := 0x112900) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11839b_1 code

theorem block_l11839b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11839b :=
  Rest.liftedBlock (rest_l11839b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11839b x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
