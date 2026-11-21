import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1184ac_1 [Bindings] (code : CodeMap) :
    Rest (n := 98) code lifted (codeRange 0x1129cc bytes_l1184ac) [(0, 91), (1, 1), (2, 92), (3, 82), (4, 4), (5, 94), (6, 85), (7, 7), (10, 96), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]
      19 0x112a20 bytes_l1184ac_1 b_l1184ac_1 := by
  have f20 : InstrSpec 0x112a20 [0x4D, 0x01, 0xFD] (fun s => s.RIP = 0x112a20) (addR64R64Effect 0x112a20 13 15)
      [.gpr 13, .gpr 15] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112a20 13 15).toInstrSpec (add_r64_r64_effect_step 0x112a20 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x112a23 [0x49, 0x11, 0xCE] (fun s => s.RIP = 0x112a23) (atFlags StatusFlags.CF (adcR64R64Effect 0x112a23 14 1))
      [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112a23 14 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112a23 0x49 0xce c (by decide) (by decide))) pre_rip
  have f22 : InstrSpec 0x112a26 [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x08] (LoadPre 0x112a26 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112a26 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x112a26 6 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x112a26 6 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x112a26 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x112a2c [0x4D, 0x11, 0xE0] (fun s => s.RIP = 0x112a2c) (atFlags StatusFlags.CF (adcR64R64Effect 0x112a2c 8 12))
      [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112a2c 8 12).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112a2c 0x4d 0xe0 c (by decide) (by decide))) pre_rip
  have f24 : InstrSpec 0x112a2f [0x0F, 0x92, 0xC1] (fun s => s.RIP = 0x112a2f) (atFlags (condHolds 2) (setccR8Effect 0x112a2f 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x112a2f 3 1 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x112a2f 2 0xc1 (by decide) (by decide) c)) pre_rip
  have f25 : InstrSpec 0x112a32 [0x4C, 0x01, 0xED] (fun s => s.RIP = 0x112a32) (addR64R64Effect 0x112a32 5 13)
      [.gpr 5, .gpr 13] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112a32 5 13).toInstrSpec (add_r64_r64_effect_step 0x112a32 0x4c 0xed (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x112a35 [0x49, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x112a35) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a35 10 0x0))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112a35 10 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112a35 0x49 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f27 : InstrSpec 0x112a39 [0x48, 0x01, 0xF5] (fun s => s.RIP = 0x112a39) (addR64R64Effect 0x112a39 5 6)
      [.gpr 5, .gpr 6] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112a39 5 6).toInstrSpec (add_r64_r64_effect_step 0x112a39 0x48 0xf5 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x112a3c [0x49, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x112a3c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a3c 10 0x0))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112a3c 10 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112a3c 0x49 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f29 : InstrSpec 0x112a40 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x112a40) (movR64R64Effect 0x112a40 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112a40 0 12).toInstrSpec (mov_r64_r64_effect_step 0x112a40 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x112a43 [0xBA, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x112a43) (movR32Imm32Effect 0x112a43 5 2 0xffffffff)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x112a43 5 2 0xffffffff).toInstrSpec (mov_r32_imm32_effect_step 0x112a43 0xba (by decide) 0xffffffff) pre_rip
  have f31 : InstrSpec 0x112a48 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x112a48) (mulR64Effect 0x112a48 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112a48 2).toInstrSpec (mul_r64_effect_step 0x112a48 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x112a4b [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x112a4b) (movR64R64Effect 0x112a4b 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x112a4b 11 2).toInstrSpec (mov_r64_r64_effect_step 0x112a4b 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x112a4e [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x112a4e) (movR64R64Effect 0x112a4e 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x112a4e 15 0).toInstrSpec (mov_r64_r64_effect_step 0x112a4e 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x112a51 [0x4D, 0x01, 0xF7] (fun s => s.RIP = 0x112a51) (addR64R64Effect 0x112a51 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112a51 15 14).toInstrSpec (add_r64_r64_effect_step 0x112a51 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x112a54 [0x49, 0x83, 0xD3, 0x00] (fun s => s.RIP = 0x112a54) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a54 11 0x0))
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112a54 11 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112a54 0x49 0xd3 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f36 : InstrSpec 0x112a58 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x112a58 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x112a58 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112a58 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x112a58 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x112a58 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x112a5d [0x4C, 0x8B, 0x48, 0x18] (LoadPre 0x112a5d (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x112a5d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112a5d 9 (.base 0 (.d8 0x18)))
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x112a5d 9 (.base 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x112a5d 0x4c (by decide) 1 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f38 : InstrSpec 0x112a61 [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x112a61) (movR64R64Effect 0x112a61 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112a61 0 9).toInstrSpec (mov_r64_r64_effect_step 0x112a61 0x4c 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f20 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 99) f20 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 100) (ρ' := [(0, 91), (1, 1), (2, 92), (3, 82), (4, 4), (5, 94), (6, 85), (7, 7), (10, 96), (11, 62), (12, 12), (13, 98), (14, 14), (15, 15), (16, 99), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a23) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f21 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 102) f21 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x112a23 14 1 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 103) (ρ' := [(0, 91), (1, 1), (2, 92), (3, 82), (4, 4), (5, 94), (6, 85), (7, 7), (10, 96), (11, 62), (12, 12), (13, 98), (14, 101), (15, 15), (16, 102), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a26) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f22 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 91), (1, 1), (2, 92), (3, 82), (4, 4), (5, 94), (6, 85), (7, 7), (8, 104), (10, 96), (11, 62), (12, 12), (13, 98), (14, 101), (15, 15), (16, 102), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a2c) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f23 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 107) f23 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x112a2c 8 12 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 108) (ρ' := [(0, 91), (1, 1), (2, 92), (3, 82), (4, 4), (5, 94), (6, 85), (7, 7), (8, 106), (10, 96), (11, 62), (12, 12), (13, 98), (14, 101), (15, 15), (16, 107), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a2f) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 91), (1, 109), (2, 92), (3, 82), (4, 4), (5, 94), (6, 85), (7, 7), (8, 106), (10, 96), (11, 62), (12, 12), (13, 98), (14, 101), (15, 15), (16, 107), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a32) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f25 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 112) f25 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 113) (ρ' := [(0, 91), (1, 109), (2, 92), (3, 82), (4, 4), (5, 111), (6, 85), (7, 7), (8, 106), (10, 96), (11, 62), (12, 12), (13, 98), (14, 101), (15, 15), (16, 112), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a35) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f26 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 91), (1, 109), (2, 92), (3, 82), (4, 4), (5, 111), (6, 85), (7, 7), (8, 106), (10, 114), (11, 62), (12, 12), (13, 98), (14, 101), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a39) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f27 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 117) f27 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 118) (ρ' := [(0, 91), (1, 109), (2, 92), (3, 82), (4, 4), (5, 116), (6, 85), (7, 7), (8, 106), (10, 114), (11, 62), (12, 12), (13, 98), (14, 101), (15, 15), (16, 117), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a3c) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f28 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 91), (1, 109), (2, 92), (3, 82), (4, 4), (5, 116), (6, 85), (7, 7), (8, 106), (10, 119), (11, 62), (12, 12), (13, 98), (14, 101), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a40) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 121), (1, 109), (2, 92), (3, 82), (4, 4), (5, 116), (6, 85), (7, 7), (8, 106), (10, 119), (11, 62), (12, 12), (13, 98), (14, 101), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a43) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f30 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 121), (1, 109), (2, 123), (3, 82), (4, 4), (5, 116), (6, 85), (7, 7), (8, 106), (10, 119), (11, 62), (12, 12), (13, 98), (14, 101), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a48) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 126) f31 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 127) (ρ' := [(0, 125), (1, 109), (2, 126), (3, 82), (4, 4), (5, 116), (6, 85), (7, 7), (8, 106), (10, 119), (11, 62), (12, 12), (13, 98), (14, 101), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a4b) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f32 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 125), (1, 109), (2, 126), (3, 82), (4, 4), (5, 116), (6, 85), (7, 7), (8, 106), (10, 119), (11, 128), (12, 12), (13, 98), (14, 101), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a4e) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f33 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 125), (1, 109), (2, 126), (3, 82), (4, 4), (5, 116), (6, 85), (7, 7), (8, 106), (10, 119), (11, 128), (12, 12), (13, 98), (14, 101), (15, 130), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a51) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f34 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 133) f34 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 134) (ρ' := [(0, 125), (1, 109), (2, 126), (3, 82), (4, 4), (5, 116), (6, 85), (7, 7), (8, 106), (10, 119), (11, 128), (12, 12), (13, 98), (14, 101), (15, 132), (16, 133), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a54) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f35 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 125), (1, 109), (2, 126), (3, 82), (4, 4), (5, 116), (6, 85), (7, 7), (8, 106), (10, 119), (11, 135), (12, 12), (13, 98), (14, 101), (15, 132), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a58) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f36 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 137), (1, 109), (2, 126), (3, 82), (4, 4), (5, 116), (6, 85), (7, 7), (8, 106), (10, 119), (11, 135), (12, 12), (13, 98), (14, 101), (15, 132), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a5d) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f37 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 137), (1, 109), (2, 126), (3, 82), (4, 4), (5, 116), (6, 85), (7, 7), (8, 106), (9, 139), (10, 119), (11, 135), (12, 12), (13, 98), (14, 101), (15, 132), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a61) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f38 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 141), (1, 109), (2, 126), (3, 82), (4, 4), (5, 116), (6, 85), (7, 7), (8, 106), (9, 139), (10, 119), (11, 135), (12, 12), (13, 98), (14, 101), (15, 132), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a64) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 143) (by decide) rfl

theorem rest_l1184ac [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1129cc bytes_l1184ac) (entryMap (live .l1184ac))
      39 0x1129cc bytes_l1184ac b_l1184ac := by
  have f0 : InstrSpec 0x1129cc [0x48, 0xBA, 0xFE, 0x9B, 0xDF, 0xEE, 0x85, 0xFD, 0x2F, 0x01] (fun s => s.RIP = 0x1129cc) (movR64Imm64Effect 0x1129cc 2 0x12ffd85eedf9bfe)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x1129cc 2 0x12ffd85eedf9bfe).toInstrSpec (mov_r64_imm64_effect_step 0x1129cc 0x48 0xba (by decide) (by decide) 0x12ffd85eedf9bfe) pre_rip
  have f1 : InstrSpec 0x1129d6 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x1129d6) (mulR64Effect 0x1129d6 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1129d6 2).toInstrSpec (mul_r64_effect_step 0x1129d6 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1129d9 [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x1129d9) (movR64R64Effect 0x1129d9 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1129d9 9 0).toInstrSpec (mov_r64_r64_effect_step 0x1129d9 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1129dc [0x48, 0x89, 0xD5] (fun s => s.RIP = 0x1129dc) (movR64R64Effect 0x1129dc 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1129dc 5 2).toInstrSpec (mov_r64_r64_effect_step 0x1129dc 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1129df [0x49, 0x83, 0xE3, 0xFE] (fun s => s.RIP = 0x1129df) (andR64Imm8Effect 0x1129df 11 0xfe)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x1129df 11 0xfe).toInstrSpec (and_r64_imm8_effect_step 0x1129df 0x49 0xe3 0xfe (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1129e3 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x1129e3) (movR64R64Effect 0x1129e3 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1129e3 0 12).toInstrSpec (mov_r64_r64_effect_step 0x1129e3 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1129e6 [0x48, 0xBA, 0x21, 0x6C, 0x1A, 0xDF, 0x52, 0x05, 0x19, 0x43] (fun s => s.RIP = 0x1129e6) (movR64Imm64Effect 0x1129e6 2 0x43190552df1a6c21)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x1129e6 2 0x43190552df1a6c21).toInstrSpec (mov_r64_imm64_effect_step 0x1129e6 0x48 0xba (by decide) (by decide) 0x43190552df1a6c21) pre_rip
  have f7 : InstrSpec 0x1129f0 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x1129f0) (mulR64Effect 0x1129f0 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1129f0 2).toInstrSpec (mul_r64_effect_step 0x1129f0 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1129f3 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x1129f3) (movR64R64Effect 0x1129f3 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1129f3 6 2).toInstrSpec (mov_r64_r64_effect_step 0x1129f3 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1129f6 [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x1129f6) (movR64R64Effect 0x1129f6 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1129f6 3 0).toInstrSpec (mov_r64_r64_effect_step 0x1129f6 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1129f9 [0x4C, 0x01, 0xD3] (fun s => s.RIP = 0x1129f9) (addR64R64Effect 0x1129f9 3 10)
      [.gpr 3, .gpr 10] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1129f9 3 10).toInstrSpec (add_r64_r64_effect_step 0x1129f9 0x4c 0xd3 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1129fc [0x48, 0x83, 0xD6, 0x00] (fun s => s.RIP = 0x1129fc) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1129fc 6 0x0))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x1129fc 6 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x1129fc 0x48 0xd6 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f12 : InstrSpec 0x112a00 [0x4D, 0x01, 0xD9] (fun s => s.RIP = 0x112a00) (addR64R64Effect 0x112a00 9 11)
      [.gpr 9, .gpr 11] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112a00 9 11).toInstrSpec (add_r64_r64_effect_step 0x112a00 0x4d 0xd9 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x112a03 [0x48, 0x11, 0xEB] (fun s => s.RIP = 0x112a03) (atFlags StatusFlags.CF (adcR64R64Effect 0x112a03 3 5))
      [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112a03 3 5).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112a03 0x48 0xeb c (by decide) (by decide))) pre_rip
  have f14 : InstrSpec 0x112a06 [0x48, 0x83, 0xD6, 0x00] (fun s => s.RIP = 0x112a06) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a06 6 0x0))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112a06 6 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112a06 0x48 0xd6 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f15 : InstrSpec 0x112a0a [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x112a0a) (movR64R64Effect 0x112a0a 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112a0a 0 12).toInstrSpec (mov_r64_r64_effect_step 0x112a0a 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x112a0d [0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x112a0d) (movR64Imm64Effect 0x112a0d 2 0xfffffffeffffffff)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x112a0d 2 0xfffffffeffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x112a0d 0x48 0xba (by decide) (by decide) 0xfffffffeffffffff) pre_rip
  have f17 : InstrSpec 0x112a17 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x112a17) (mulR64Effect 0x112a17 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112a17 2).toInstrSpec (mul_r64_effect_step 0x112a17 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x112a1a [0x48, 0x89, 0xC5] (fun s => s.RIP = 0x112a1a) (movR64R64Effect 0x112a1a 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x112a1a 5 0).toInstrSpec (mov_r64_r64_effect_step 0x112a1a 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x112a1d [0x49, 0x89, 0xD2] (fun s => s.RIP = 0x112a1d) (movR64R64Effect 0x112a1d 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x112a1d 10 2).toInstrSpec (mov_r64_r64_effect_step 0x112a1d 0x49 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129d6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (2, 56), (4, 4), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129d9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 1), (2, 56), (4, 4), (7, 7), (9, 58), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129dc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 1), (2, 56), (4, 4), (5, 60), (7, 7), (9, 58), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129df) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 1), (2, 56), (4, 4), (5, 60), (7, 7), (9, 58), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129e3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 1), (2, 56), (4, 4), (5, 60), (7, 7), (9, 58), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129e6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 1), (2, 66), (4, 4), (5, 60), (7, 7), (9, 58), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129f0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 1), (2, 69), (4, 4), (5, 60), (7, 7), (9, 58), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129f3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 68), (1, 1), (2, 69), (4, 4), (5, 60), (6, 71), (7, 7), (9, 58), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129f6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 68), (1, 1), (2, 69), (3, 73), (4, 4), (5, 60), (6, 71), (7, 7), (9, 58), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129f9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 77) (ρ' := [(0, 68), (1, 1), (2, 69), (3, 75), (4, 4), (5, 60), (6, 71), (7, 7), (9, 58), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (16, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129fc) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 68), (1, 1), (2, 69), (3, 75), (4, 4), (5, 60), (6, 78), (7, 7), (9, 58), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a00) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f12 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 68), (1, 1), (2, 69), (3, 75), (4, 4), (5, 60), (6, 78), (7, 7), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (16, 80), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a03) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 83) f13 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x112a03 3 5 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 68), (1, 1), (2, 69), (3, 82), (4, 4), (5, 60), (6, 78), (7, 7), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (16, 83), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a06) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 68), (1, 1), (2, 69), (3, 82), (4, 4), (5, 60), (6, 85), (7, 7), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a0a) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 1), (2, 69), (3, 82), (4, 4), (5, 60), (6, 85), (7, 7), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a0d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 87), (1, 1), (2, 89), (3, 82), (4, 4), (5, 60), (6, 85), (7, 7), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a17) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 92) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 93) (ρ' := [(0, 91), (1, 1), (2, 92), (3, 82), (4, 4), (5, 60), (6, 85), (7, 7), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a1a) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f18 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 91), (1, 1), (2, 92), (3, 82), (4, 4), (5, 94), (6, 85), (7, 7), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a1d) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 91), (1, 1), (2, 92), (3, 82), (4, 4), (5, 94), (6, 85), (7, 7), (10, 96), (11, 62), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112a20) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1184ac_1 code

theorem block_l1184ac [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1184ac :=
  Rest.liftedBlock (rest_l1184ac code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1184ac x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
