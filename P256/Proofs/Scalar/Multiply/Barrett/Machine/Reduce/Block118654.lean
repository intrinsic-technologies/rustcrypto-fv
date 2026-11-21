import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l118654_2 [Bindings] (code : CodeMap) :
    Rest (n := 150) code lifted (codeRange 0x112b74 bytes_l118654) [(0, 139), (1, 1), (2, 140), (3, 135), (4, 4), (5, 130), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 144), (14, 147), (15, 142), (16, 148), (22, 22), (39, 39), (51, 51)]
      3 0x112c08 bytes_l118654_2 b_l118654_2 := by
  have f40 : InstrSpec 0x112c08 [0x48, 0x11, 0xEB] (fun s => s.RIP = 0x112c08) (atFlags StatusFlags.CF (adcR64R64Effect 0x112c08 3 5))
      [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112c08 3 5).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112c08 0x48 0xeb c (by decide) (by decide))) pre_rip
  have f41 : InstrSpec 0x112c0b [0x48, 0x8B, 0x4C, 0x24, 0x28] (LoadPre 0x112c0b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x112c0b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112c0b 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x112c0b 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x112c0b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f42 : InstrSpec 0x112c10 [0x4C, 0x8B, 0x01] (LoadPre 0x112c10 (fun s => AddrMode.addr (.base 1 .none) s (0x112c10 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x112c10 8 (.base 1 .none))
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x112c10 8 (.base 1 .none)).toInstrSpec (mov_r64_m64_effect_step 0x112c10 0x4c (by decide) 0 (.base 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f40 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 139), (1, 1), (2, 140), (3, 150), (4, 4), (5, 130), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 144), (14, 147), (15, 142), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c0b) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f41 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 139), (1, 152), (2, 140), (3, 150), (4, 4), (5, 130), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 144), (14, 147), (15, 142), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c10) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f42 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 139), (1, 152), (2, 140), (3, 150), (4, 4), (5, 130), (6, 91), (7, 7), (8, 154), (9, 85), (10, 78), (11, 114), (12, 88), (13, 144), (14, 147), (15, 142), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c13) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 156) (by decide) rfl

theorem rest_l118654_1 [Bindings] (code : CodeMap) :
    Rest (n := 102) code lifted (codeRange 0x112b74 bytes_l118654) [(0, 97), (1, 1), (2, 98), (3, 3), (4, 4), (5, 100), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 75), (12, 88), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]
      23 0x112bc3 bytes_l118654_1 b_l118654_1 := by
  have f20 : InstrSpec 0x112bc3 [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x112bc3) (movR64R64Effect 0x112bc3 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x112bc3 14 0).toInstrSpec (mov_r64_r64_effect_step 0x112bc3 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x112bc6 [0x4D, 0x01, 0xDE] (fun s => s.RIP = 0x112bc6) (addR64R64Effect 0x112bc6 14 11)
      [.gpr 14, .gpr 11] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112bc6 14 11).toInstrSpec (add_r64_r64_effect_step 0x112bc6 0x4d 0xde (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x112bc9 [0x48, 0x83, 0xD5, 0x00] (fun s => s.RIP = 0x112bc9) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112bc9 5 0x0))
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112bc9 5 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112bc9 0x48 0xd5 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f23 : InstrSpec 0x112bcd [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x112bcd) (movR64R64Effect 0x112bcd 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112bcd 0 15).toInstrSpec (mov_r64_r64_effect_step 0x112bcd 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x112bd0 [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x112bd0) (mulR64Effect 0x112bd0 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112bd0 8).toInstrSpec (mul_r64_effect_step 0x112bd0 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x112bd3 [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x112bd3) (movR64R64Effect 0x112bd3 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x112bd3 11 2).toInstrSpec (mov_r64_r64_effect_step 0x112bd3 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x112bd6 [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x112bd6) (movR64R64Effect 0x112bd6 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x112bd6 13 0).toInstrSpec (mov_r64_r64_effect_step 0x112bd6 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x112bd9 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x112bd9) (movR64R64Effect 0x112bd9 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112bd9 0 15).toInstrSpec (mov_r64_r64_effect_step 0x112bd9 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x112bdc [0x48, 0xBA, 0x84, 0x9E, 0x17, 0xA7, 0xAD, 0xFA, 0xE6, 0xBC] (fun s => s.RIP = 0x112bdc) (movR64Imm64Effect 0x112bdc 2 0xbce6faada7179e84)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x112bdc 2 0xbce6faada7179e84).toInstrSpec (mov_r64_imm64_effect_step 0x112bdc 0x48 0xba (by decide) (by decide) 0xbce6faada7179e84) pre_rip
  have f29 : InstrSpec 0x112be6 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x112be6) (mulR64Effect 0x112be6 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112be6 2).toInstrSpec (mul_r64_effect_step 0x112be6 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x112be9 [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x112be9) (movR64R64Effect 0x112be9 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x112be9 3 2).toInstrSpec (mov_r64_r64_effect_step 0x112be9 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x112bec [0x49, 0x01, 0xF6] (fun s => s.RIP = 0x112bec) (addR64R64Effect 0x112bec 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112bec 14 6).toInstrSpec (add_r64_r64_effect_step 0x112bec 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x112bef [0x4C, 0x11, 0xD5] (fun s => s.RIP = 0x112bef) (atFlags StatusFlags.CF (adcR64R64Effect 0x112bef 5 10))
      [.gpr 5, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112bef 5 10).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112bef 0x4c 0xd5 c (by decide) (by decide))) pre_rip
  have f33 : InstrSpec 0x112bf2 [0x49, 0x01, 0xC6] (fun s => s.RIP = 0x112bf2) (addR64R64Effect 0x112bf2 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112bf2 14 0).toInstrSpec (add_r64_r64_effect_step 0x112bf2 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x112bf5 [0x48, 0x83, 0xD3, 0x00] (fun s => s.RIP = 0x112bf5) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112bf5 3 0x0))
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112bf5 3 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112bf5 0x48 0xd3 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f35 : InstrSpec 0x112bf9 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x112bf9) (movR64R64Effect 0x112bf9 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112bf9 0 1).toInstrSpec (mov_r64_r64_effect_step 0x112bf9 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x112bfc [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x112bfc) (mulR64Effect 0x112bfc 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112bfc 8).toInstrSpec (mul_r64_effect_step 0x112bfc 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x112bff [0x4D, 0x89, 0xC7] (fun s => s.RIP = 0x112bff) (movR64R64Effect 0x112bff 15 8)
      [.gpr 8] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x112bff 15 8).toInstrSpec (mov_r64_r64_effect_step 0x112bff 0x4d 0xc7 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x112c02 [0x4D, 0x01, 0xE5] (fun s => s.RIP = 0x112c02) (addR64R64Effect 0x112c02 13 12)
      [.gpr 13, .gpr 12] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112c02 13 12).toInstrSpec (add_r64_r64_effect_step 0x112c02 0x4d 0xe5 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x112c05 [0x4D, 0x11, 0xDE] (fun s => s.RIP = 0x112c05) (atFlags StatusFlags.CF (adcR64R64Effect 0x112c05 14 11))
      [.gpr 14, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112c05 14 11).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112c05 0x4d 0xde c (by decide) (by decide))) pre_rip
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f20 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 97), (1, 1), (2, 98), (3, 3), (4, 4), (5, 100), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 75), (12, 88), (13, 58), (14, 102), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bc6) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f21 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 105) f21 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 106) (ρ' := [(0, 97), (1, 1), (2, 98), (3, 3), (4, 4), (5, 100), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 75), (12, 88), (13, 58), (14, 104), (15, 15), (16, 105), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bc9) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f22 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 97), (1, 1), (2, 98), (3, 3), (4, 4), (5, 107), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 75), (12, 88), (13, 58), (14, 104), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bcd) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 109), (1, 1), (2, 98), (3, 3), (4, 4), (5, 107), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 75), (12, 88), (13, 58), (14, 104), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bd0) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 112) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 113) (ρ' := [(0, 111), (1, 1), (2, 112), (3, 3), (4, 4), (5, 107), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 75), (12, 88), (13, 58), (14, 104), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bd3) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f25 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 111), (1, 1), (2, 112), (3, 3), (4, 4), (5, 107), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 58), (14, 104), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bd6) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f26 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 111), (1, 1), (2, 112), (3, 3), (4, 4), (5, 107), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 116), (14, 104), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bd9) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 118), (1, 1), (2, 112), (3, 3), (4, 4), (5, 107), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 116), (14, 104), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bdc) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 118), (1, 1), (2, 120), (3, 3), (4, 4), (5, 107), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 116), (14, 104), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112be6) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 123) f29 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 124) (ρ' := [(0, 122), (1, 1), (2, 123), (3, 3), (4, 4), (5, 107), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 116), (14, 104), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112be9) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f30 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 122), (1, 1), (2, 123), (3, 125), (4, 4), (5, 107), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 116), (14, 104), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bec) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f31 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 128) f31 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 129) (ρ' := [(0, 122), (1, 1), (2, 123), (3, 125), (4, 4), (5, 107), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 116), (14, 127), (15, 15), (16, 128), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bef) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f32 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 122), (1, 1), (2, 123), (3, 125), (4, 4), (5, 130), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 116), (14, 127), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bf2) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f33 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 133) f33 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 134) (ρ' := [(0, 122), (1, 1), (2, 123), (3, 125), (4, 4), (5, 130), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 116), (14, 132), (15, 15), (16, 133), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bf5) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f34 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 122), (1, 1), (2, 123), (3, 135), (4, 4), (5, 130), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 116), (14, 132), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bf9) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f35 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 137), (1, 1), (2, 123), (3, 135), (4, 4), (5, 130), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 116), (14, 132), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bfc) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f36 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 140) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 141) (ρ' := [(0, 139), (1, 1), (2, 140), (3, 135), (4, 4), (5, 130), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 116), (14, 132), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bff) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f37 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 139), (1, 1), (2, 140), (3, 135), (4, 4), (5, 130), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 116), (14, 132), (15, 142), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c02) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f38 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 145) f38 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 146) (ρ' := [(0, 139), (1, 1), (2, 140), (3, 135), (4, 4), (5, 130), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 144), (14, 132), (15, 142), (16, 145), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c05) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f39 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 148) f39 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x112c05 14 11 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 149) (ρ' := [(0, 139), (1, 1), (2, 140), (3, 135), (4, 4), (5, 130), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 114), (12, 88), (13, 144), (14, 147), (15, 142), (16, 148), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c08) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l118654_2 code

theorem rest_l118654 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112b74 bytes_l118654) (entryMap (live .l118654))
      43 0x112b74 bytes_l118654 b_l118654 := by
  have f0 : InstrSpec 0x112b74 [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x112b74) (mulR64Effect 0x112b74 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112b74 8).toInstrSpec (mul_r64_effect_step 0x112b74 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x112b77 [0x48, 0x89, 0xD5] (fun s => s.RIP = 0x112b77) (movR64R64Effect 0x112b77 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x112b77 5 2).toInstrSpec (mov_r64_r64_effect_step 0x112b77 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112b7a [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x112b7a) (movR64R64Effect 0x112b7a 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x112b7a 13 0).toInstrSpec (mov_r64_r64_effect_step 0x112b7a 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x112b7d [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x112b7d) (movR64R64Effect 0x112b7d 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112b7d 0 3).toInstrSpec (mov_r64_r64_effect_step 0x112b7d 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x112b80 [0x48, 0xBA, 0x84, 0x9E, 0x17, 0xA7, 0xAD, 0xFA, 0xE6, 0xBC] (fun s => s.RIP = 0x112b80) (movR64Imm64Effect 0x112b80 2 0xbce6faada7179e84)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x112b80 2 0xbce6faada7179e84).toInstrSpec (mov_r64_imm64_effect_step 0x112b80 0x48 0xba (by decide) (by decide) 0xbce6faada7179e84) pre_rip
  have f5 : InstrSpec 0x112b8a [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x112b8a) (mulR64Effect 0x112b8a 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112b8a 2).toInstrSpec (mul_r64_effect_step 0x112b8a 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112b8d [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x112b8d) (movR64R64Effect 0x112b8d 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x112b8d 6 2).toInstrSpec (mov_r64_r64_effect_step 0x112b8d 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x112b90 [0x4C, 0x03, 0x4C, 0x24, 0x18] (LoadPre 0x112b90 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x112b90 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x112b90 9 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 9, .gpr 4] [] [.reg 9, .flags, .rip] :=
    (addR64M64Effect_footprint 0x112b90 9 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (add_r64_m64_effect_step 0x112b90 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x112b95 [0x4C, 0x13, 0x64, 0x24, 0x10] (LoadPre 0x112b95 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x112b95 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x112b95 12 (.sib 4 none 0 (.d8 0x10))))
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x112b95 12 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x112b95 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x112b9a [0x4C, 0x13, 0x5C, 0x24, 0x20] (LoadPre 0x112b9a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x112b9a + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x112b9a 11 (.sib 4 none 0 (.d8 0x20))))
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x112b9a 11 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x112b9a 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x112b9f [0x4D, 0x11, 0xF2] (fun s => s.RIP = 0x112b9f) (atFlags StatusFlags.CF (adcR64R64Effect 0x112b9f 10 14))
      [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112b9f 10 14).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112b9f 0x4d 0xf2 c (by decide) (by decide))) pre_rip
  have f11 : InstrSpec 0x112ba2 [0x49, 0x01, 0xC4] (fun s => s.RIP = 0x112ba2) (addR64R64Effect 0x112ba2 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112ba2 12 0).toInstrSpec (add_r64_r64_effect_step 0x112ba2 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x112ba5 [0x48, 0x83, 0xD6, 0x00] (fun s => s.RIP = 0x112ba5) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112ba5 6 0x0))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112ba5 6 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112ba5 0x48 0xd6 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f13 : InstrSpec 0x112ba9 [0x4D, 0x01, 0xE9] (fun s => s.RIP = 0x112ba9) (addR64R64Effect 0x112ba9 9 13)
      [.gpr 9, .gpr 13] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112ba9 9 13).toInstrSpec (add_r64_r64_effect_step 0x112ba9 0x4d 0xe9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x112bac [0x49, 0x11, 0xEC] (fun s => s.RIP = 0x112bac) (atFlags StatusFlags.CF (adcR64R64Effect 0x112bac 12 5))
      [.gpr 12, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112bac 12 5).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112bac 0x49 0xec c (by decide) (by decide))) pre_rip
  have f15 : InstrSpec 0x112baf [0x48, 0x83, 0xD6, 0x00] (fun s => s.RIP = 0x112baf) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112baf 6 0x0))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112baf 6 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112baf 0x48 0xd6 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f16 : InstrSpec 0x112bb3 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x112bb3) (movR64R64Effect 0x112bb3 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112bb3 0 3).toInstrSpec (mov_r64_r64_effect_step 0x112bb3 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x112bb6 [0x48, 0xC7, 0xC2, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x112bb6) (movR64Imm32Effect 0x112bb6 2 0xffffffff)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x112bb6 2 0xffffffff).toInstrSpec (mov_r64_imm32_effect_step 0x112bb6 0x48 0xc2 (by decide) (by decide) (by decide) 0xffffffff) pre_rip
  have f18 : InstrSpec 0x112bbd [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x112bbd) (mulR64Effect 0x112bbd 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112bbd 2).toInstrSpec (mul_r64_effect_step 0x112bbd 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x112bc0 [0x48, 0x89, 0xD5] (fun s => s.RIP = 0x112bc0) (movR64R64Effect 0x112bc0 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x112bc0 5 2).toInstrSpec (mov_r64_r64_effect_step 0x112bc0 0x48 0xd5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 54), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b77) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 1), (2, 54), (3, 3), (4, 4), (5, 56), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b7a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 54), (3, 3), (4, 4), (5, 56), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b7d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 54), (3, 3), (4, 4), (5, 56), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b80) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 1), (2, 62), (3, 3), (4, 4), (5, 56), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b8a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 64), (1, 1), (2, 65), (3, 3), (4, 4), (5, 56), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b8d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 1), (2, 65), (3, 3), (4, 4), (5, 56), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b90) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f7 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 64), (1, 1), (2, 65), (3, 3), (4, 4), (5, 56), (6, 67), (7, 7), (8, 8), (9, 69), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 15), (16, 70), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b95) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 73) f8 .CF (fun _ => rfl) (adcR64M64Effect_fresh 0x112b95 12 (.sib 4 none 0 (.d8 0x10)) _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 64), (1, 1), (2, 65), (3, 3), (4, 4), (5, 56), (6, 67), (7, 7), (8, 8), (9, 69), (10, 10), (11, 11), (12, 72), (13, 58), (14, 14), (15, 15), (16, 73), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b9a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f9 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 76) f9 .CF (fun _ => rfl) (adcR64M64Effect_fresh 0x112b9a 11 (.sib 4 none 0 (.d8 0x20)) _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 77) (ρ' := [(0, 64), (1, 1), (2, 65), (3, 3), (4, 4), (5, 56), (6, 67), (7, 7), (8, 8), (9, 69), (10, 10), (11, 75), (12, 72), (13, 58), (14, 14), (15, 15), (16, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b9f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 64), (1, 1), (2, 65), (3, 3), (4, 4), (5, 56), (6, 67), (7, 7), (8, 8), (9, 69), (10, 78), (11, 75), (12, 72), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ba2) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 81) f11 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 82) (ρ' := [(0, 64), (1, 1), (2, 65), (3, 3), (4, 4), (5, 56), (6, 67), (7, 7), (8, 8), (9, 69), (10, 78), (11, 75), (12, 80), (13, 58), (14, 14), (15, 15), (16, 81), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ba5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 64), (1, 1), (2, 65), (3, 3), (4, 4), (5, 56), (6, 83), (7, 7), (8, 8), (9, 69), (10, 78), (11, 75), (12, 80), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ba9) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f13 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 64), (1, 1), (2, 65), (3, 3), (4, 4), (5, 56), (6, 83), (7, 7), (8, 8), (9, 85), (10, 78), (11, 75), (12, 80), (13, 58), (14, 14), (15, 15), (16, 86), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bac) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f14 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 89) f14 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x112bac 12 5 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 90) (ρ' := [(0, 64), (1, 1), (2, 65), (3, 3), (4, 4), (5, 56), (6, 83), (7, 7), (8, 8), (9, 85), (10, 78), (11, 75), (12, 88), (13, 58), (14, 14), (15, 15), (16, 89), (22, 22), (39, 39), (51, 51)]) (p' := 0x112baf) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 64), (1, 1), (2, 65), (3, 3), (4, 4), (5, 56), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 75), (12, 88), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bb3) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 1), (2, 65), (3, 3), (4, 4), (5, 56), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 75), (12, 88), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bb6) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 93), (1, 1), (2, 95), (3, 3), (4, 4), (5, 56), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 75), (12, 88), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bbd) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 98) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 99) (ρ' := [(0, 97), (1, 1), (2, 98), (3, 3), (4, 4), (5, 56), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 75), (12, 88), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bc0) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f19 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 97), (1, 1), (2, 98), (3, 3), (4, 4), (5, 100), (6, 91), (7, 7), (8, 8), (9, 85), (10, 78), (11, 75), (12, 88), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112bc3) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l118654_1 code

theorem block_l118654 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l118654 :=
  Rest.liftedBlock (rest_l118654 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l118654 x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
