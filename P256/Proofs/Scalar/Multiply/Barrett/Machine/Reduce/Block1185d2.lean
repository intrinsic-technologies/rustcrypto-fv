import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1185d2_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x112af2 bytes_l1185d2) [(0, 89), (1, 53), (2, 82), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (10, 91), (11, 67), (12, 84), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]
      11 0x112b4a bytes_l1185d2_1 b_l1185d2_1 := by
  have f20 : InstrSpec 0x112b4a [0x4D, 0x0F, 0xAF, 0xD3] (fun s => s.RIP = 0x112b4a) (imulR64R64Effect 0x112b4a 4 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x112b4a 4 10 11).toInstrSpec (imul_r64_r64_effect_step 0x112b4a 0x4d (by decide) 0xd3 (by decide)) pre_rip
  have f21 : InstrSpec 0x112b4e [0x4C, 0x01, 0xF8] (fun s => s.RIP = 0x112b4e) (addR64R64Effect 0x112b4e 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112b4e 0 15).toInstrSpec (add_r64_r64_effect_step 0x112b4e 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x112b51 [0x49, 0x29, 0xC2] (fun s => s.RIP = 0x112b51) (subR64R64Effect 0x112b51 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (subR64R64Effect_footprint 0x112b51 10 0).toInstrSpec (sub_r64_r64_effect_step 0x112b51 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x112b54 [0x48, 0xBA, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x112b54) (movR64Imm64Effect 0x112b54 2 0xffffffff00000000)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x112b54 2 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x112b54 0x48 0xba (by decide) (by decide) 0xffffffff00000000) pre_rip
  have f24 : InstrSpec 0x112b5e [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x112b5e) (movR64R64Effect 0x112b5e 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112b5e 0 14).toInstrSpec (mov_r64_r64_effect_step 0x112b5e 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x112b61 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x112b61) (mulR64Effect 0x112b61 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112b61 2).toInstrSpec (mul_r64_effect_step 0x112b61 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x112b64 [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x112b64) (movR64R64Effect 0x112b64 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x112b64 11 0).toInstrSpec (mov_r64_r64_effect_step 0x112b64 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x112b67 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x112b67) (movR64R64Effect 0x112b67 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x112b67 14 2).toInstrSpec (mov_r64_r64_effect_step 0x112b67 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x112b6a [0x49, 0x0F, 0xAF, 0xF0] (fun s => s.RIP = 0x112b6a) (imulR64R64Effect 0x112b6a 4 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x112b6a 4 6 8).toInstrSpec (imul_r64_r64_effect_step 0x112b6a 0x49 (by decide) 0xf0 (by decide)) pre_rip
  have f29 : InstrSpec 0x112b6e [0x49, 0x01, 0xF2] (fun s => s.RIP = 0x112b6e) (addR64R64Effect 0x112b6e 10 6)
      [.gpr 10, .gpr 6] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112b6e 10 6).toInstrSpec (add_r64_r64_effect_step 0x112b6e 0x49 0xf2 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x112b71 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x112b71) (movR64R64Effect 0x112b71 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112b71 0 3).toInstrSpec (mov_r64_r64_effect_step 0x112b71 0x48 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 89), (1, 53), (2, 82), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (10, 93), (11, 67), (12, 84), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b4e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 53), (2, 82), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (10, 93), (11, 67), (12, 84), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b51) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 53), (2, 82), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (10, 97), (11, 67), (12, 84), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b54) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 95), (1, 53), (2, 99), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (10, 97), (11, 67), (12, 84), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b5e) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 101), (1, 53), (2, 99), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (10, 97), (11, 67), (12, 84), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b61) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 104) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 105) (ρ' := [(0, 103), (1, 53), (2, 104), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (10, 97), (11, 67), (12, 84), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b64) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f26 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 103), (1, 53), (2, 104), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (10, 97), (11, 106), (12, 84), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b67) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f27 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 103), (1, 53), (2, 104), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (10, 97), (11, 106), (12, 84), (14, 108), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b6a) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f28 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 103), (1, 53), (2, 104), (3, 3), (4, 4), (6, 110), (7, 7), (8, 58), (9, 74), (10, 97), (11, 106), (12, 84), (14, 108), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b6e) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f29 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 103), (1, 53), (2, 104), (3, 3), (4, 4), (6, 110), (7, 7), (8, 58), (9, 74), (10, 112), (11, 106), (12, 84), (14, 108), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b71) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f30 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 114), (1, 53), (2, 104), (3, 3), (4, 4), (6, 110), (7, 7), (8, 58), (9, 74), (10, 112), (11, 106), (12, 84), (14, 108), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b74) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 116) (by decide) rfl

theorem rest_l1185d2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112af2 bytes_l1185d2) (entryMap (live .l1185d2))
      31 0x112af2 bytes_l1185d2 b_l1185d2 := by
  have f0 : InstrSpec 0x112af2 [0x48, 0x11, 0xD1] (fun s => s.RIP = 0x112af2) (atFlags StatusFlags.CF (adcR64R64Effect 0x112af2 1 2))
      [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112af2 1 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112af2 0x48 0xd1 c (by decide) (by decide))) pre_rip
  have f1 : InstrSpec 0x112af5 [0x48, 0x83, 0xD6, 0x00] (fun s => s.RIP = 0x112af5) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112af5 6 0x0))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112af5 6 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112af5 0x48 0xd6 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f2 : InstrSpec 0x112af9 [0x49, 0xB8, 0x51, 0x25, 0x63, 0xFC, 0xC2, 0xCA, 0xB9, 0xF3] (fun s => s.RIP = 0x112af9) (movR64Imm64Effect 0x112af9 8 0xf3b9cac2fc632551)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x112af9 8 0xf3b9cac2fc632551).toInstrSpec (mov_r64_imm64_effect_step 0x112af9 0x49 0xb8 (by decide) (by decide) 0xf3b9cac2fc632551) pre_rip
  have f3 : InstrSpec 0x112b03 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x112b03) (movR64R64Effect 0x112b03 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112b03 0 14).toInstrSpec (mov_r64_r64_effect_step 0x112b03 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x112b06 [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x112b06) (mulR64Effect 0x112b06 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112b06 8).toInstrSpec (mul_r64_effect_step 0x112b06 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112b09 [0x48, 0x89, 0x44, 0x24, 0x08] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112b09 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112b09 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112b09 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112b09 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112b09 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f6 : InstrSpec 0x112b0e [0x48, 0x89, 0x54, 0x24, 0x18] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112b0e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x112b0e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112b0e 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112b0e 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112b0e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f7 : InstrSpec 0x112b13 [0x49, 0xBB, 0x84, 0x9E, 0x17, 0xA7, 0xAD, 0xFA, 0xE6, 0xBC] (fun s => s.RIP = 0x112b13) (movR64Imm64Effect 0x112b13 11 0xbce6faada7179e84)
      [] [] [.reg 11, .rip] :=
    (movR64Imm64Effect_footprint 0x112b13 11 0xbce6faada7179e84).toInstrSpec (mov_r64_imm64_effect_step 0x112b13 0x49 0xbb (by decide) (by decide) 0xbce6faada7179e84) pre_rip
  have f8 : InstrSpec 0x112b1d [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x112b1d) (movR64R64Effect 0x112b1d 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112b1d 0 14).toInstrSpec (mov_r64_r64_effect_step 0x112b1d 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112b20 [0x49, 0xF7, 0xE3] (fun s => s.RIP = 0x112b20) (mulR64Effect 0x112b20 11)
      [.gpr 11, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112b20 11).toInstrSpec (mul_r64_effect_step 0x112b20 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x112b23 [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x112b23) (movR64R64Effect 0x112b23 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x112b23 9 0).toInstrSpec (mov_r64_r64_effect_step 0x112b23 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x112b26 [0x48, 0x89, 0x54, 0x24, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112b26 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x112b26 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112b26 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112b26 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112b26 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f12 : InstrSpec 0x112b2b [0x48, 0xC7, 0xC2, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x112b2b) (movR64Imm32Effect 0x112b2b 2 0xffffffff)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x112b2b 2 0xffffffff).toInstrSpec (mov_r64_imm32_effect_step 0x112b2b 0x48 0xc2 (by decide) (by decide) (by decide) 0xffffffff) pre_rip
  have f13 : InstrSpec 0x112b32 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x112b32) (movR64R64Effect 0x112b32 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112b32 0 14).toInstrSpec (mov_r64_r64_effect_step 0x112b32 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x112b35 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x112b35) (mulR64Effect 0x112b35 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112b35 2).toInstrSpec (mul_r64_effect_step 0x112b35 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x112b38 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x112b38) (movR64R64Effect 0x112b38 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x112b38 12 0).toInstrSpec (mov_r64_r64_effect_step 0x112b38 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x112b3b [0x48, 0x89, 0x54, 0x24, 0x20] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112b3b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x112b3b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112b3b 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112b3b 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112b3b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f17 : InstrSpec 0x112b40 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x112b40) (movR64R64Effect 0x112b40 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112b40 0 3).toInstrSpec (mov_r64_r64_effect_step 0x112b40 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x112b43 [0x48, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x112b43) (shlR64Effect 0x112b43 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x112b43 4 0 32).toInstrSpec (shl_r64_imm8_effect_step 0x112b43 0x48 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x112b47 [0x49, 0x89, 0xCA] (fun s => s.RIP = 0x112b47) (movR64R64Effect 0x112b47 10 1)
      [.gpr 1] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x112b47 10 1).toInstrSpec (mov_r64_r64_effect_step 0x112b47 0x49 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 54) f0 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x112af2 1 2 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (14, 14), (15, 15), (16, 54), (22, 22), (39, 39), (51, 51)]) (p' := 0x112af5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (6, 56), (7, 7), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112af9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b03) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 53), (2, 2), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b06) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 53), (2, 63), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b09) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 53), (2, 63), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b0e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 53), (2, 63), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b13) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 62), (1, 53), (2, 63), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (11, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b1d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 53), (2, 63), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (11, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b20) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 71), (1, 53), (2, 72), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (11, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b23) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 53), (2, 72), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (11, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b26) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 53), (2, 72), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (11, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b2b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 53), (2, 77), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (11, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b32) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 53), (2, 77), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (11, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b35) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 82) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 53), (2, 82), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (11, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b38) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f15 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 81), (1, 53), (2, 82), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (11, 67), (12, 84), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b3b) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 81), (1, 53), (2, 82), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (11, 67), (12, 84), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b40) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 53), (2, 82), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (11, 67), (12, 84), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b43) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 53), (2, 82), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (11, 67), (12, 84), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b47) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 89), (1, 53), (2, 82), (3, 3), (4, 4), (6, 56), (7, 7), (8, 58), (9, 74), (10, 91), (11, 67), (12, 84), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112b4a) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1185d2_1 code

theorem block_l1185d2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1185d2 :=
  Rest.liftedBlock (rest_l1185d2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1185d2 x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
