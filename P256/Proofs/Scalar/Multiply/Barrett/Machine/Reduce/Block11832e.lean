import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11832e_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x11284e bytes_l11832e) [(0, 90), (1, 56), (2, 88), (3, 84), (4, 4), (5, 77), (6, 6), (7, 7), (8, 64), (9, 58), (10, 73), (12, 53), (13, 66), (14, 75), (15, 86), (22, 22), (39, 39), (51, 51)]
      7 0x1128a6 bytes_l11832e_1 b_l11832e_1 := by
  have f20 : InstrSpec 0x1128a6 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x1128a6) (mulR64Effect 0x1128a6 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1128a6 2).toInstrSpec (mul_r64_effect_step 0x1128a6 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1128a9 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x1128a9) (movR64R64Effect 0x1128a9 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1128a9 6 0).toInstrSpec (mov_r64_r64_effect_step 0x1128a9 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x1128ac [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x1128ac) (movR64R64Effect 0x1128ac 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1128ac 11 2).toInstrSpec (mov_r64_r64_effect_step 0x1128ac 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x1128af [0x4D, 0x01, 0xC2] (fun s => s.RIP = 0x1128af) (addR64R64Effect 0x1128af 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1128af 10 8).toInstrSpec (add_r64_r64_effect_step 0x1128af 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x1128b2 [0x4C, 0x11, 0xF3] (fun s => s.RIP = 0x1128b2) (atFlags StatusFlags.CF (adcR64R64Effect 0x1128b2 3 14))
      [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1128b2 3 14).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1128b2 0x4c 0xf3 c (by decide) (by decide))) pre_rip
  have f25 : InstrSpec 0x1128b5 [0x4C, 0x11, 0xFE] (fun s => s.RIP = 0x1128b5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1128b5 6 15))
      [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1128b5 6 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1128b5 0x4c 0xfe c (by decide) (by decide))) pre_rip
  have f26 : InstrSpec 0x1128b8 [0x49, 0x11, 0xCB] (fun s => s.RIP = 0x1128b8) (atFlags StatusFlags.CF (adcR64R64Effect 0x1128b8 11 1))
      [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1128b8 11 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1128b8 0x49 0xcb c (by decide) (by decide))) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 94) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 95) (ρ' := [(0, 93), (1, 56), (2, 94), (3, 84), (4, 4), (5, 77), (6, 6), (7, 7), (8, 64), (9, 58), (10, 73), (12, 53), (13, 66), (14, 75), (15, 86), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128a9) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 93), (1, 56), (2, 94), (3, 84), (4, 4), (5, 77), (6, 96), (7, 7), (8, 64), (9, 58), (10, 73), (12, 53), (13, 66), (14, 75), (15, 86), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128ac) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f22 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 93), (1, 56), (2, 94), (3, 84), (4, 4), (5, 77), (6, 96), (7, 7), (8, 64), (9, 58), (10, 73), (11, 98), (12, 53), (13, 66), (14, 75), (15, 86), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128af) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f23 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 101) f23 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 102) (ρ' := [(0, 93), (1, 56), (2, 94), (3, 84), (4, 4), (5, 77), (6, 96), (7, 7), (8, 64), (9, 58), (10, 100), (11, 98), (12, 53), (13, 66), (14, 75), (15, 86), (16, 101), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128b2) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f24 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 104) f24 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x1128b2 3 14 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 105) (ρ' := [(0, 93), (1, 56), (2, 94), (3, 103), (4, 4), (5, 77), (6, 96), (7, 7), (8, 64), (9, 58), (10, 100), (11, 98), (12, 53), (13, 66), (14, 75), (15, 86), (16, 104), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128b5) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f25 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 107) f25 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x1128b5 6 15 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 108) (ρ' := [(0, 93), (1, 56), (2, 94), (3, 103), (4, 4), (5, 77), (6, 106), (7, 7), (8, 64), (9, 58), (10, 100), (11, 98), (12, 53), (13, 66), (14, 75), (15, 86), (16, 107), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128b8) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f26 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 110) f26 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x1128b8 11 1 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 111) (ρ' := [(0, 93), (1, 56), (2, 94), (3, 103), (4, 4), (5, 77), (6, 106), (7, 7), (8, 64), (9, 58), (10, 100), (11, 109), (12, 53), (13, 66), (14, 75), (15, 86), (16, 110), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128bb) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 112) (by decide) rfl

theorem rest_l11832e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11284e bytes_l11832e) (entryMap (live .l11832e))
      27 0x11284e bytes_l11832e b_l11832e := by
  have f0 : InstrSpec 0x11284e [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x11284e) (movR64R64Effect 0x11284e 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x11284e 12 2).toInstrSpec (mov_r64_r64_effect_step 0x11284e 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x112851 [0x48, 0x89, 0x74, 0x24, 0x28] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112851 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x112851 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112851 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112851 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112851 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f2 : InstrSpec 0x112856 [0x48, 0x8B, 0x4E, 0x18] (LoadPre 0x112856 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x112856 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112856 1 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x112856 1 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x112856 0x48 (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11285a [0x49, 0xB9, 0xFE, 0x9B, 0xDF, 0xEE, 0x85, 0xFD, 0x2F, 0x01] (fun s => s.RIP = 0x11285a) (movR64Imm64Effect 0x11285a 9 0x12ffd85eedf9bfe)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x11285a 9 0x12ffd85eedf9bfe).toInstrSpec (mov_r64_imm64_effect_step 0x11285a 0x49 0xb9 (by decide) (by decide) 0x12ffd85eedf9bfe) pre_rip
  have f4 : InstrSpec 0x112864 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x112864) (movR64R64Effect 0x112864 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112864 0 1).toInstrSpec (mov_r64_r64_effect_step 0x112864 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112867 [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x112867) (mulR64Effect 0x112867 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112867 9).toInstrSpec (mul_r64_effect_step 0x112867 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11286a [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x11286a) (movR64R64Effect 0x11286a 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x11286a 8 2).toInstrSpec (mov_r64_r64_effect_step 0x11286a 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11286d [0x49, 0xBD, 0x21, 0x6C, 0x1A, 0xDF, 0x52, 0x05, 0x19, 0x43] (fun s => s.RIP = 0x11286d) (movR64Imm64Effect 0x11286d 13 0x43190552df1a6c21)
      [] [] [.reg 13, .rip] :=
    (movR64Imm64Effect_footprint 0x11286d 13 0x43190552df1a6c21).toInstrSpec (mov_r64_imm64_effect_step 0x11286d 0x49 0xbd (by decide) (by decide) 0x43190552df1a6c21) pre_rip
  have f8 : InstrSpec 0x112877 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x112877) (movR64R64Effect 0x112877 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112877 0 1).toInstrSpec (mov_r64_r64_effect_step 0x112877 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11287a [0x49, 0xF7, 0xE5] (fun s => s.RIP = 0x11287a) (mulR64Effect 0x11287a 13)
      [.gpr 13, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11287a 13).toInstrSpec (mul_r64_effect_step 0x11287a 0x49 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11287d [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x11287d) (movR64R64Effect 0x11287d 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x11287d 10 0).toInstrSpec (mov_r64_r64_effect_step 0x11287d 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x112880 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x112880) (movR64R64Effect 0x112880 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x112880 14 2).toInstrSpec (mov_r64_r64_effect_step 0x112880 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x112883 [0x48, 0xBD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x112883) (movR64Imm64Effect 0x112883 5 0xfffffffeffffffff)
      [] [] [.reg 5, .rip] :=
    (movR64Imm64Effect_footprint 0x112883 5 0xfffffffeffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x112883 0x48 0xbd (by decide) (by decide) 0xfffffffeffffffff) pre_rip
  have f13 : InstrSpec 0x11288d [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x11288d) (movR64R64Effect 0x11288d 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11288d 0 1).toInstrSpec (mov_r64_r64_effect_step 0x11288d 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x112890 [0x48, 0xF7, 0xE5] (fun s => s.RIP = 0x112890) (mulR64Effect 0x112890 5)
      [.gpr 5, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112890 5).toInstrSpec (mul_r64_effect_step 0x112890 0x48 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x112893 [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x112893) (movR64R64Effect 0x112893 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x112893 3 0).toInstrSpec (mov_r64_r64_effect_step 0x112893 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x112896 [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x112896) (movR64R64Effect 0x112896 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x112896 15 2).toInstrSpec (mov_r64_r64_effect_step 0x112896 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x112899 [0xBA, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x112899) (movR32Imm32Effect 0x112899 5 2 0xffffffff)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x112899 5 2 0xffffffff).toInstrSpec (mov_r32_imm32_effect_step 0x112899 0xba (by decide) 0xffffffff) pre_rip
  have f18 : InstrSpec 0x11289e [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x11289e) (movR64R64Effect 0x11289e 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11289e 0 1).toInstrSpec (mov_r64_r64_effect_step 0x11289e 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1128a1 [0x48, 0x89, 0x4C, 0x24, 0x38] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1128a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1128a1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1128a1 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1128a1 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1128a1 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (6, 6), (7, 7), (12, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x112851) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(2, 2), (4, 4), (6, 6), (7, 7), (12, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x112856) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 56), (2, 2), (4, 4), (6, 6), (7, 7), (12, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x11285a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 56), (2, 2), (4, 4), (6, 6), (7, 7), (9, 58), (12, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x112864) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 56), (2, 2), (4, 4), (6, 6), (7, 7), (9, 58), (12, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x112867) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 56), (2, 62), (4, 4), (6, 6), (7, 7), (9, 58), (12, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x11286a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 56), (2, 62), (4, 4), (6, 6), (7, 7), (8, 64), (9, 58), (12, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x11286d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 56), (2, 62), (4, 4), (6, 6), (7, 7), (8, 64), (9, 58), (12, 53), (13, 66), (22, 22), (39, 39), (51, 51)]) (p' := 0x112877) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 56), (2, 62), (4, 4), (6, 6), (7, 7), (8, 64), (9, 58), (12, 53), (13, 66), (22, 22), (39, 39), (51, 51)]) (p' := 0x11287a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 70), (1, 56), (2, 71), (4, 4), (6, 6), (7, 7), (8, 64), (9, 58), (12, 53), (13, 66), (22, 22), (39, 39), (51, 51)]) (p' := 0x11287d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 70), (1, 56), (2, 71), (4, 4), (6, 6), (7, 7), (8, 64), (9, 58), (10, 73), (12, 53), (13, 66), (22, 22), (39, 39), (51, 51)]) (p' := 0x112880) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 70), (1, 56), (2, 71), (4, 4), (6, 6), (7, 7), (8, 64), (9, 58), (10, 73), (12, 53), (13, 66), (14, 75), (22, 22), (39, 39), (51, 51)]) (p' := 0x112883) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 70), (1, 56), (2, 71), (4, 4), (5, 77), (6, 6), (7, 7), (8, 64), (9, 58), (10, 73), (12, 53), (13, 66), (14, 75), (22, 22), (39, 39), (51, 51)]) (p' := 0x11288d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 56), (2, 71), (4, 4), (5, 77), (6, 6), (7, 7), (8, 64), (9, 58), (10, 73), (12, 53), (13, 66), (14, 75), (22, 22), (39, 39), (51, 51)]) (p' := 0x112890) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 82) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 56), (2, 82), (4, 4), (5, 77), (6, 6), (7, 7), (8, 64), (9, 58), (10, 73), (12, 53), (13, 66), (14, 75), (22, 22), (39, 39), (51, 51)]) (p' := 0x112893) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f15 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 81), (1, 56), (2, 82), (3, 84), (4, 4), (5, 77), (6, 6), (7, 7), (8, 64), (9, 58), (10, 73), (12, 53), (13, 66), (14, 75), (22, 22), (39, 39), (51, 51)]) (p' := 0x112896) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f16 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 81), (1, 56), (2, 82), (3, 84), (4, 4), (5, 77), (6, 6), (7, 7), (8, 64), (9, 58), (10, 73), (12, 53), (13, 66), (14, 75), (15, 86), (22, 22), (39, 39), (51, 51)]) (p' := 0x112899) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 81), (1, 56), (2, 88), (3, 84), (4, 4), (5, 77), (6, 6), (7, 7), (8, 64), (9, 58), (10, 73), (12, 53), (13, 66), (14, 75), (15, 86), (22, 22), (39, 39), (51, 51)]) (p' := 0x11289e) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (1, 56), (2, 88), (3, 84), (4, 4), (5, 77), (6, 6), (7, 7), (8, 64), (9, 58), (10, 73), (12, 53), (13, 66), (14, 75), (15, 86), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128a1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 90), (1, 56), (2, 88), (3, 84), (4, 4), (5, 77), (6, 6), (7, 7), (8, 64), (9, 58), (10, 73), (12, 53), (13, 66), (14, 75), (15, 86), (22, 22), (39, 39), (51, 51)]) (p' := 0x1128a6) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l11832e_1 code

theorem block_l11832e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11832e :=
  Rest.liftedBlock (rest_l11832e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11832e x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
