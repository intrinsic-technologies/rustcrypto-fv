import K256.Proofs.Ecdh.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Ecdh.LIR.Generated.Values

namespace K256.Proofs.Ecdh.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR

theorem rest_l10e4c0_24 [Bindings] (code : CodeMap) :
    Rest (n := 1081) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 1058), (1, 1061), (2, 1079), (3, 1023), (4, 65), (5, 760), (6, 1074), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]
      13 0x10ec62 bytes_l10e4c0_24 b_l10e4c0_24 := by
  have f480 : InstrSpec 0x10ec62 [0x48, 0x21, 0xF1] (fun s => s.RIP = 0x10ec62) (andR64R64Effect 0x10ec62 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ec62 1 6).toInstrSpec (and_r64_r64_effect_step 0x10ec62 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f481 : InstrSpec 0x10ec65 [0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x10ec65) (movR64Imm64Effect 0x10ec65 0 0xffffffffffff)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x10ec65 0 0xffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10ec65 0x48 0xb8 (by decide) (by decide) 0xffffffffffff) pre_rip
  have f482 : InstrSpec 0x10ec6f [0x48, 0x21, 0xC5] (fun s => s.RIP = 0x10ec6f) (andR64R64Effect 0x10ec6f 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ec6f 5 0).toInstrSpec (and_r64_r64_effect_step 0x10ec6f 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f483 : InstrSpec 0x10ec72 [0x48, 0x01, 0xD5] (fun s => s.RIP = 0x10ec72) (addR64R64Effect 0x10ec72 5 2)
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10ec72 5 2).toInstrSpec (add_r64_r64_effect_step 0x10ec72 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f484 : InstrSpec 0x10ec75 [0x4C, 0x89, 0x9C, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x10ec75 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10ec75 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ec75 11 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ec75 11 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x10ec75 0x4c (by decide) 3 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f485 : InstrSpec 0x10ec7d [0x48, 0x89, 0xBC, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x10ec7d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10ec7d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ec7d 7 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ec7d 7 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x10ec7d 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f486 : InstrSpec 0x10ec85 [0x4C, 0x89, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x10ec85 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10ec85 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ec85 15 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ec85 15 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x10ec85 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f487 : InstrSpec 0x10ec8d [0x48, 0x89, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x10ec8d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10ec8d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ec8d 1 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ec8d 1 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x10ec8d 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f488 : InstrSpec 0x10ec95 [0x48, 0x89, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x10ec95 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10ec95 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ec95 5 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ec95 5 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x10ec95 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f489 : InstrSpec 0x10ec9d [0x48, 0x8D, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ec9d) (leaR64Effect 0x10ec9d 6 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10ec9d 6 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (lea_r64_effect_step 0x10ec9d 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) pre_rip
  have f490 : InstrSpec 0x10eca5 [0x48, 0x8B, 0x5C, 0x24, 0x60] (LoadPre 0x10eca5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10eca5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10eca5 3 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10eca5 3 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x10eca5 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f491 : InstrSpec 0x10ecaa [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10ecaa) (movR64R64Effect 0x10ecaa 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10ecaa 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10ecaa 0x48 0xdf (by decide) (by decide)) pre_rip
  have f492 : InstrSpec 0x10ecad [0xE8, 0x7E, 0x5C, 0x00, 0x00] (PushPre 0x10ecad 5) (callEffect (fun _ => 0x114930) 0x10ecb2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10ecad 0x114930 0x10ecb2).toInstrSpec (call_rel32_effect_step 0x10ecad 0x5c7e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 1081) (RestInside.out (n := 1081) f480 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1082) (ρ' := [(0, 1058), (1, 1081), (2, 1079), (3, 1023), (4, 65), (5, 760), (6, 1074), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec65) f480 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1083) (RestInside.out (n := 1083) f481 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1084) (ρ' := [(0, 1083), (1, 1081), (2, 1079), (3, 1023), (4, 65), (5, 760), (6, 1074), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec6f) f481 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1085) (RestInside.out (n := 1085) f482 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1086) (ρ' := [(0, 1083), (1, 1081), (2, 1079), (3, 1023), (4, 65), (5, 1085), (6, 1074), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec72) f482 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1087) (RestInside.out (n := 1087) f483 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1088) (ρ' := [(0, 1083), (1, 1081), (2, 1079), (3, 1023), (4, 65), (5, 1087), (6, 1074), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec75) f483 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1089) (RestInside.exec (n := 1089) (ρ' := [(0, 1083), (1, 1081), (2, 1079), (3, 1023), (4, 65), (5, 1087), (6, 1074), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec7d) f484 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1090) (RestInside.exec (n := 1090) (ρ' := [(0, 1083), (1, 1081), (2, 1079), (3, 1023), (4, 65), (5, 1087), (6, 1074), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec85) f485 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1091) (RestInside.exec (n := 1091) (ρ' := [(0, 1083), (1, 1081), (2, 1079), (3, 1023), (4, 65), (5, 1087), (6, 1074), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec8d) f486 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1092) (RestInside.exec (n := 1092) (ρ' := [(0, 1083), (1, 1081), (2, 1079), (3, 1023), (4, 65), (5, 1087), (6, 1074), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec95) f487 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1093) (RestInside.exec (n := 1093) (ρ' := [(0, 1083), (1, 1081), (2, 1079), (3, 1023), (4, 65), (5, 1087), (6, 1074), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec9d) f488 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1094) (RestInside.out (n := 1094) f489 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1095) (ρ' := [(0, 1083), (1, 1081), (2, 1079), (3, 1023), (4, 65), (5, 1087), (6, 1094), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eca5) f489 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1096) (RestInside.out (n := 1096) f490 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1097) (ρ' := [(0, 1083), (1, 1081), (2, 1079), (3, 1096), (4, 65), (5, 1087), (6, 1094), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecaa) f490 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1098) (RestInside.out (n := 1098) f491 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1099) (ρ' := [(0, 1083), (1, 1081), (2, 1079), (3, 1096), (4, 65), (5, 1087), (6, 1094), (7, 1098), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecad) f491 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1100) (RestInside.out (n := 1100) f492 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1101) (ρ' := [(0, 1083), (1, 1081), (2, 1079), (3, 1096), (4, 1100), (5, 1087), (6, 1094), (7, 1098), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114930) f492 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 1102) (by decide) (by decide) rfl rfl

theorem rest_l10e4c0_23 [Bindings] (code : CodeMap) :
    Rest (n := 1039) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 1020), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1012), (10, 1009), (11, 894), (12, 1034), (13, 980), (14, 957), (15, 1036), (16, 1037), (22, 22), (39, 39), (50, 50), (51, 51)]
      33 0x10ec0a bytes_l10e4c0_23 b_l10e4c0_23 := by
  have f460 : InstrSpec 0x10ec0a [0x49, 0x11, 0xD4] (fun s => s.RIP = 0x10ec0a) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ec0a 12 2))
      [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10ec0a 12 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10ec0a 0x49 0xd4 c (by decide) (by decide))) pre_rip
  have f461 : InstrSpec 0x10ec0d [0x48, 0x8B, 0x44, 0x24, 0x78] (LoadPre 0x10ec0d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10ec0d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ec0d 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ec0d 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x10ec0d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f462 : InstrSpec 0x10ec12 [0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x10ec12 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10ec12 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ec12 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ec12 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x10ec12 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f463 : InstrSpec 0x10ec1a [0x4D, 0x01, 0xF7] (fun s => s.RIP = 0x10ec1a) (addR64R64Effect 0x10ec1a 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10ec1a 15 14).toInstrSpec (add_r64_r64_effect_step 0x10ec1a 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f464 : InstrSpec 0x10ec1d [0x49, 0x83, 0xD4, 0x00] (fun s => s.RIP = 0x10ec1d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ec1d 12 0x0))
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10ec1d 12 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10ec1d 0x49 0xd4 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f465 : InstrSpec 0x10ec21 [0x4D, 0x0F, 0xA4, 0xD1, 0x0C] (fun s => s.RIP = 0x10ec21) (shldR64R64Effect 0x10ec21 5 9 10 12)
      [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10ec21 5 9 10 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10ec21 0x4d (by decide) 0xd1 (by decide) 0xc) pre_rip
  have f466 : InstrSpec 0x10ec26 [0x4D, 0x0F, 0xA4, 0xFC, 0x0C] (fun s => s.RIP = 0x10ec26) (shldR64R64Effect 0x10ec26 5 12 15 12)
      [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10ec26 5 12 15 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10ec26 0x4d (by decide) 0xfc (by decide) 0xc) pre_rip
  have f467 : InstrSpec 0x10ec2b [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x10ec2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10ec2b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ec2b 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ec2b 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10ec2b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f468 : InstrSpec 0x10ec30 [0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x10ec30 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10ec30 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ec30 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ec30 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x10ec30 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f469 : InstrSpec 0x10ec38 [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x10ec38) (movR64R64Effect 0x10ec38 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10ec38 0 9).toInstrSpec (mov_r64_r64_effect_step 0x10ec38 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f470 : InstrSpec 0x10ec3b [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x10ec3b) (mulR64Effect 0x10ec3b 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10ec3b 8).toInstrSpec (mul_r64_effect_step 0x10ec3b 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f471 : InstrSpec 0x10ec3e [0x48, 0x89, 0xF1] (fun s => s.RIP = 0x10ec3e) (movR64R64Effect 0x10ec3e 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10ec3e 1 6).toInstrSpec (mov_r64_r64_effect_step 0x10ec3e 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f472 : InstrSpec 0x10ec41 [0x49, 0x21, 0xF7] (fun s => s.RIP = 0x10ec41) (andR64R64Effect 0x10ec41 15 6)
      [.gpr 15, .gpr 6] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ec41 15 6).toInstrSpec (and_r64_r64_effect_step 0x10ec41 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f473 : InstrSpec 0x10ec44 [0x48, 0x8B, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x10ec44 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10ec44 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ec44 6 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10ec44 6 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x10ec44 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f474 : InstrSpec 0x10ec4c [0x48, 0x21, 0xCE] (fun s => s.RIP = 0x10ec4c) (andR64R64Effect 0x10ec4c 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ec4c 6 1).toInstrSpec (and_r64_r64_effect_step 0x10ec4c 0x48 0xce (by decide) (by decide)) pre_rip
  have f475 : InstrSpec 0x10ec4f [0x48, 0x01, 0xC6] (fun s => s.RIP = 0x10ec4f) (addR64R64Effect 0x10ec4f 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10ec4f 6 0).toInstrSpec (add_r64_r64_effect_step 0x10ec4f 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f476 : InstrSpec 0x10ec52 [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x10ec52) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ec52 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10ec52 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10ec52 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f477 : InstrSpec 0x10ec56 [0x4C, 0x01, 0xE6] (fun s => s.RIP = 0x10ec56) (addR64R64Effect 0x10ec56 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10ec56 6 12).toInstrSpec (add_r64_r64_effect_step 0x10ec56 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f478 : InstrSpec 0x10ec59 [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x10ec59) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ec59 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10ec59 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10ec59 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f479 : InstrSpec 0x10ec5d [0x48, 0x0F, 0xA4, 0xF2, 0x0C] (fun s => s.RIP = 0x10ec5d) (shldR64R64Effect 0x10ec5d 5 2 6 12)
      [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10ec5d 5 2 6 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10ec5d 0x48 (by decide) 0xf2 (by decide) 0xc) pre_rip
  refine Rest.ofInside (n := 1039) (RestInside.out (n := 1039) f460 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1040) (ρ' := [(0, 1020), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1012), (10, 1009), (11, 894), (12, 1039), (13, 980), (14, 957), (15, 1036), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec0d) f460 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1041) (RestInside.out (n := 1041) f461 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1042) (ρ' := [(0, 1041), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1012), (10, 1009), (11, 894), (12, 1039), (13, 980), (14, 957), (15, 1036), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec12) f461 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1043) (RestInside.exec (n := 1043) (ρ' := [(0, 1041), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1012), (10, 1009), (11, 894), (12, 1039), (13, 980), (14, 957), (15, 1036), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec1a) f462 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1044) (RestInside.out (n := 1044) f463 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1045) f463 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 1046) (ρ' := [(0, 1041), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1012), (10, 1009), (11, 894), (12, 1039), (13, 980), (14, 957), (15, 1044), (16, 1045), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec1d) f463 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1047) (RestInside.out (n := 1047) f464 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1048) (ρ' := [(0, 1041), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1012), (10, 1009), (11, 894), (12, 1047), (13, 980), (14, 957), (15, 1044), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec21) f464 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1049) (RestInside.out (n := 1049) f465 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1050) (ρ' := [(0, 1041), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1047), (13, 980), (14, 957), (15, 1044), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec26) f465 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1051) (RestInside.out (n := 1051) f466 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1052) (ρ' := [(0, 1041), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1044), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec2b) f466 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1053) (RestInside.out (n := 1053) f467 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1054) (ρ' := [(0, 1053), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1044), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec30) f467 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1055) (RestInside.exec (n := 1055) (ρ' := [(0, 1053), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1044), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec38) f468 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1056) (RestInside.out (n := 1056) f469 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1057) (ρ' := [(0, 1056), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1044), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec3b) f469 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1058) (RestInside.out (n := 1058) f470 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1059) f470 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 1060) (ρ' := [(0, 1058), (1, 982), (2, 1059), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1044), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec3e) f470 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1061) (RestInside.out (n := 1061) f471 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1062) (ρ' := [(0, 1058), (1, 1061), (2, 1059), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1044), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec41) f471 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1063) (RestInside.out (n := 1063) f472 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1064) (ρ' := [(0, 1058), (1, 1061), (2, 1059), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec44) f472 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1065) (RestInside.out (n := 1065) f473 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1066) (ρ' := [(0, 1058), (1, 1061), (2, 1059), (3, 1023), (4, 65), (5, 760), (6, 1065), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec4c) f473 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1067) (RestInside.out (n := 1067) f474 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1068) (ρ' := [(0, 1058), (1, 1061), (2, 1059), (3, 1023), (4, 65), (5, 760), (6, 1067), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec4f) f474 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1069) (RestInside.out (n := 1069) f475 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1070) f475 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 1071) (ρ' := [(0, 1058), (1, 1061), (2, 1059), (3, 1023), (4, 65), (5, 760), (6, 1069), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (16, 1070), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec52) f475 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1072) (RestInside.out (n := 1072) f476 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1073) (ρ' := [(0, 1058), (1, 1061), (2, 1072), (3, 1023), (4, 65), (5, 760), (6, 1069), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec56) f476 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1074) (RestInside.out (n := 1074) f477 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1075) f477 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 1076) (ρ' := [(0, 1058), (1, 1061), (2, 1072), (3, 1023), (4, 65), (5, 760), (6, 1074), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (16, 1075), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec59) f477 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1077) (RestInside.out (n := 1077) f478 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1078) (ρ' := [(0, 1058), (1, 1061), (2, 1077), (3, 1023), (4, 65), (5, 760), (6, 1074), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec5d) f478 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1079) (RestInside.out (n := 1079) f479 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1080) (ρ' := [(0, 1058), (1, 1061), (2, 1079), (3, 1023), (4, 65), (5, 760), (6, 1074), (7, 986), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec62) f479 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_24 code

theorem rest_l10e4c0_22 [Bindings] (code : CodeMap) :
    Rest (n := 993) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 990), (1, 982), (2, 991), (3, 890), (4, 65), (5, 760), (6, 984), (7, 986), (8, 927), (9, 863), (10, 892), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]
      53 0x10ebb7 bytes_l10e4c0_22 b_l10e4c0_22 := by
  have f440 : InstrSpec 0x10ebb7 [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x10ebb7) (movR64R64Effect 0x10ebb7 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10ebb7 9 2).toInstrSpec (mov_r64_r64_effect_step 0x10ebb7 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f441 : InstrSpec 0x10ebba [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x10ebba) (movR64R64Effect 0x10ebba 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10ebba 3 0).toInstrSpec (mov_r64_r64_effect_step 0x10ebba 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f442 : InstrSpec 0x10ebbd [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x10ebbd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10ebbd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ebbd 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ebbd 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10ebbd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f443 : InstrSpec 0x10ebc2 [0x48, 0xF7, 0x64, 0x24, 0x50] (LoadPre 0x10ebc2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10ebc2 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10ebc2 5 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10ebc2 5 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mul_m64_effect_step 0x10ebc2 0x48 (by decide) (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f444 : InstrSpec 0x10ebc7 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x10ebc7) (movR64R64Effect 0x10ebc7 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10ebc7 10 0).toInstrSpec (mov_r64_r64_effect_step 0x10ebc7 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f445 : InstrSpec 0x10ebca [0x49, 0x01, 0xDA] (fun s => s.RIP = 0x10ebca) (addR64R64Effect 0x10ebca 10 3)
      [.gpr 10, .gpr 3] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10ebca 10 3).toInstrSpec (add_r64_r64_effect_step 0x10ebca 0x49 0xda (by decide) (by decide)) pre_rip
  have f446 : InstrSpec 0x10ebcd [0x49, 0x11, 0xD1] (fun s => s.RIP = 0x10ebcd) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ebcd 9 2))
      [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10ebcd 9 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10ebcd 0x49 0xd1 c (by decide) (by decide))) pre_rip
  have f447 : InstrSpec 0x10ebd0 [0x4D, 0x01, 0xC2] (fun s => s.RIP = 0x10ebd0) (addR64R64Effect 0x10ebd0 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10ebd0 10 8).toInstrSpec (add_r64_r64_effect_step 0x10ebd0 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f448 : InstrSpec 0x10ebd3 [0x49, 0x83, 0xD1, 0x00] (fun s => s.RIP = 0x10ebd3) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ebd3 9 0x0))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10ebd3 9 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10ebd3 0x49 0xd1 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f449 : InstrSpec 0x10ebd7 [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x10ebd7) (movR64R64Effect 0x10ebd7 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10ebd7 0 10).toInstrSpec (mov_r64_r64_effect_step 0x10ebd7 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f450 : InstrSpec 0x10ebda [0x48, 0x21, 0xF0] (fun s => s.RIP = 0x10ebda) (andR64R64Effect 0x10ebda 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ebda 0 6).toInstrSpec (and_r64_r64_effect_step 0x10ebda 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f451 : InstrSpec 0x10ebdd [0x49, 0xB8, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ebdd) (movR64Imm64Effect 0x10ebdd 8 0x1000003d10)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x10ebdd 8 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x10ebdd 0x49 0xb8 (by decide) (by decide) 0x1000003d10) pre_rip
  have f452 : InstrSpec 0x10ebe7 [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x10ebe7) (mulR64Effect 0x10ebe7 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10ebe7 8).toInstrSpec (mul_r64_effect_step 0x10ebe7 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f453 : InstrSpec 0x10ebea [0x48, 0x8B, 0x5C, 0x24, 0x08] (LoadPre 0x10ebea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10ebea + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ebea 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10ebea 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10ebea 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f454 : InstrSpec 0x10ebef [0x48, 0x89, 0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x10ebef 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10ebef + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ebef 3 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ebef 3 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x10ebef 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f455 : InstrSpec 0x10ebf7 [0x4C, 0x03, 0x7C, 0x24, 0x20] (LoadPre 0x10ebf7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ebf7 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10ebf7 15 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 15, .gpr 4] [] [.reg 15, .flags, .rip] :=
    (addR64M64Effect_footprint 0x10ebf7 15 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (add_r64_m64_effect_step 0x10ebf7 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f456 : InstrSpec 0x10ebfc [0x4C, 0x13, 0x64, 0x24, 0x30] (LoadPre 0x10ebfc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10ebfc + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10ebfc 12 (.sib 4 none 0 (.d8 0x30))))
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10ebfc 12 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10ebfc 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f457 : InstrSpec 0x10ec01 [0x4D, 0x01, 0xEF] (fun s => s.RIP = 0x10ec01) (addR64R64Effect 0x10ec01 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10ec01 15 13).toInstrSpec (add_r64_r64_effect_step 0x10ec01 0x4d 0xef (by decide) (by decide)) pre_rip
  have f458 : InstrSpec 0x10ec04 [0x49, 0x11, 0xCC] (fun s => s.RIP = 0x10ec04) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ec04 12 1))
      [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10ec04 12 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10ec04 0x49 0xcc c (by decide) (by decide))) pre_rip
  have f459 : InstrSpec 0x10ec07 [0x49, 0x01, 0xC7] (fun s => s.RIP = 0x10ec07) (addR64R64Effect 0x10ec07 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10ec07 15 0).toInstrSpec (add_r64_r64_effect_step 0x10ec07 0x49 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 993) (RestInside.out (n := 993) f440 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 994) (ρ' := [(0, 990), (1, 982), (2, 991), (3, 890), (4, 65), (5, 760), (6, 984), (7, 986), (8, 927), (9, 993), (10, 892), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebba) f440 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 995) (RestInside.out (n := 995) f441 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 996) (ρ' := [(0, 990), (1, 982), (2, 991), (3, 995), (4, 65), (5, 760), (6, 984), (7, 986), (8, 927), (9, 993), (10, 892), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebbd) f441 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 997) (RestInside.out (n := 997) f442 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 998) (ρ' := [(0, 997), (1, 982), (2, 991), (3, 995), (4, 65), (5, 760), (6, 984), (7, 986), (8, 927), (9, 993), (10, 892), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebc2) f442 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 999) (RestInside.out (n := 999) f443 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1000) f443 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 1001) (ρ' := [(0, 999), (1, 982), (2, 1000), (3, 995), (4, 65), (5, 760), (6, 984), (7, 986), (8, 927), (9, 993), (10, 892), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebc7) f443 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1002) (RestInside.out (n := 1002) f444 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1003) (ρ' := [(0, 999), (1, 982), (2, 1000), (3, 995), (4, 65), (5, 760), (6, 984), (7, 986), (8, 927), (9, 993), (10, 1002), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebca) f444 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1004) (RestInside.out (n := 1004) f445 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1005) f445 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 1006) (ρ' := [(0, 999), (1, 982), (2, 1000), (3, 995), (4, 65), (5, 760), (6, 984), (7, 986), (8, 927), (9, 993), (10, 1004), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (16, 1005), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebcd) f445 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1007) (RestInside.out (n := 1007) f446 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1008) (ρ' := [(0, 999), (1, 982), (2, 1000), (3, 995), (4, 65), (5, 760), (6, 984), (7, 986), (8, 927), (9, 1007), (10, 1004), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebd0) f446 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1009) (RestInside.out (n := 1009) f447 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1010) f447 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 1011) (ρ' := [(0, 999), (1, 982), (2, 1000), (3, 995), (4, 65), (5, 760), (6, 984), (7, 986), (8, 927), (9, 1007), (10, 1009), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (16, 1010), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebd3) f447 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1012) (RestInside.out (n := 1012) f448 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1013) (ρ' := [(0, 999), (1, 982), (2, 1000), (3, 995), (4, 65), (5, 760), (6, 984), (7, 986), (8, 927), (9, 1012), (10, 1009), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebd7) f448 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1014) (RestInside.out (n := 1014) f449 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1015) (ρ' := [(0, 1014), (1, 982), (2, 1000), (3, 995), (4, 65), (5, 760), (6, 984), (7, 986), (8, 927), (9, 1012), (10, 1009), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebda) f449 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1016) (RestInside.out (n := 1016) f450 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1017) (ρ' := [(0, 1016), (1, 982), (2, 1000), (3, 995), (4, 65), (5, 760), (6, 984), (7, 986), (8, 927), (9, 1012), (10, 1009), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebdd) f450 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1018) (RestInside.out (n := 1018) f451 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1019) (ρ' := [(0, 1016), (1, 982), (2, 1000), (3, 995), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1012), (10, 1009), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebe7) f451 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1020) (RestInside.out (n := 1020) f452 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1021) f452 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 1022) (ρ' := [(0, 1020), (1, 982), (2, 1021), (3, 995), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1012), (10, 1009), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebea) f452 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1023) (RestInside.out (n := 1023) f453 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1024) (ρ' := [(0, 1020), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1012), (10, 1009), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebef) f453 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1025) (RestInside.exec (n := 1025) (ρ' := [(0, 1020), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1012), (10, 1009), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebf7) f454 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1026) (RestInside.out (n := 1026) f455 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1027) f455 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 1028) (ρ' := [(0, 1020), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1012), (10, 1009), (11, 894), (12, 971), (13, 980), (14, 957), (15, 1026), (16, 1027), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebfc) f455 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1029) (RestInside.out (n := 1029) f456 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1030) (ρ' := [(0, 1020), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1012), (10, 1009), (11, 894), (12, 1029), (13, 980), (14, 957), (15, 1026), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec01) f456 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1031) (RestInside.out (n := 1031) f457 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1032) f457 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 1033) (ρ' := [(0, 1020), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1012), (10, 1009), (11, 894), (12, 1029), (13, 980), (14, 957), (15, 1031), (16, 1032), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec04) f457 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1034) (RestInside.out (n := 1034) f458 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1035) (ρ' := [(0, 1020), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1012), (10, 1009), (11, 894), (12, 1034), (13, 980), (14, 957), (15, 1031), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec07) f458 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1036) (RestInside.out (n := 1036) f459 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 1037) f459 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 1038) (ρ' := [(0, 1020), (1, 982), (2, 1021), (3, 1023), (4, 65), (5, 760), (6, 984), (7, 986), (8, 1018), (9, 1012), (10, 1009), (11, 894), (12, 1034), (13, 980), (14, 957), (15, 1036), (16, 1037), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ec0a) f459 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_23 code

theorem rest_l10e4c0_21 [Bindings] (code : CodeMap) :
    Rest (n := 952) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 946), (1, 931), (2, 934), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 944), (15, 865), (16, 950), (22, 22), (39, 39), (50, 50), (51, 51)]
      73 0x10eb5f bytes_l10e4c0_21 b_l10e4c0_21 := by
  have f420 : InstrSpec 0x10eb5f [0x49, 0x83, 0xD6, 0x00] (fun s => s.RIP = 0x10eb5f) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10eb5f 14 0x0))
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10eb5f 14 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10eb5f 0x49 0xd6 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f421 : InstrSpec 0x10eb63 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x10eb63 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10eb63 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10eb63 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10eb63 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10eb63 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f422 : InstrSpec 0x10eb68 [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x10eb68 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10eb68 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10eb68 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10eb68 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x10eb68 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f423 : InstrSpec 0x10eb70 [0x49, 0x0F, 0xA4, 0xFE, 0x0C] (fun s => s.RIP = 0x10eb70) (shldR64R64Effect 0x10eb70 5 14 7 12)
      [.gpr 14, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10eb70 5 14 7 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10eb70 0x49 (by decide) 0xfe (by decide) 0xc) pre_rip
  have f424 : InstrSpec 0x10eb75 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x10eb75) (movR64R64Effect 0x10eb75 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10eb75 0 15).toInstrSpec (mov_r64_r64_effect_step 0x10eb75 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f425 : InstrSpec 0x10eb78 [0x48, 0xF7, 0xE6] (fun s => s.RIP = 0x10eb78) (mulR64Effect 0x10eb78 6)
      [.gpr 6, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10eb78 6).toInstrSpec (mul_r64_effect_step 0x10eb78 0x48 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f426 : InstrSpec 0x10eb7b [0x48, 0x89, 0x54, 0x24, 0x30] (StorePre 0x10eb7b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10eb7b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10eb7b 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10eb7b 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10eb7b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f427 : InstrSpec 0x10eb80 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x10eb80 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10eb80 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10eb80 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10eb80 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10eb80 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f428 : InstrSpec 0x10eb85 [0x48, 0x8B, 0x44, 0x24, 0x70] (LoadPre 0x10eb85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10eb85 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10eb85 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10eb85 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x10eb85 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f429 : InstrSpec 0x10eb8a [0x48, 0xF7, 0x64, 0x24, 0x48] (LoadPre 0x10eb8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10eb8a + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10eb8a 5 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10eb8a 5 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mul_m64_effect_step 0x10eb8a 0x48 (by decide) (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f430 : InstrSpec 0x10eb8f [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x10eb8f) (movR64R64Effect 0x10eb8f 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10eb8f 12 2).toInstrSpec (mov_r64_r64_effect_step 0x10eb8f 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f431 : InstrSpec 0x10eb92 [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x10eb92) (movR64R64Effect 0x10eb92 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10eb92 15 0).toInstrSpec (mov_r64_r64_effect_step 0x10eb92 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f432 : InstrSpec 0x10eb95 [0x48, 0x8B, 0x04, 0x24] (LoadPre 0x10eb95 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10eb95 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10eb95 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10eb95 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10eb95 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f433 : InstrSpec 0x10eb99 [0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x10eb99 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10eb99 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10eb99 8 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10eb99 8 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mul_m64_effect_step 0x10eb99 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f434 : InstrSpec 0x10eba1 [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x10eba1) (movR64R64Effect 0x10eba1 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10eba1 13 0).toInstrSpec (mov_r64_r64_effect_step 0x10eba1 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f435 : InstrSpec 0x10eba4 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x10eba4) (movR64R64Effect 0x10eba4 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10eba4 1 2).toInstrSpec (mov_r64_r64_effect_step 0x10eba4 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f436 : InstrSpec 0x10eba7 [0x4C, 0x89, 0xD6] (fun s => s.RIP = 0x10eba7) (movR64R64Effect 0x10eba7 6 10)
      [.gpr 10] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10eba7 6 10).toInstrSpec (mov_r64_r64_effect_step 0x10eba7 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f437 : InstrSpec 0x10ebaa [0x4C, 0x21, 0xD7] (fun s => s.RIP = 0x10ebaa) (andR64R64Effect 0x10ebaa 7 10)
      [.gpr 7, .gpr 10] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ebaa 7 10).toInstrSpec (and_r64_r64_effect_step 0x10ebaa 0x4c 0xd7 (by decide) (by decide)) pre_rip
  have f438 : InstrSpec 0x10ebad [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x10ebad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10ebad + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ebad 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ebad 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x10ebad 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f439 : InstrSpec 0x10ebb2 [0x48, 0xF7, 0x64, 0x24, 0x38] (LoadPre 0x10ebb2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10ebb2 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10ebb2 5 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10ebb2 5 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mul_m64_effect_step 0x10ebb2 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 952) (RestInside.out (n := 952) f420 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 953) (ρ' := [(0, 946), (1, 931), (2, 934), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 952), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb63) f420 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 954) (RestInside.out (n := 954) f421 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 955) (ρ' := [(0, 954), (1, 931), (2, 934), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 952), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb68) f421 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 956) (RestInside.exec (n := 956) (ρ' := [(0, 954), (1, 931), (2, 934), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 952), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb70) f422 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 957) (RestInside.out (n := 957) f423 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 958) (ρ' := [(0, 954), (1, 931), (2, 934), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 957), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb75) f423 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 959) (RestInside.out (n := 959) f424 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 960) (ρ' := [(0, 959), (1, 931), (2, 934), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 957), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb78) f424 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 961) (RestInside.out (n := 961) f425 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 962) f425 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 963) (ρ' := [(0, 961), (1, 931), (2, 962), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 957), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb7b) f425 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 964) (RestInside.exec (n := 964) (ρ' := [(0, 961), (1, 931), (2, 962), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 957), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb80) f426 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 965) (RestInside.exec (n := 965) (ρ' := [(0, 961), (1, 931), (2, 962), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 957), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb85) f427 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 966) (RestInside.out (n := 966) f428 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 967) (ρ' := [(0, 966), (1, 931), (2, 962), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 957), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb8a) f428 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 968) (RestInside.out (n := 968) f429 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 969) f429 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 970) (ρ' := [(0, 968), (1, 931), (2, 969), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 957), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb8f) f429 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 971) (RestInside.out (n := 971) f430 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 972) (ρ' := [(0, 968), (1, 931), (2, 969), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 971), (13, 912), (14, 957), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb92) f430 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 973) (RestInside.out (n := 973) f431 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 974) (ρ' := [(0, 968), (1, 931), (2, 969), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 971), (13, 912), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb95) f431 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 975) (RestInside.out (n := 975) f432 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 976) (ρ' := [(0, 975), (1, 931), (2, 969), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 971), (13, 912), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb99) f432 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 977) (RestInside.out (n := 977) f433 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 978) f433 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 979) (ρ' := [(0, 977), (1, 931), (2, 978), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 971), (13, 912), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eba1) f433 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 980) (RestInside.out (n := 980) f434 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 981) (ρ' := [(0, 977), (1, 931), (2, 978), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eba4) f434 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 982) (RestInside.out (n := 982) f435 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 983) (ρ' := [(0, 977), (1, 982), (2, 978), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eba7) f435 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 984) (RestInside.out (n := 984) f436 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 985) (ρ' := [(0, 977), (1, 982), (2, 978), (3, 890), (4, 65), (5, 760), (6, 984), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebaa) f436 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 986) (RestInside.out (n := 986) f437 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 987) (ρ' := [(0, 977), (1, 982), (2, 978), (3, 890), (4, 65), (5, 760), (6, 984), (7, 986), (8, 927), (9, 863), (10, 892), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebad) f437 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 988) (RestInside.out (n := 988) f438 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 989) (ρ' := [(0, 988), (1, 982), (2, 978), (3, 890), (4, 65), (5, 760), (6, 984), (7, 986), (8, 927), (9, 863), (10, 892), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebb2) f438 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 990) (RestInside.out (n := 990) f439 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 991) f439 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 992) (ρ' := [(0, 990), (1, 982), (2, 991), (3, 890), (4, 65), (5, 760), (6, 984), (7, 986), (8, 927), (9, 863), (10, 892), (11, 894), (12, 971), (13, 980), (14, 957), (15, 973), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ebb7) f439 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_22 code

theorem rest_l10e4c0_20 [Bindings] (code : CodeMap) :
    Rest (n := 905) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 898), (1, 888), (2, 899), (3, 890), (4, 65), (5, 760), (6, 778), (7, 881), (8, 901), (9, 863), (10, 892), (11, 894), (12, 838), (13, 903), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]
      93 0x10eb07 bytes_l10e4c0_20 b_l10e4c0_20 := by
  have f400 : InstrSpec 0x10eb07 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x10eb07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10eb07 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10eb07 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10eb07 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10eb07 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f401 : InstrSpec 0x10eb0c [0x48, 0x8B, 0x74, 0x24, 0x30] (LoadPre 0x10eb0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10eb0c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10eb0c 6 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10eb0c 6 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10eb0c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f402 : InstrSpec 0x10eb11 [0x48, 0xF7, 0xE6] (fun s => s.RIP = 0x10eb11) (mulR64Effect 0x10eb11 6)
      [.gpr 6, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10eb11 6).toInstrSpec (mul_r64_effect_step 0x10eb11 0x48 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f403 : InstrSpec 0x10eb14 [0x49, 0x01, 0xCD] (fun s => s.RIP = 0x10eb14) (addR64R64Effect 0x10eb14 13 1)
      [.gpr 13, .gpr 1] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10eb14 13 1).toInstrSpec (add_r64_r64_effect_step 0x10eb14 0x49 0xcd (by decide) (by decide)) pre_rip
  have f404 : InstrSpec 0x10eb17 [0x49, 0x11, 0xD8] (fun s => s.RIP = 0x10eb17) (atFlags StatusFlags.CF (adcR64R64Effect 0x10eb17 8 3))
      [.gpr 8, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10eb17 8 3).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10eb17 0x49 0xd8 c (by decide) (by decide))) pre_rip
  have f405 : InstrSpec 0x10eb1a [0x4C, 0x01, 0xE8] (fun s => s.RIP = 0x10eb1a) (addR64R64Effect 0x10eb1a 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10eb1a 0 13).toInstrSpec (add_r64_r64_effect_step 0x10eb1a 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f406 : InstrSpec 0x10eb1d [0x49, 0x11, 0xD0] (fun s => s.RIP = 0x10eb1d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10eb1d 8 2))
      [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10eb1d 8 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10eb1d 0x49 0xd0 c (by decide) (by decide))) pre_rip
  have f407 : InstrSpec 0x10eb20 [0x4C, 0x01, 0xE0] (fun s => s.RIP = 0x10eb20) (addR64R64Effect 0x10eb20 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10eb20 0 12).toInstrSpec (add_r64_r64_effect_step 0x10eb20 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f408 : InstrSpec 0x10eb23 [0x49, 0x83, 0xD0, 0x00] (fun s => s.RIP = 0x10eb23) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10eb23 8 0x0))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10eb23 8 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10eb23 0x49 0xd0 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f409 : InstrSpec 0x10eb27 [0x49, 0x0F, 0xA4, 0xC0, 0x0C] (fun s => s.RIP = 0x10eb27) (shldR64R64Effect 0x10eb27 5 8 0 12)
      [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10eb27 5 8 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10eb27 0x49 (by decide) 0xc0 (by decide) 0xc) pre_rip
  have f410 : InstrSpec 0x10eb2c [0x4C, 0x21, 0xD0] (fun s => s.RIP = 0x10eb2c) (andR64R64Effect 0x10eb2c 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10eb2c 0 10).toInstrSpec (and_r64_r64_effect_step 0x10eb2c 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f411 : InstrSpec 0x10eb2f [0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10eb2f) (movR64Imm64Effect 0x10eb2f 1 0x1000003d10)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10eb2f 1 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x10eb2f 0x48 0xb9 (by decide) (by decide) 0x1000003d10) pre_rip
  have f412 : InstrSpec 0x10eb39 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10eb39) (mulR64Effect 0x10eb39 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10eb39 1).toInstrSpec (mul_r64_effect_step 0x10eb39 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f413 : InstrSpec 0x10eb3c [0x48, 0x03, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x10eb3c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10eb3c + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10eb3c 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 7, .gpr 4] [] [.reg 7, .flags, .rip] :=
    (addR64M64Effect_footprint 0x10eb3c 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (add_r64_m64_effect_step 0x10eb3c 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f414 : InstrSpec 0x10eb44 [0x4C, 0x13, 0x74, 0x24, 0x58] (LoadPre 0x10eb44 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10eb44 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10eb44 14 (.sib 4 none 0 (.d8 0x58))))
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10eb44 14 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10eb44 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f415 : InstrSpec 0x10eb49 [0x48, 0x01, 0xC7] (fun s => s.RIP = 0x10eb49) (addR64R64Effect 0x10eb49 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10eb49 7 0).toInstrSpec (add_r64_r64_effect_step 0x10eb49 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f416 : InstrSpec 0x10eb4c [0x49, 0x11, 0xD6] (fun s => s.RIP = 0x10eb4c) (atFlags StatusFlags.CF (adcR64R64Effect 0x10eb4c 14 2))
      [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10eb4c 14 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10eb4c 0x49 0xd6 c (by decide) (by decide))) pre_rip
  have f417 : InstrSpec 0x10eb4f [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x10eb4f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10eb4f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10eb4f 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10eb4f 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10eb4f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f418 : InstrSpec 0x10eb54 [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x10eb54 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10eb54 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10eb54 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10eb54 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x10eb54 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f419 : InstrSpec 0x10eb5c [0x4C, 0x01, 0xCF] (fun s => s.RIP = 0x10eb5c) (addR64R64Effect 0x10eb5c 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10eb5c 7 9).toInstrSpec (add_r64_r64_effect_step 0x10eb5c 0x4c 0xcf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 905) (RestInside.out (n := 905) f400 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 906) (ρ' := [(0, 905), (1, 888), (2, 899), (3, 890), (4, 65), (5, 760), (6, 778), (7, 881), (8, 901), (9, 863), (10, 892), (11, 894), (12, 838), (13, 903), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb0c) f400 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 907) (RestInside.out (n := 907) f401 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 908) (ρ' := [(0, 905), (1, 888), (2, 899), (3, 890), (4, 65), (5, 760), (6, 907), (7, 881), (8, 901), (9, 863), (10, 892), (11, 894), (12, 838), (13, 903), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb11) f401 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 909) (RestInside.out (n := 909) f402 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 910) f402 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 911) (ρ' := [(0, 909), (1, 888), (2, 910), (3, 890), (4, 65), (5, 760), (6, 907), (7, 881), (8, 901), (9, 863), (10, 892), (11, 894), (12, 838), (13, 903), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb14) f402 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 912) (RestInside.out (n := 912) f403 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 913) f403 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 914) (ρ' := [(0, 909), (1, 888), (2, 910), (3, 890), (4, 65), (5, 760), (6, 907), (7, 881), (8, 901), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 879), (15, 865), (16, 913), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb17) f403 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 915) (RestInside.out (n := 915) f404 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 916) (ρ' := [(0, 909), (1, 888), (2, 910), (3, 890), (4, 65), (5, 760), (6, 907), (7, 881), (8, 915), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb1a) f404 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 917) (RestInside.out (n := 917) f405 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 918) f405 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 919) (ρ' := [(0, 917), (1, 888), (2, 910), (3, 890), (4, 65), (5, 760), (6, 907), (7, 881), (8, 915), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 879), (15, 865), (16, 918), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb1d) f405 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 920) (RestInside.out (n := 920) f406 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 921) (ρ' := [(0, 917), (1, 888), (2, 910), (3, 890), (4, 65), (5, 760), (6, 907), (7, 881), (8, 920), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb20) f406 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 922) (RestInside.out (n := 922) f407 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 923) f407 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 924) (ρ' := [(0, 922), (1, 888), (2, 910), (3, 890), (4, 65), (5, 760), (6, 907), (7, 881), (8, 920), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 879), (15, 865), (16, 923), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb23) f407 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 925) (RestInside.out (n := 925) f408 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 926) (ρ' := [(0, 922), (1, 888), (2, 910), (3, 890), (4, 65), (5, 760), (6, 907), (7, 881), (8, 925), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb27) f408 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 927) (RestInside.out (n := 927) f409 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 928) (ρ' := [(0, 922), (1, 888), (2, 910), (3, 890), (4, 65), (5, 760), (6, 907), (7, 881), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb2c) f409 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 929) (RestInside.out (n := 929) f410 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 930) (ρ' := [(0, 929), (1, 888), (2, 910), (3, 890), (4, 65), (5, 760), (6, 907), (7, 881), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb2f) f410 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 931) (RestInside.out (n := 931) f411 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 932) (ρ' := [(0, 929), (1, 931), (2, 910), (3, 890), (4, 65), (5, 760), (6, 907), (7, 881), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb39) f411 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 933) (RestInside.out (n := 933) f412 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 934) f412 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 935) (ρ' := [(0, 933), (1, 931), (2, 934), (3, 890), (4, 65), (5, 760), (6, 907), (7, 881), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb3c) f412 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 936) (RestInside.out (n := 936) f413 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 937) f413 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 938) (ρ' := [(0, 933), (1, 931), (2, 934), (3, 890), (4, 65), (5, 760), (6, 907), (7, 936), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 879), (15, 865), (16, 937), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb44) f413 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 939) (RestInside.out (n := 939) f414 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 940) (ρ' := [(0, 933), (1, 931), (2, 934), (3, 890), (4, 65), (5, 760), (6, 907), (7, 936), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 939), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb49) f414 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 941) (RestInside.out (n := 941) f415 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 942) f415 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 943) (ρ' := [(0, 933), (1, 931), (2, 934), (3, 890), (4, 65), (5, 760), (6, 907), (7, 941), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 939), (15, 865), (16, 942), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb4c) f415 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 944) (RestInside.out (n := 944) f416 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 945) (ρ' := [(0, 933), (1, 931), (2, 934), (3, 890), (4, 65), (5, 760), (6, 907), (7, 941), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 944), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb4f) f416 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 946) (RestInside.out (n := 946) f417 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 947) (ρ' := [(0, 946), (1, 931), (2, 934), (3, 890), (4, 65), (5, 760), (6, 907), (7, 941), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 944), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb54) f417 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 948) (RestInside.exec (n := 948) (ρ' := [(0, 946), (1, 931), (2, 934), (3, 890), (4, 65), (5, 760), (6, 907), (7, 941), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 944), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb5c) f418 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 949) (RestInside.out (n := 949) f419 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 950) f419 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 951) (ρ' := [(0, 946), (1, 931), (2, 934), (3, 890), (4, 65), (5, 760), (6, 907), (7, 949), (8, 927), (9, 863), (10, 892), (11, 894), (12, 838), (13, 912), (14, 944), (15, 865), (16, 950), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb5f) f419 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_21 code

theorem rest_l10e4c0_19 [Bindings] (code : CodeMap) :
    Rest (n := 863) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 850), (1, 848), (2, 851), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 860), (10, 823), (11, 857), (12, 838), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]
      113 0x10eaaf bytes_l10e4c0_19 b_l10e4c0_19 := by
  have f380 : InstrSpec 0x10eaaf [0x4D, 0x0F, 0xA4, 0xD9, 0x0C] (fun s => s.RIP = 0x10eaaf) (shldR64R64Effect 0x10eaaf 5 9 11 12)
      [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10eaaf 5 9 11 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10eaaf 0x4d (by decide) 0xd9 (by decide) 0xc) pre_rip
  have f381 : InstrSpec 0x10eab4 [0x4C, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x10eab4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10eab4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10eab4 15 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10eab4 15 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10eab4 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f382 : InstrSpec 0x10eab9 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x10eab9) (movR64R64Effect 0x10eab9 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10eab9 0 15).toInstrSpec (mov_r64_r64_effect_step 0x10eab9 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f383 : InstrSpec 0x10eabc [0x49, 0xF7, 0xE6] (fun s => s.RIP = 0x10eabc) (mulR64Effect 0x10eabc 14)
      [.gpr 14, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10eabc 14).toInstrSpec (mul_r64_effect_step 0x10eabc 0x49 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f384 : InstrSpec 0x10eabf [0x48, 0x89, 0x54, 0x24, 0x58] (StorePre 0x10eabf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10eabf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10eabf 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10eabf 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x10eabf 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f385 : InstrSpec 0x10eac4 [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x10eac4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10eac4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10eac4 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10eac4 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x10eac4 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f386 : InstrSpec 0x10eacc [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x10eacc) (movR64R64Effect 0x10eacc 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10eacc 0 6).toInstrSpec (mov_r64_r64_effect_step 0x10eacc 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f387 : InstrSpec 0x10eacf [0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x10eacf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10eacf + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10eacf 8 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10eacf 8 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mul_m64_effect_step 0x10eacf 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f388 : InstrSpec 0x10ead7 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x10ead7) (movR64R64Effect 0x10ead7 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10ead7 14 2).toInstrSpec (mov_r64_r64_effect_step 0x10ead7 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f389 : InstrSpec 0x10eada [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x10eada) (movR64R64Effect 0x10eada 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10eada 7 0).toInstrSpec (mov_r64_r64_effect_step 0x10eada 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f390 : InstrSpec 0x10eadd [0x48, 0x8B, 0x04, 0x24] (LoadPre 0x10eadd (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10eadd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10eadd 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10eadd 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10eadd 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f391 : InstrSpec 0x10eae1 [0x48, 0xF7, 0x64, 0x24, 0x38] (LoadPre 0x10eae1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10eae1 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10eae1 5 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10eae1 5 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mul_m64_effect_step 0x10eae1 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f392 : InstrSpec 0x10eae6 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10eae6) (movR64R64Effect 0x10eae6 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10eae6 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10eae6 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f393 : InstrSpec 0x10eae9 [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x10eae9) (movR64R64Effect 0x10eae9 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10eae9 3 2).toInstrSpec (mov_r64_r64_effect_step 0x10eae9 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f394 : InstrSpec 0x10eaec [0x49, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x10eaec) (movR64Imm64Effect 0x10eaec 10 0xfffffffffffff)
      [] [] [.reg 10, .rip] :=
    (movR64Imm64Effect_footprint 0x10eaec 10 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10eaec 0x49 0xba (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f395 : InstrSpec 0x10eaf6 [0x4D, 0x21, 0xD3] (fun s => s.RIP = 0x10eaf6) (andR64R64Effect 0x10eaf6 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10eaf6 11 10).toInstrSpec (and_r64_r64_effect_step 0x10eaf6 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f396 : InstrSpec 0x10eaf9 [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x10eaf9) (movR64R64Effect 0x10eaf9 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10eaf9 0 8).toInstrSpec (mov_r64_r64_effect_step 0x10eaf9 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f397 : InstrSpec 0x10eafc [0x48, 0xF7, 0x64, 0x24, 0x50] (LoadPre 0x10eafc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10eafc + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10eafc 5 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10eafc 5 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mul_m64_effect_step 0x10eafc 0x48 (by decide) (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f398 : InstrSpec 0x10eb01 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x10eb01) (movR64R64Effect 0x10eb01 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10eb01 8 2).toInstrSpec (mov_r64_r64_effect_step 0x10eb01 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f399 : InstrSpec 0x10eb04 [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x10eb04) (movR64R64Effect 0x10eb04 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10eb04 13 0).toInstrSpec (mov_r64_r64_effect_step 0x10eb04 0x49 0xc5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 863) (RestInside.out (n := 863) f380 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 864) (ρ' := [(0, 850), (1, 848), (2, 851), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 863), (10, 823), (11, 857), (12, 838), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eab4) f380 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 865) (RestInside.out (n := 865) f381 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 866) (ρ' := [(0, 850), (1, 848), (2, 851), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 863), (10, 823), (11, 857), (12, 838), (13, 789), (14, 813), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eab9) f381 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 867) (RestInside.out (n := 867) f382 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 868) (ρ' := [(0, 867), (1, 848), (2, 851), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 863), (10, 823), (11, 857), (12, 838), (13, 789), (14, 813), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eabc) f382 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 869) (RestInside.out (n := 869) f383 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 870) f383 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 871) (ρ' := [(0, 869), (1, 848), (2, 870), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 863), (10, 823), (11, 857), (12, 838), (13, 789), (14, 813), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eabf) f383 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 872) (RestInside.exec (n := 872) (ρ' := [(0, 869), (1, 848), (2, 870), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 863), (10, 823), (11, 857), (12, 838), (13, 789), (14, 813), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eac4) f384 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 873) (RestInside.exec (n := 873) (ρ' := [(0, 869), (1, 848), (2, 870), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 863), (10, 823), (11, 857), (12, 838), (13, 789), (14, 813), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eacc) f385 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 874) (RestInside.out (n := 874) f386 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 875) (ρ' := [(0, 874), (1, 848), (2, 870), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 863), (10, 823), (11, 857), (12, 838), (13, 789), (14, 813), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eacf) f386 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 876) (RestInside.out (n := 876) f387 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 877) f387 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 878) (ρ' := [(0, 876), (1, 848), (2, 877), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 863), (10, 823), (11, 857), (12, 838), (13, 789), (14, 813), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ead7) f387 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 879) (RestInside.out (n := 879) f388 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 880) (ρ' := [(0, 876), (1, 848), (2, 877), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 863), (10, 823), (11, 857), (12, 838), (13, 789), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eada) f388 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 881) (RestInside.out (n := 881) f389 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 882) (ρ' := [(0, 876), (1, 848), (2, 877), (3, 807), (4, 65), (5, 760), (6, 778), (7, 881), (8, 800), (9, 863), (10, 823), (11, 857), (12, 838), (13, 789), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eadd) f389 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 883) (RestInside.out (n := 883) f390 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 884) (ρ' := [(0, 883), (1, 848), (2, 877), (3, 807), (4, 65), (5, 760), (6, 778), (7, 881), (8, 800), (9, 863), (10, 823), (11, 857), (12, 838), (13, 789), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eae1) f390 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 885) (RestInside.out (n := 885) f391 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 886) f391 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 887) (ρ' := [(0, 885), (1, 848), (2, 886), (3, 807), (4, 65), (5, 760), (6, 778), (7, 881), (8, 800), (9, 863), (10, 823), (11, 857), (12, 838), (13, 789), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eae6) f391 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 888) (RestInside.out (n := 888) f392 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 889) (ρ' := [(0, 885), (1, 888), (2, 886), (3, 807), (4, 65), (5, 760), (6, 778), (7, 881), (8, 800), (9, 863), (10, 823), (11, 857), (12, 838), (13, 789), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eae9) f392 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 890) (RestInside.out (n := 890) f393 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 891) (ρ' := [(0, 885), (1, 888), (2, 886), (3, 890), (4, 65), (5, 760), (6, 778), (7, 881), (8, 800), (9, 863), (10, 823), (11, 857), (12, 838), (13, 789), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eaec) f393 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 892) (RestInside.out (n := 892) f394 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 893) (ρ' := [(0, 885), (1, 888), (2, 886), (3, 890), (4, 65), (5, 760), (6, 778), (7, 881), (8, 800), (9, 863), (10, 892), (11, 857), (12, 838), (13, 789), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eaf6) f394 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 894) (RestInside.out (n := 894) f395 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 895) (ρ' := [(0, 885), (1, 888), (2, 886), (3, 890), (4, 65), (5, 760), (6, 778), (7, 881), (8, 800), (9, 863), (10, 892), (11, 894), (12, 838), (13, 789), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eaf9) f395 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 896) (RestInside.out (n := 896) f396 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 897) (ρ' := [(0, 896), (1, 888), (2, 886), (3, 890), (4, 65), (5, 760), (6, 778), (7, 881), (8, 800), (9, 863), (10, 892), (11, 894), (12, 838), (13, 789), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eafc) f396 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 898) (RestInside.out (n := 898) f397 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 899) f397 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 900) (ρ' := [(0, 898), (1, 888), (2, 899), (3, 890), (4, 65), (5, 760), (6, 778), (7, 881), (8, 800), (9, 863), (10, 892), (11, 894), (12, 838), (13, 789), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb01) f397 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 901) (RestInside.out (n := 901) f398 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 902) (ρ' := [(0, 898), (1, 888), (2, 899), (3, 890), (4, 65), (5, 760), (6, 778), (7, 881), (8, 901), (9, 863), (10, 892), (11, 894), (12, 838), (13, 789), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb04) f398 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 903) (RestInside.out (n := 903) f399 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 904) (ρ' := [(0, 898), (1, 888), (2, 899), (3, 890), (4, 65), (5, 760), (6, 778), (7, 881), (8, 901), (9, 863), (10, 892), (11, 894), (12, 838), (13, 903), (14, 879), (15, 865), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eb07) f399 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_20 code

theorem rest_l10e4c0_18 [Bindings] (code : CodeMap) :
    Rest (n := 818) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 815), (1, 785), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 798), (11, 765), (12, 796), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]
      133 0x10ea5b bytes_l10e4c0_18 b_l10e4c0_18 := by
  have f360 : InstrSpec 0x10ea5b [0x49, 0x01, 0xCA] (fun s => s.RIP = 0x10ea5b) (addR64R64Effect 0x10ea5b 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10ea5b 10 1).toInstrSpec (add_r64_r64_effect_step 0x10ea5b 0x49 0xca (by decide) (by decide)) pre_rip
  have f361 : InstrSpec 0x10ea5e [0x4D, 0x11, 0xCC] (fun s => s.RIP = 0x10ea5e) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ea5e 12 9))
      [.gpr 12, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10ea5e 12 9).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10ea5e 0x4d 0xcc c (by decide) (by decide))) pre_rip
  have f362 : InstrSpec 0x10ea61 [0x4D, 0x01, 0xFA] (fun s => s.RIP = 0x10ea61) (addR64R64Effect 0x10ea61 10 15)
      [.gpr 10, .gpr 15] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10ea61 10 15).toInstrSpec (add_r64_r64_effect_step 0x10ea61 0x4d 0xfa (by decide) (by decide)) pre_rip
  have f363 : InstrSpec 0x10ea64 [0x49, 0x11, 0xDC] (fun s => s.RIP = 0x10ea64) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ea64 12 3))
      [.gpr 12, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10ea64 12 3).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10ea64 0x49 0xdc c (by decide) (by decide))) pre_rip
  have f364 : InstrSpec 0x10ea67 [0x4C, 0x01, 0xD0] (fun s => s.RIP = 0x10ea67) (addR64R64Effect 0x10ea67 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10ea67 0 10).toInstrSpec (add_r64_r64_effect_step 0x10ea67 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f365 : InstrSpec 0x10ea6a [0x49, 0x11, 0xD4] (fun s => s.RIP = 0x10ea6a) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ea6a 12 2))
      [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10ea6a 12 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10ea6a 0x49 0xd4 c (by decide) (by decide))) pre_rip
  have f366 : InstrSpec 0x10ea6d [0x4C, 0x01, 0xD8] (fun s => s.RIP = 0x10ea6d) (addR64R64Effect 0x10ea6d 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10ea6d 0 11).toInstrSpec (add_r64_r64_effect_step 0x10ea6d 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f367 : InstrSpec 0x10ea70 [0x49, 0x83, 0xD4, 0x00] (fun s => s.RIP = 0x10ea70) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ea70 12 0x0))
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10ea70 12 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10ea70 0x49 0xd4 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f368 : InstrSpec 0x10ea74 [0x49, 0x0F, 0xA4, 0xC4, 0x0C] (fun s => s.RIP = 0x10ea74) (shldR64R64Effect 0x10ea74 5 12 0 12)
      [.gpr 12, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10ea74 5 12 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10ea74 0x49 (by decide) 0xc4 (by decide) 0xc) pre_rip
  have f369 : InstrSpec 0x10ea79 [0x48, 0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x10ea79) (shlR64Effect 0x10ea79 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10ea79 4 0 4).toInstrSpec (shl_r64_imm8_effect_step 0x10ea79 0x48 0xe0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f370 : InstrSpec 0x10ea7d [0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00] (fun s => s.RIP = 0x10ea7d) (movR64Imm64Effect 0x10ea7d 1 0xfffffffffffff0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10ea7d 1 0xfffffffffffff0).toInstrSpec (mov_r64_imm64_effect_step 0x10ea7d 0x48 0xb9 (by decide) (by decide) 0xfffffffffffff0) pre_rip
  have f371 : InstrSpec 0x10ea87 [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x10ea87) (andR64R64Effect 0x10ea87 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ea87 0 1).toInstrSpec (and_r64_r64_effect_step 0x10ea87 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f372 : InstrSpec 0x10ea8a [0x4C, 0x09, 0xE8] (fun s => s.RIP = 0x10ea8a) (orR64R64Effect 0x10ea8a 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10ea8a 0 13).toInstrSpec (or_r64_r64_effect_step 0x10ea8a 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f373 : InstrSpec 0x10ea8d [0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ea8d) (movR64Imm64Effect 0x10ea8d 1 0x1000003d1)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10ea8d 1 0x1000003d1).toInstrSpec (mov_r64_imm64_effect_step 0x10ea8d 0x48 0xb9 (by decide) (by decide) 0x1000003d1) pre_rip
  have f374 : InstrSpec 0x10ea97 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10ea97) (mulR64Effect 0x10ea97 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10ea97 1).toInstrSpec (mul_r64_effect_step 0x10ea97 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f375 : InstrSpec 0x10ea9a [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x10ea9a) (movR64R64Effect 0x10ea9a 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10ea9a 9 2).toInstrSpec (mov_r64_r64_effect_step 0x10ea9a 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f376 : InstrSpec 0x10ea9d [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x10ea9d) (movR64R64Effect 0x10ea9d 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10ea9d 11 0).toInstrSpec (mov_r64_r64_effect_step 0x10ea9d 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f377 : InstrSpec 0x10eaa0 [0x4C, 0x03, 0x5C, 0x24, 0x58] (LoadPre 0x10eaa0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10eaa0 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10eaa0 11 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 11, .gpr 4] [] [.reg 11, .flags, .rip] :=
    (addR64M64Effect_footprint 0x10eaa0 11 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (add_r64_m64_effect_step 0x10eaa0 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f378 : InstrSpec 0x10eaa5 [0x4C, 0x13, 0x4C, 0x24, 0x60] (LoadPre 0x10eaa5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10eaa5 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10eaa5 9 (.sib 4 none 0 (.d8 0x60))))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10eaa5 9 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10eaa5 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f379 : InstrSpec 0x10eaaa [0x48, 0x89, 0x7C, 0x24, 0x60] (StorePre 0x10eaaa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10eaaa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10eaaa 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10eaaa 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x10eaaa 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 818) (RestInside.out (n := 818) f360 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 819) f360 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 820) (ρ' := [(0, 815), (1, 785), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 818), (11, 765), (12, 796), (13, 789), (14, 813), (15, 809), (16, 819), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea5e) f360 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 821) (RestInside.out (n := 821) f361 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 822) (ρ' := [(0, 815), (1, 785), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 818), (11, 765), (12, 821), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea61) f361 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 823) (RestInside.out (n := 823) f362 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 824) f362 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 825) (ρ' := [(0, 815), (1, 785), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 823), (11, 765), (12, 821), (13, 789), (14, 813), (15, 809), (16, 824), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea64) f362 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 826) (RestInside.out (n := 826) f363 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 827) (ρ' := [(0, 815), (1, 785), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 823), (11, 765), (12, 826), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea67) f363 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 828) (RestInside.out (n := 828) f364 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 829) f364 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 830) (ρ' := [(0, 828), (1, 785), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 823), (11, 765), (12, 826), (13, 789), (14, 813), (15, 809), (16, 829), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea6a) f364 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 831) (RestInside.out (n := 831) f365 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 832) (ρ' := [(0, 828), (1, 785), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 823), (11, 765), (12, 831), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea6d) f365 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 833) (RestInside.out (n := 833) f366 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 834) f366 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 835) (ρ' := [(0, 833), (1, 785), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 823), (11, 765), (12, 831), (13, 789), (14, 813), (15, 809), (16, 834), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea70) f366 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 836) (RestInside.out (n := 836) f367 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 837) (ρ' := [(0, 833), (1, 785), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 823), (11, 765), (12, 836), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea74) f367 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 838) (RestInside.out (n := 838) f368 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 839) (ρ' := [(0, 833), (1, 785), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 823), (11, 765), (12, 838), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea79) f368 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 840) (RestInside.out (n := 840) f369 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 841) (ρ' := [(0, 840), (1, 785), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 823), (11, 765), (12, 838), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea7d) f369 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 842) (RestInside.out (n := 842) f370 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 843) (ρ' := [(0, 840), (1, 842), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 823), (11, 765), (12, 838), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea87) f370 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 844) (RestInside.out (n := 844) f371 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 845) (ρ' := [(0, 844), (1, 842), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 823), (11, 765), (12, 838), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea8a) f371 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 846) (RestInside.out (n := 846) f372 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 847) (ρ' := [(0, 846), (1, 842), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 823), (11, 765), (12, 838), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea8d) f372 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 848) (RestInside.out (n := 848) f373 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 849) (ρ' := [(0, 846), (1, 848), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 823), (11, 765), (12, 838), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea97) f373 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 850) (RestInside.out (n := 850) f374 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 851) f374 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 852) (ρ' := [(0, 850), (1, 848), (2, 851), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 823), (11, 765), (12, 838), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea9a) f374 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 853) (RestInside.out (n := 853) f375 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 854) (ρ' := [(0, 850), (1, 848), (2, 851), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 853), (10, 823), (11, 765), (12, 838), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea9d) f375 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 855) (RestInside.out (n := 855) f376 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 856) (ρ' := [(0, 850), (1, 848), (2, 851), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 853), (10, 823), (11, 855), (12, 838), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eaa0) f376 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 857) (RestInside.out (n := 857) f377 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 858) f377 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 859) (ρ' := [(0, 850), (1, 848), (2, 851), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 853), (10, 823), (11, 857), (12, 838), (13, 789), (14, 813), (15, 809), (16, 858), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eaa5) f377 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 860) (RestInside.out (n := 860) f378 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 861) (ρ' := [(0, 850), (1, 848), (2, 851), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 860), (10, 823), (11, 857), (12, 838), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eaaa) f378 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 862) (RestInside.exec (n := 862) (ρ' := [(0, 850), (1, 848), (2, 851), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 860), (10, 823), (11, 857), (12, 838), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eaaf) f379 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10e4c0_19 code

theorem rest_l10e4c0_17 [Bindings] (code : CodeMap) :
    Rest (n := 776) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 773), (1, 724), (2, 774), (3, 726), (4, 65), (5, 760), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 765), (12, 712), (13, 769), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]
      153 0x10ea0d bytes_l10e4c0_17 b_l10e4c0_17 := by
  have f340 : InstrSpec 0x10ea0d [0x48, 0x89, 0x54, 0x24, 0x60] (StorePre 0x10ea0d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10ea0d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ea0d 2 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ea0d 2 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x10ea0d 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f341 : InstrSpec 0x10ea12 [0x48, 0x89, 0x44, 0x24, 0x58] (StorePre 0x10ea12 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10ea12 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ea12 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ea12 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x10ea12 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f342 : InstrSpec 0x10ea17 [0x48, 0x8B, 0x74, 0x24, 0x70] (LoadPre 0x10ea17 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10ea17 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ea17 6 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10ea17 6 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x10ea17 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f343 : InstrSpec 0x10ea1c [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x10ea1c) (movR64R64Effect 0x10ea1c 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10ea1c 0 6).toInstrSpec (mov_r64_r64_effect_step 0x10ea1c 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f344 : InstrSpec 0x10ea1f [0x48, 0xF7, 0x64, 0x24, 0x38] (LoadPre 0x10ea1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10ea1f + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10ea1f 5 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10ea1f 5 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mul_m64_effect_step 0x10ea1f 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f345 : InstrSpec 0x10ea24 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10ea24) (movR64R64Effect 0x10ea24 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10ea24 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10ea24 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f346 : InstrSpec 0x10ea27 [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x10ea27) (movR64R64Effect 0x10ea27 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10ea27 9 2).toInstrSpec (mov_r64_r64_effect_step 0x10ea27 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f347 : InstrSpec 0x10ea2a [0x41, 0x83, 0xE5, 0x0F] (fun s => s.RIP = 0x10ea2a) (andR32Imm8Effect 0x10ea2a 4 13 0xf)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x10ea2a 4 13 0xf).toInstrSpec (and_r32_imm8_rex_effect_step 0x10ea2a 0x41 0xe5 0xf (by decide) (by decide) (by decide)) pre_rip
  have f348 : InstrSpec 0x10ea2e [0x48, 0x8B, 0x04, 0x24] (LoadPre 0x10ea2e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10ea2e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10ea2e 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ea2e 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10ea2e 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f349 : InstrSpec 0x10ea32 [0x48, 0xF7, 0x64, 0x24, 0x50] (LoadPre 0x10ea32 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10ea32 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10ea32 5 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10ea32 5 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mul_m64_effect_step 0x10ea32 0x48 (by decide) (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f350 : InstrSpec 0x10ea37 [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x10ea37) (movR64R64Effect 0x10ea37 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10ea37 12 2).toInstrSpec (mov_r64_r64_effect_step 0x10ea37 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f351 : InstrSpec 0x10ea3a [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x10ea3a) (movR64R64Effect 0x10ea3a 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10ea3a 10 0).toInstrSpec (mov_r64_r64_effect_step 0x10ea3a 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f352 : InstrSpec 0x10ea3d [0x4C, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x10ea3d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10ea3d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ea3d 8 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10ea3d 8 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x10ea3d 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f353 : InstrSpec 0x10ea42 [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x10ea42) (movR64R64Effect 0x10ea42 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10ea42 0 8).toInstrSpec (mov_r64_r64_effect_step 0x10ea42 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f354 : InstrSpec 0x10ea45 [0x48, 0xF7, 0x64, 0x24, 0x30] (LoadPre 0x10ea45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10ea45 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10ea45 5 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10ea45 5 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mul_m64_effect_step 0x10ea45 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f355 : InstrSpec 0x10ea4a [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x10ea4a) (movR64R64Effect 0x10ea4a 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10ea4a 3 2).toInstrSpec (mov_r64_r64_effect_step 0x10ea4a 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f356 : InstrSpec 0x10ea4d [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x10ea4d) (movR64R64Effect 0x10ea4d 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10ea4d 15 0).toInstrSpec (mov_r64_r64_effect_step 0x10ea4d 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f357 : InstrSpec 0x10ea50 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x10ea50) (movR64R64Effect 0x10ea50 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10ea50 0 14).toInstrSpec (mov_r64_r64_effect_step 0x10ea50 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f358 : InstrSpec 0x10ea53 [0x4C, 0x8B, 0x74, 0x24, 0x48] (LoadPre 0x10ea53 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10ea53 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ea53 14 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x10ea53 14 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10ea53 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f359 : InstrSpec 0x10ea58 [0x49, 0xF7, 0xE6] (fun s => s.RIP = 0x10ea58) (mulR64Effect 0x10ea58 14)
      [.gpr 14, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10ea58 14).toInstrSpec (mul_r64_effect_step 0x10ea58 0x49 0xe6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 776) (RestInside.exec (n := 776) (ρ' := [(0, 773), (1, 724), (2, 774), (3, 726), (4, 65), (5, 760), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 765), (12, 712), (13, 769), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea12) f340 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 777) (RestInside.exec (n := 777) (ρ' := [(0, 773), (1, 724), (2, 774), (3, 726), (4, 65), (5, 760), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 765), (12, 712), (13, 769), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea17) f341 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 778) (RestInside.out (n := 778) f342 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 779) (ρ' := [(0, 773), (1, 724), (2, 774), (3, 726), (4, 65), (5, 760), (6, 778), (7, 7), (8, 679), (9, 660), (10, 719), (11, 765), (12, 712), (13, 769), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea1c) f342 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 780) (RestInside.out (n := 780) f343 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 781) (ρ' := [(0, 780), (1, 724), (2, 774), (3, 726), (4, 65), (5, 760), (6, 778), (7, 7), (8, 679), (9, 660), (10, 719), (11, 765), (12, 712), (13, 769), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea1f) f343 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 782) (RestInside.out (n := 782) f344 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 783) f344 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 784) (ρ' := [(0, 782), (1, 724), (2, 783), (3, 726), (4, 65), (5, 760), (6, 778), (7, 7), (8, 679), (9, 660), (10, 719), (11, 765), (12, 712), (13, 769), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea24) f344 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 785) (RestInside.out (n := 785) f345 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 786) (ρ' := [(0, 782), (1, 785), (2, 783), (3, 726), (4, 65), (5, 760), (6, 778), (7, 7), (8, 679), (9, 660), (10, 719), (11, 765), (12, 712), (13, 769), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea27) f345 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 787) (RestInside.out (n := 787) f346 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 788) (ρ' := [(0, 782), (1, 785), (2, 783), (3, 726), (4, 65), (5, 760), (6, 778), (7, 7), (8, 679), (9, 787), (10, 719), (11, 765), (12, 712), (13, 769), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea2a) f346 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 789) (RestInside.out (n := 789) f347 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 790) (ρ' := [(0, 782), (1, 785), (2, 783), (3, 726), (4, 65), (5, 760), (6, 778), (7, 7), (8, 679), (9, 787), (10, 719), (11, 765), (12, 712), (13, 789), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea2e) f347 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 791) (RestInside.out (n := 791) f348 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 792) (ρ' := [(0, 791), (1, 785), (2, 783), (3, 726), (4, 65), (5, 760), (6, 778), (7, 7), (8, 679), (9, 787), (10, 719), (11, 765), (12, 712), (13, 789), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea32) f348 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 793) (RestInside.out (n := 793) f349 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 794) f349 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 795) (ρ' := [(0, 793), (1, 785), (2, 794), (3, 726), (4, 65), (5, 760), (6, 778), (7, 7), (8, 679), (9, 787), (10, 719), (11, 765), (12, 712), (13, 789), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea37) f349 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 796) (RestInside.out (n := 796) f350 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 797) (ρ' := [(0, 793), (1, 785), (2, 794), (3, 726), (4, 65), (5, 760), (6, 778), (7, 7), (8, 679), (9, 787), (10, 719), (11, 765), (12, 796), (13, 789), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea3a) f350 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 798) (RestInside.out (n := 798) f351 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 799) (ρ' := [(0, 793), (1, 785), (2, 794), (3, 726), (4, 65), (5, 760), (6, 778), (7, 7), (8, 679), (9, 787), (10, 798), (11, 765), (12, 796), (13, 789), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea3d) f351 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 800) (RestInside.out (n := 800) f352 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 801) (ρ' := [(0, 793), (1, 785), (2, 794), (3, 726), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 798), (11, 765), (12, 796), (13, 789), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea42) f352 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 802) (RestInside.out (n := 802) f353 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 803) (ρ' := [(0, 802), (1, 785), (2, 794), (3, 726), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 798), (11, 765), (12, 796), (13, 789), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea45) f353 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 804) (RestInside.out (n := 804) f354 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 805) f354 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 806) (ρ' := [(0, 804), (1, 785), (2, 805), (3, 726), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 798), (11, 765), (12, 796), (13, 789), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea4a) f354 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 807) (RestInside.out (n := 807) f355 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 808) (ρ' := [(0, 804), (1, 785), (2, 805), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 798), (11, 765), (12, 796), (13, 789), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea4d) f355 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 809) (RestInside.out (n := 809) f356 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 810) (ρ' := [(0, 804), (1, 785), (2, 805), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 798), (11, 765), (12, 796), (13, 789), (14, 649), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea50) f356 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 811) (RestInside.out (n := 811) f357 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 812) (ρ' := [(0, 811), (1, 785), (2, 805), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 798), (11, 765), (12, 796), (13, 789), (14, 649), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea53) f357 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 813) (RestInside.out (n := 813) f358 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 814) (ρ' := [(0, 811), (1, 785), (2, 805), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 798), (11, 765), (12, 796), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea58) f358 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 815) (RestInside.out (n := 815) f359 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 816) f359 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 817) (ρ' := [(0, 815), (1, 785), (2, 816), (3, 807), (4, 65), (5, 760), (6, 778), (7, 7), (8, 800), (9, 787), (10, 798), (11, 765), (12, 796), (13, 789), (14, 813), (15, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea5b) f359 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_18 code

theorem rest_l10e4c0_16 [Bindings] (code : CodeMap) :
    Rest (n := 728) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 721), (1, 724), (2, 722), (3, 726), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 695), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]
      173 0x10e9bd bytes_l10e4c0_16 b_l10e4c0_16 := by
  have f320 : InstrSpec 0x10e9bd [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x10e9bd) (movR64R64Effect 0x10e9bd 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e9bd 0 9).toInstrSpec (mov_r64_r64_effect_step 0x10e9bd 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f321 : InstrSpec 0x10e9c0 [0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10e9c0) (movR64Imm64Effect 0x10e9c0 2 0x1000003d10)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x10e9c0 2 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x10e9c0 0x48 0xba (by decide) (by decide) 0x1000003d10) pre_rip
  have f322 : InstrSpec 0x10e9ca [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x10e9ca) (mulR64Effect 0x10e9ca 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e9ca 2).toInstrSpec (mul_r64_effect_step 0x10e9ca 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f323 : InstrSpec 0x10e9cd [0x48, 0x03, 0x6C, 0x24, 0x58] (LoadPre 0x10e9cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10e9cd + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10e9cd 5 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 5, .gpr 4] [] [.reg 5, .flags, .rip] :=
    (addR64M64Effect_footprint 0x10e9cd 5 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (add_r64_m64_effect_step 0x10e9cd 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f324 : InstrSpec 0x10e9d2 [0x4C, 0x13, 0x5C, 0x24, 0x60] (LoadPre 0x10e9d2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10e9d2 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e9d2 11 (.sib 4 none 0 (.d8 0x60))))
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10e9d2 11 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10e9d2 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f325 : InstrSpec 0x10e9d7 [0x4C, 0x01, 0xFD] (fun s => s.RIP = 0x10e9d7) (addR64R64Effect 0x10e9d7 5 15)
      [.gpr 5, .gpr 15] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e9d7 5 15).toInstrSpec (add_r64_r64_effect_step 0x10e9d7 0x4c 0xfd (by decide) (by decide)) pre_rip
  have f326 : InstrSpec 0x10e9da [0x4C, 0x13, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x10e9da (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10e9da + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e9da 11 (.sib 4 none 0 (.d32 0x88))))
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10e9da 11 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10e9da 0x4c (by decide) 3 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f327 : InstrSpec 0x10e9e2 [0x4C, 0x01, 0xED] (fun s => s.RIP = 0x10e9e2) (addR64R64Effect 0x10e9e2 5 13)
      [.gpr 5, .gpr 13] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e9e2 5 13).toInstrSpec (add_r64_r64_effect_step 0x10e9e2 0x4c 0xed (by decide) (by decide)) pre_rip
  have f328 : InstrSpec 0x10e9e5 [0x4D, 0x11, 0xE3] (fun s => s.RIP = 0x10e9e5) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e9e5 11 12))
      [.gpr 11, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e9e5 11 12).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e9e5 0x4d 0xe3 c (by decide) (by decide))) pre_rip
  have f329 : InstrSpec 0x10e9e8 [0x48, 0x01, 0xDD] (fun s => s.RIP = 0x10e9e8) (addR64R64Effect 0x10e9e8 5 3)
      [.gpr 5, .gpr 3] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e9e8 5 3).toInstrSpec (add_r64_r64_effect_step 0x10e9e8 0x48 0xdd (by decide) (by decide)) pre_rip
  have f330 : InstrSpec 0x10e9eb [0x49, 0x11, 0xCB] (fun s => s.RIP = 0x10e9eb) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e9eb 11 1))
      [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e9eb 11 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e9eb 0x49 0xcb c (by decide) (by decide))) pre_rip
  have f331 : InstrSpec 0x10e9ee [0x48, 0x01, 0xC5] (fun s => s.RIP = 0x10e9ee) (addR64R64Effect 0x10e9ee 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e9ee 5 0).toInstrSpec (add_r64_r64_effect_step 0x10e9ee 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f332 : InstrSpec 0x10e9f1 [0x49, 0x11, 0xD3] (fun s => s.RIP = 0x10e9f1) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e9f1 11 2))
      [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e9f1 11 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e9f1 0x49 0xd3 c (by decide) (by decide))) pre_rip
  have f333 : InstrSpec 0x10e9f4 [0x4C, 0x01, 0xC5] (fun s => s.RIP = 0x10e9f4) (addR64R64Effect 0x10e9f4 5 8)
      [.gpr 5, .gpr 8] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e9f4 5 8).toInstrSpec (add_r64_r64_effect_step 0x10e9f4 0x4c 0xc5 (by decide) (by decide)) pre_rip
  have f334 : InstrSpec 0x10e9f7 [0x49, 0x83, 0xD3, 0x00] (fun s => s.RIP = 0x10e9f7) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e9f7 11 0x0))
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10e9f7 11 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10e9f7 0x49 0xd3 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f335 : InstrSpec 0x10e9fb [0x49, 0x0F, 0xA4, 0xEB, 0x0C] (fun s => s.RIP = 0x10e9fb) (shldR64R64Effect 0x10e9fb 5 11 5 12)
      [.gpr 11, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e9fb 5 11 5 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e9fb 0x49 (by decide) 0xeb (by decide) 0xc) pre_rip
  have f336 : InstrSpec 0x10ea00 [0x49, 0x89, 0xED] (fun s => s.RIP = 0x10ea00) (movR64R64Effect 0x10ea00 13 5)
      [.gpr 5] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10ea00 13 5).toInstrSpec (mov_r64_r64_effect_step 0x10ea00 0x49 0xed (by decide) (by decide)) pre_rip
  have f337 : InstrSpec 0x10ea03 [0x49, 0xC1, 0xED, 0x30] (fun s => s.RIP = 0x10ea03) (shrR64Effect 0x10ea03 4 13 48)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR64Effect_footprint 0x10ea03 4 13 48).toInstrSpec (shr_r64_imm8_effect_step 0x10ea03 0x49 0xed 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f338 : InstrSpec 0x10ea07 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x10ea07) (movR64R64Effect 0x10ea07 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10ea07 0 6).toInstrSpec (mov_r64_r64_effect_step 0x10ea07 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f339 : InstrSpec 0x10ea0a [0x49, 0xF7, 0xE2] (fun s => s.RIP = 0x10ea0a) (mulR64Effect 0x10ea0a 10)
      [.gpr 10, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10ea0a 10).toInstrSpec (mul_r64_effect_step 0x10ea0a 0x49 0xe2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 728) (RestInside.out (n := 728) f320 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 729) (ρ' := [(0, 728), (1, 724), (2, 722), (3, 726), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 695), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9c0) f320 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 730) (RestInside.out (n := 730) f321 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 731) (ρ' := [(0, 728), (1, 724), (2, 730), (3, 726), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 695), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9ca) f321 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 732) (RestInside.out (n := 732) f322 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 733) f322 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 734) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 695), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9cd) f322 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 735) (RestInside.out (n := 735) f323 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 736) f323 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 737) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 735), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 695), (12, 712), (13, 714), (14, 649), (15, 705), (16, 736), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9d2) f323 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 738) (RestInside.out (n := 738) f324 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 739) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 735), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 738), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9d7) f324 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 740) (RestInside.out (n := 740) f325 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 741) f325 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 742) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 740), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 738), (12, 712), (13, 714), (14, 649), (15, 705), (16, 741), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9da) f325 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 743) (RestInside.out (n := 743) f326 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 744) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 740), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 743), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9e2) f326 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 745) (RestInside.out (n := 745) f327 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 746) f327 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 747) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 745), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 743), (12, 712), (13, 714), (14, 649), (15, 705), (16, 746), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9e5) f327 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 748) (RestInside.out (n := 748) f328 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 749) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 745), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 748), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9e8) f328 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 750) (RestInside.out (n := 750) f329 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 751) f329 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 752) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 750), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 748), (12, 712), (13, 714), (14, 649), (15, 705), (16, 751), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9eb) f329 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 753) (RestInside.out (n := 753) f330 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 754) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 750), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 753), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9ee) f330 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 755) (RestInside.out (n := 755) f331 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 756) f331 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 757) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 755), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 753), (12, 712), (13, 714), (14, 649), (15, 705), (16, 756), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9f1) f331 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 758) (RestInside.out (n := 758) f332 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 759) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 755), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 758), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9f4) f332 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 760) (RestInside.out (n := 760) f333 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 761) f333 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 762) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 760), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 758), (12, 712), (13, 714), (14, 649), (15, 705), (16, 761), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9f7) f333 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 763) (RestInside.out (n := 763) f334 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 764) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 760), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 763), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9fb) f334 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 765) (RestInside.out (n := 765) f335 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 766) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 760), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 765), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea00) f335 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 767) (RestInside.out (n := 767) f336 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 768) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 760), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 765), (12, 712), (13, 767), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea03) f336 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 769) (RestInside.out (n := 769) f337 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 770) (ρ' := [(0, 732), (1, 724), (2, 733), (3, 726), (4, 65), (5, 760), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 765), (12, 712), (13, 769), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea07) f337 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 771) (RestInside.out (n := 771) f338 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 772) (ρ' := [(0, 771), (1, 724), (2, 733), (3, 726), (4, 65), (5, 760), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 765), (12, 712), (13, 769), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea0a) f338 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 773) (RestInside.out (n := 773) f339 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 774) f339 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 775) (ρ' := [(0, 773), (1, 724), (2, 774), (3, 726), (4, 65), (5, 760), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 765), (12, 712), (13, 769), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ea0d) f339 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_17 code

theorem rest_l10e4c0_15 [Bindings] (code : CodeMap) :
    Rest (n := 688) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 685), (1, 653), (2, 686), (3, 584), (4, 65), (5, 596), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]
      193 0x10e970 bytes_l10e4c0_15 b_l10e4c0_15 := by
  have f300 : InstrSpec 0x10e970 [0x48, 0x89, 0x54, 0x24, 0x60] (StorePre 0x10e970 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10e970 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e970 2 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e970 2 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x10e970 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f301 : InstrSpec 0x10e975 [0x48, 0x89, 0x44, 0x24, 0x58] (StorePre 0x10e975 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10e975 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e975 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e975 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x10e975 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f302 : InstrSpec 0x10e97a [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x10e97a) (movR64R64Effect 0x10e97a 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e97a 0 5).toInstrSpec (mov_r64_r64_effect_step 0x10e97a 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f303 : InstrSpec 0x10e97d [0x48, 0xF7, 0xE3] (fun s => s.RIP = 0x10e97d) (mulR64Effect 0x10e97d 3)
      [.gpr 3, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e97d 3).toInstrSpec (mul_r64_effect_step 0x10e97d 0x48 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f304 : InstrSpec 0x10e980 [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x10e980) (movR64R64Effect 0x10e980 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10e980 11 2).toInstrSpec (mov_r64_r64_effect_step 0x10e980 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f305 : InstrSpec 0x10e983 [0x48, 0x89, 0xC5] (fun s => s.RIP = 0x10e983) (movR64R64Effect 0x10e983 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x10e983 5 0).toInstrSpec (mov_r64_r64_effect_step 0x10e983 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f306 : InstrSpec 0x10e986 [0x48, 0x8B, 0x04, 0x24] (LoadPre 0x10e986 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e986 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e986 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e986 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10e986 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f307 : InstrSpec 0x10e98a [0x49, 0xF7, 0xE7] (fun s => s.RIP = 0x10e98a) (mulR64Effect 0x10e98a 15)
      [.gpr 15, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e98a 15).toInstrSpec (mul_r64_effect_step 0x10e98a 0x49 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f308 : InstrSpec 0x10e98d [0x48, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x10e98d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10e98d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10e98d 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e98d 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x10e98d 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f309 : InstrSpec 0x10e995 [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x10e995) (movR64R64Effect 0x10e995 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10e995 15 0).toInstrSpec (mov_r64_r64_effect_step 0x10e995 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f310 : InstrSpec 0x10e998 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x10e998) (movR64R64Effect 0x10e998 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e998 0 13).toInstrSpec (mov_r64_r64_effect_step 0x10e998 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f311 : InstrSpec 0x10e99b [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x10e99b) (mulR64Effect 0x10e99b 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e99b 12).toInstrSpec (mul_r64_effect_step 0x10e99b 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f312 : InstrSpec 0x10e99e [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x10e99e) (movR64R64Effect 0x10e99e 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10e99e 12 2).toInstrSpec (mov_r64_r64_effect_step 0x10e99e 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f313 : InstrSpec 0x10e9a1 [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x10e9a1) (movR64R64Effect 0x10e9a1 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10e9a1 13 0).toInstrSpec (mov_r64_r64_effect_step 0x10e9a1 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f314 : InstrSpec 0x10e9a4 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x10e9a4) (movR64R64Effect 0x10e9a4 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e9a4 0 14).toInstrSpec (mov_r64_r64_effect_step 0x10e9a4 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f315 : InstrSpec 0x10e9a7 [0x4C, 0x89, 0x74, 0x24, 0x40] (StorePre 0x10e9a7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10e9a7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e9a7 14 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e9a7 14 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x10e9a7 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f316 : InstrSpec 0x10e9ac [0x4C, 0x8B, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x10e9ac (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10e9ac + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10e9ac 10 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x10e9ac 10 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x10e9ac 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f317 : InstrSpec 0x10e9b4 [0x49, 0xF7, 0xE2] (fun s => s.RIP = 0x10e9b4) (mulR64Effect 0x10e9b4 10)
      [.gpr 10, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e9b4 10).toInstrSpec (mul_r64_effect_step 0x10e9b4 0x49 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f318 : InstrSpec 0x10e9b7 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x10e9b7) (movR64R64Effect 0x10e9b7 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10e9b7 1 2).toInstrSpec (mov_r64_r64_effect_step 0x10e9b7 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f319 : InstrSpec 0x10e9ba [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x10e9ba) (movR64R64Effect 0x10e9ba 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10e9ba 3 0).toInstrSpec (mov_r64_r64_effect_step 0x10e9ba 0x48 0xc3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 688) (RestInside.exec (n := 688) (ρ' := [(0, 685), (1, 653), (2, 686), (3, 584), (4, 65), (5, 596), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e975) f300 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 689) (RestInside.exec (n := 689) (ρ' := [(0, 685), (1, 653), (2, 686), (3, 584), (4, 65), (5, 596), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e97a) f301 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 690) (RestInside.out (n := 690) f302 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 691) (ρ' := [(0, 690), (1, 653), (2, 686), (3, 584), (4, 65), (5, 596), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e97d) f302 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 692) (RestInside.out (n := 692) f303 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 693) f303 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 694) (ρ' := [(0, 692), (1, 653), (2, 693), (3, 584), (4, 65), (5, 596), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e980) f303 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 695) (RestInside.out (n := 695) f304 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 696) (ρ' := [(0, 692), (1, 653), (2, 693), (3, 584), (4, 65), (5, 596), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 695), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e983) f304 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 697) (RestInside.out (n := 697) f305 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 698) (ρ' := [(0, 692), (1, 653), (2, 693), (3, 584), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 695), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e986) f305 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 699) (RestInside.out (n := 699) f306 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 700) (ρ' := [(0, 699), (1, 653), (2, 693), (3, 584), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 695), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e98a) f306 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 701) (RestInside.out (n := 701) f307 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 702) f307 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 703) (ρ' := [(0, 701), (1, 653), (2, 702), (3, 584), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 695), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e98d) f307 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 704) (RestInside.exec (n := 704) (ρ' := [(0, 701), (1, 653), (2, 702), (3, 584), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 695), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e995) f308 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 705) (RestInside.out (n := 705) f309 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 706) (ρ' := [(0, 701), (1, 653), (2, 702), (3, 584), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 695), (12, 618), (13, 632), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e998) f309 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 707) (RestInside.out (n := 707) f310 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 708) (ρ' := [(0, 707), (1, 653), (2, 702), (3, 584), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 695), (12, 618), (13, 632), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e99b) f310 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 709) (RestInside.out (n := 709) f311 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 710) f311 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 711) (ρ' := [(0, 709), (1, 653), (2, 710), (3, 584), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 695), (12, 618), (13, 632), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e99e) f311 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 712) (RestInside.out (n := 712) f312 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 713) (ρ' := [(0, 709), (1, 653), (2, 710), (3, 584), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 695), (12, 712), (13, 632), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9a1) f312 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 714) (RestInside.out (n := 714) f313 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 715) (ρ' := [(0, 709), (1, 653), (2, 710), (3, 584), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 695), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9a4) f313 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 716) (RestInside.out (n := 716) f314 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 717) (ρ' := [(0, 716), (1, 653), (2, 710), (3, 584), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 695), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9a7) f314 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 718) (RestInside.exec (n := 718) (ρ' := [(0, 716), (1, 653), (2, 710), (3, 584), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 695), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9ac) f315 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 719) (RestInside.out (n := 719) f316 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 720) (ρ' := [(0, 716), (1, 653), (2, 710), (3, 584), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 695), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9b4) f316 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 721) (RestInside.out (n := 721) f317 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 722) f317 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 723) (ρ' := [(0, 721), (1, 653), (2, 722), (3, 584), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 695), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9b7) f317 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 724) (RestInside.out (n := 724) f318 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 725) (ρ' := [(0, 721), (1, 724), (2, 722), (3, 584), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 695), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9ba) f318 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 726) (RestInside.out (n := 726) f319 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 727) (ρ' := [(0, 721), (1, 724), (2, 722), (3, 726), (4, 65), (5, 697), (6, 681), (7, 7), (8, 679), (9, 660), (10, 719), (11, 695), (12, 712), (13, 714), (14, 649), (15, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e9bd) f319 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_16 code

theorem rest_l10e4c0_14 [Bindings] (code : CodeMap) :
    Rest (n := 644) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 637), (1, 630), (2, 638), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 610), (10, 640), (11, 642), (12, 618), (13, 632), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]
      213 0x10e918 bytes_l10e4c0_14 b_l10e4c0_14 := by
  have f280 : InstrSpec 0x10e918 [0x49, 0x01, 0xF3] (fun s => s.RIP = 0x10e918) (addR64R64Effect 0x10e918 11 6)
      [.gpr 11, .gpr 6] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e918 11 6).toInstrSpec (add_r64_r64_effect_step 0x10e918 0x49 0xf3 (by decide) (by decide)) pre_rip
  have f281 : InstrSpec 0x10e91b [0x49, 0x11, 0xCA] (fun s => s.RIP = 0x10e91b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e91b 10 1))
      [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e91b 10 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e91b 0x49 0xca c (by decide) (by decide))) pre_rip
  have f282 : InstrSpec 0x10e91e [0x4D, 0x8B, 0x76, 0x48] (LoadPre 0x10e91e (fun s => AddrMode.addr (.base 14 (.d8 0x48)) s (0x10e91e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e91e 14 (.base 14 (.d8 0x48)))
      [.gpr 14] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x10e91e 14 (.base 14 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10e91e 0x4d (by decide) 6 (.base 14 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f283 : InstrSpec 0x10e922 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x10e922) (movR64R64Effect 0x10e922 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e922 0 14).toInstrSpec (mov_r64_r64_effect_step 0x10e922 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f284 : InstrSpec 0x10e925 [0x48, 0x8B, 0x4C, 0x24, 0x38] (LoadPre 0x10e925 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10e925 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e925 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10e925 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10e925 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f285 : InstrSpec 0x10e92a [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e92a) (mulR64Effect 0x10e92a 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e92a 1).toInstrSpec (mul_r64_effect_step 0x10e92a 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f286 : InstrSpec 0x10e92d [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x10e92d) (movR64R64Effect 0x10e92d 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10e92d 9 2).toInstrSpec (mov_r64_r64_effect_step 0x10e92d 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f287 : InstrSpec 0x10e930 [0x49, 0x0F, 0xA4, 0xC1, 0x0C] (fun s => s.RIP = 0x10e930) (shldR64R64Effect 0x10e930 5 9 0 12)
      [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e930 5 9 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e930 0x49 (by decide) 0xc1 (by decide) 0xc) pre_rip
  have f288 : InstrSpec 0x10e935 [0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x10e935) (movR64Imm64Effect 0x10e935 2 0xfffffffffffff)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x10e935 2 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10e935 0x48 0xba (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f289 : InstrSpec 0x10e93f [0x48, 0x21, 0xD0] (fun s => s.RIP = 0x10e93f) (andR64R64Effect 0x10e93f 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e93f 0 2).toInstrSpec (and_r64_r64_effect_step 0x10e93f 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f290 : InstrSpec 0x10e942 [0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10e942) (movR64Imm64Effect 0x10e942 2 0x1000003d10)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x10e942 2 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x10e942 0x48 0xba (by decide) (by decide) 0x1000003d10) pre_rip
  have f291 : InstrSpec 0x10e94c [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x10e94c) (mulR64Effect 0x10e94c 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e94c 2).toInstrSpec (mul_r64_effect_step 0x10e94c 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f292 : InstrSpec 0x10e94f [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x10e94f) (movR64R64Effect 0x10e94f 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10e94f 8 2).toInstrSpec (mov_r64_r64_effect_step 0x10e94f 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f293 : InstrSpec 0x10e952 [0x4C, 0x01, 0xD8] (fun s => s.RIP = 0x10e952) (addR64R64Effect 0x10e952 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e952 0 11).toInstrSpec (add_r64_r64_effect_step 0x10e952 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f294 : InstrSpec 0x10e955 [0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x10e955 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10e955 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10e955 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e955 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x10e955 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f295 : InstrSpec 0x10e95d [0x4D, 0x11, 0xD0] (fun s => s.RIP = 0x10e95d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e95d 8 10))
      [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e95d 8 10).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e95d 0x4d 0xd0 c (by decide) (by decide))) pre_rip
  have f296 : InstrSpec 0x10e960 [0x49, 0x0F, 0xA4, 0xC0, 0x0C] (fun s => s.RIP = 0x10e960) (shldR64R64Effect 0x10e960 5 8 0 12)
      [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e960 5 8 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e960 0x49 (by decide) 0xc0 (by decide) 0xc) pre_rip
  have f297 : InstrSpec 0x10e965 [0x48, 0x8B, 0x74, 0x24, 0x20] (LoadPre 0x10e965 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e965 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e965 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10e965 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10e965 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f298 : InstrSpec 0x10e96a [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x10e96a) (movR64R64Effect 0x10e96a 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e96a 0 6).toInstrSpec (mov_r64_r64_effect_step 0x10e96a 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f299 : InstrSpec 0x10e96d [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e96d) (mulR64Effect 0x10e96d 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e96d 1).toInstrSpec (mul_r64_effect_step 0x10e96d 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 644) (RestInside.out (n := 644) f280 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 645) f280 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 646) (ρ' := [(0, 637), (1, 630), (2, 638), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 610), (10, 640), (11, 644), (12, 618), (13, 632), (14, 579), (15, 601), (16, 645), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e91b) f280 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 647) (RestInside.out (n := 647) f281 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 648) (ρ' := [(0, 637), (1, 630), (2, 638), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 610), (10, 647), (11, 644), (12, 618), (13, 632), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e91e) f281 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 649) (RestInside.out (n := 649) f282 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 650) (ρ' := [(0, 637), (1, 630), (2, 638), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 610), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e922) f282 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 651) (RestInside.out (n := 651) f283 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 652) (ρ' := [(0, 651), (1, 630), (2, 638), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 610), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e925) f283 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 653) (RestInside.out (n := 653) f284 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 654) (ρ' := [(0, 651), (1, 653), (2, 638), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 610), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e92a) f284 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 655) (RestInside.out (n := 655) f285 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 656) f285 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 657) (ρ' := [(0, 655), (1, 653), (2, 656), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 610), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e92d) f285 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 658) (RestInside.out (n := 658) f286 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 659) (ρ' := [(0, 655), (1, 653), (2, 656), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 658), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e930) f286 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 660) (RestInside.out (n := 660) f287 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 661) (ρ' := [(0, 655), (1, 653), (2, 656), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e935) f287 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 662) (RestInside.out (n := 662) f288 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 663) (ρ' := [(0, 655), (1, 653), (2, 662), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e93f) f288 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 664) (RestInside.out (n := 664) f289 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 665) (ρ' := [(0, 664), (1, 653), (2, 662), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e942) f289 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 666) (RestInside.out (n := 666) f290 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 667) (ρ' := [(0, 664), (1, 653), (2, 666), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e94c) f290 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 668) (RestInside.out (n := 668) f291 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 669) f291 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 670) (ρ' := [(0, 668), (1, 653), (2, 669), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e94f) f291 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 671) (RestInside.out (n := 671) f292 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 672) (ρ' := [(0, 668), (1, 653), (2, 669), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 671), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e952) f292 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 673) (RestInside.out (n := 673) f293 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 674) f293 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 675) (ρ' := [(0, 673), (1, 653), (2, 669), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 671), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (16, 674), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e955) f293 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 676) (RestInside.exec (n := 676) (ρ' := [(0, 673), (1, 653), (2, 669), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 671), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (16, 674), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e95d) f294 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 677) (RestInside.out (n := 677) f295 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 678) (ρ' := [(0, 673), (1, 653), (2, 669), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 677), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e960) f295 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 679) (RestInside.out (n := 679) f296 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 680) (ρ' := [(0, 673), (1, 653), (2, 669), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 679), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e965) f296 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 681) (RestInside.out (n := 681) f297 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 682) (ρ' := [(0, 673), (1, 653), (2, 669), (3, 584), (4, 65), (5, 596), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e96a) f297 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 683) (RestInside.out (n := 683) f298 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 684) (ρ' := [(0, 683), (1, 653), (2, 669), (3, 584), (4, 65), (5, 596), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e96d) f298 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 685) (RestInside.out (n := 685) f299 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 686) f299 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 687) (ρ' := [(0, 685), (1, 653), (2, 686), (3, 584), (4, 65), (5, 596), (6, 681), (7, 7), (8, 679), (9, 660), (10, 647), (11, 644), (12, 618), (13, 632), (14, 649), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e970) f299 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_15 code

theorem rest_l10e4c0_13 [Bindings] (code : CodeMap) :
    Rest (n := 601) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 598), (1, 589), (2, 587), (3, 584), (4, 65), (5, 596), (6, 591), (7, 7), (8, 450), (9, 593), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]
      233 0x10e8ce bytes_l10e4c0_13 b_l10e4c0_13 := by
  have f260 : InstrSpec 0x10e8ce [0x4C, 0x8B, 0x7C, 0x24, 0x30] (LoadPre 0x10e8ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10e8ce + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e8ce 15 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10e8ce 15 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10e8ce 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f261 : InstrSpec 0x10e8d3 [0x49, 0xF7, 0xE7] (fun s => s.RIP = 0x10e8d3) (mulR64Effect 0x10e8d3 15)
      [.gpr 15, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e8d3 15).toInstrSpec (mul_r64_effect_step 0x10e8d3 0x49 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f262 : InstrSpec 0x10e8d6 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x10e8d6) (movR64R64Effect 0x10e8d6 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10e8d6 8 2).toInstrSpec (mov_r64_r64_effect_step 0x10e8d6 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f263 : InstrSpec 0x10e8d9 [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x10e8d9) (movR64R64Effect 0x10e8d9 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10e8d9 9 0).toInstrSpec (mov_r64_r64_effect_step 0x10e8d9 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f264 : InstrSpec 0x10e8dc [0x49, 0x01, 0xC9] (fun s => s.RIP = 0x10e8dc) (addR64R64Effect 0x10e8dc 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e8dc 9 1).toInstrSpec (add_r64_r64_effect_step 0x10e8dc 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f265 : InstrSpec 0x10e8df [0x49, 0x11, 0xF0] (fun s => s.RIP = 0x10e8df) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e8df 8 6))
      [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e8df 8 6).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e8df 0x49 0xf0 c (by decide) (by decide))) pre_rip
  have f266 : InstrSpec 0x10e8e2 [0x49, 0x8B, 0x46, 0x38] (LoadPre 0x10e8e2 (fun s => AddrMode.addr (.base 14 (.d8 0x38)) s (0x10e8e2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e8e2 0 (.base 14 (.d8 0x38)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e8e2 0 (.base 14 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10e8e2 0x49 (by decide) 0 (.base 14 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f267 : InstrSpec 0x10e8e6 [0x48, 0x89, 0x04, 0x24] (StorePre 0x10e8e6 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e8e6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e8e6 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e8e6 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10e8e6 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f268 : InstrSpec 0x10e8ea [0x4C, 0x8B, 0x64, 0x24, 0x48] (LoadPre 0x10e8ea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10e8ea + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e8ea 12 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10e8ea 12 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10e8ea 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f269 : InstrSpec 0x10e8ef [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x10e8ef) (mulR64Effect 0x10e8ef 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e8ef 12).toInstrSpec (mul_r64_effect_step 0x10e8ef 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f270 : InstrSpec 0x10e8f2 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x10e8f2) (movR64R64Effect 0x10e8f2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10e8f2 1 2).toInstrSpec (mov_r64_r64_effect_step 0x10e8f2 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f271 : InstrSpec 0x10e8f5 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x10e8f5) (movR64R64Effect 0x10e8f5 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10e8f5 6 0).toInstrSpec (mov_r64_r64_effect_step 0x10e8f5 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f272 : InstrSpec 0x10e8f8 [0x4C, 0x01, 0xCE] (fun s => s.RIP = 0x10e8f8) (addR64R64Effect 0x10e8f8 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e8f8 6 9).toInstrSpec (add_r64_r64_effect_step 0x10e8f8 0x4c 0xce (by decide) (by decide)) pre_rip
  have f273 : InstrSpec 0x10e8fb [0x4C, 0x11, 0xC1] (fun s => s.RIP = 0x10e8fb) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e8fb 1 8))
      [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e8fb 1 8).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e8fb 0x4c 0xc1 c (by decide) (by decide))) pre_rip
  have f274 : InstrSpec 0x10e8fe [0x4D, 0x8B, 0x6E, 0x40] (LoadPre 0x10e8fe (fun s => AddrMode.addr (.base 14 (.d8 0x40)) s (0x10e8fe + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e8fe 13 (.base 14 (.d8 0x40)))
      [.gpr 14] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x10e8fe 13 (.base 14 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10e8fe 0x4d (by decide) 5 (.base 14 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f275 : InstrSpec 0x10e902 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x10e902) (movR64R64Effect 0x10e902 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e902 0 13).toInstrSpec (mov_r64_r64_effect_step 0x10e902 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f276 : InstrSpec 0x10e905 [0x4C, 0x89, 0x6C, 0x24, 0x68] (StorePre 0x10e905 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10e905 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e905 13 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e905 13 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x10e905 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f277 : InstrSpec 0x10e90a [0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x10e90a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10e90a + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10e90a 8 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10e90a 8 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mul_m64_effect_step 0x10e90a 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f278 : InstrSpec 0x10e912 [0x49, 0x89, 0xD2] (fun s => s.RIP = 0x10e912) (movR64R64Effect 0x10e912 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10e912 10 2).toInstrSpec (mov_r64_r64_effect_step 0x10e912 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f279 : InstrSpec 0x10e915 [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x10e915) (movR64R64Effect 0x10e915 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10e915 11 0).toInstrSpec (mov_r64_r64_effect_step 0x10e915 0x49 0xc3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 601) (RestInside.out (n := 601) f260 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 602) (ρ' := [(0, 598), (1, 589), (2, 587), (3, 584), (4, 65), (5, 596), (6, 591), (7, 7), (8, 450), (9, 593), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8d3) f260 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 603) (RestInside.out (n := 603) f261 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 604) f261 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 605) (ρ' := [(0, 603), (1, 589), (2, 604), (3, 584), (4, 65), (5, 596), (6, 591), (7, 7), (8, 450), (9, 593), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8d6) f261 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 606) (RestInside.out (n := 606) f262 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 607) (ρ' := [(0, 603), (1, 589), (2, 604), (3, 584), (4, 65), (5, 596), (6, 591), (7, 7), (8, 606), (9, 593), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8d9) f262 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 608) (RestInside.out (n := 608) f263 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 609) (ρ' := [(0, 603), (1, 589), (2, 604), (3, 584), (4, 65), (5, 596), (6, 591), (7, 7), (8, 606), (9, 608), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8dc) f263 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 610) (RestInside.out (n := 610) f264 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 611) f264 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 612) (ρ' := [(0, 603), (1, 589), (2, 604), (3, 584), (4, 65), (5, 596), (6, 591), (7, 7), (8, 606), (9, 610), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 601), (16, 611), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8df) f264 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 613) (RestInside.out (n := 613) f265 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 614) (ρ' := [(0, 603), (1, 589), (2, 604), (3, 584), (4, 65), (5, 596), (6, 591), (7, 7), (8, 613), (9, 610), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8e2) f265 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 615) (RestInside.out (n := 615) f266 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 616) (ρ' := [(0, 615), (1, 589), (2, 604), (3, 584), (4, 65), (5, 596), (6, 591), (7, 7), (8, 613), (9, 610), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8e6) f266 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 617) (RestInside.exec (n := 617) (ρ' := [(0, 615), (1, 589), (2, 604), (3, 584), (4, 65), (5, 596), (6, 591), (7, 7), (8, 613), (9, 610), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8ea) f267 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 618) (RestInside.out (n := 618) f268 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 619) (ρ' := [(0, 615), (1, 589), (2, 604), (3, 584), (4, 65), (5, 596), (6, 591), (7, 7), (8, 613), (9, 610), (10, 424), (11, 458), (12, 618), (13, 506), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8ef) f268 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 620) (RestInside.out (n := 620) f269 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 621) f269 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 622) (ρ' := [(0, 620), (1, 589), (2, 621), (3, 584), (4, 65), (5, 596), (6, 591), (7, 7), (8, 613), (9, 610), (10, 424), (11, 458), (12, 618), (13, 506), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8f2) f269 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 623) (RestInside.out (n := 623) f270 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 624) (ρ' := [(0, 620), (1, 623), (2, 621), (3, 584), (4, 65), (5, 596), (6, 591), (7, 7), (8, 613), (9, 610), (10, 424), (11, 458), (12, 618), (13, 506), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8f5) f270 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 625) (RestInside.out (n := 625) f271 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 626) (ρ' := [(0, 620), (1, 623), (2, 621), (3, 584), (4, 65), (5, 596), (6, 625), (7, 7), (8, 613), (9, 610), (10, 424), (11, 458), (12, 618), (13, 506), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8f8) f271 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 627) (RestInside.out (n := 627) f272 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 628) f272 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 629) (ρ' := [(0, 620), (1, 623), (2, 621), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 610), (10, 424), (11, 458), (12, 618), (13, 506), (14, 579), (15, 601), (16, 628), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8fb) f272 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 630) (RestInside.out (n := 630) f273 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 631) (ρ' := [(0, 620), (1, 630), (2, 621), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 610), (10, 424), (11, 458), (12, 618), (13, 506), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8fe) f273 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 632) (RestInside.out (n := 632) f274 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 633) (ρ' := [(0, 620), (1, 630), (2, 621), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 610), (10, 424), (11, 458), (12, 618), (13, 632), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e902) f274 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 634) (RestInside.out (n := 634) f275 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 635) (ρ' := [(0, 634), (1, 630), (2, 621), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 610), (10, 424), (11, 458), (12, 618), (13, 632), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e905) f275 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 636) (RestInside.exec (n := 636) (ρ' := [(0, 634), (1, 630), (2, 621), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 610), (10, 424), (11, 458), (12, 618), (13, 632), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e90a) f276 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 637) (RestInside.out (n := 637) f277 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 638) f277 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 639) (ρ' := [(0, 637), (1, 630), (2, 638), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 610), (10, 424), (11, 458), (12, 618), (13, 632), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e912) f277 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 640) (RestInside.out (n := 640) f278 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 641) (ρ' := [(0, 637), (1, 630), (2, 638), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 610), (10, 640), (11, 458), (12, 618), (13, 632), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e915) f278 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 642) (RestInside.out (n := 642) f279 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 643) (ρ' := [(0, 637), (1, 630), (2, 638), (3, 584), (4, 65), (5, 596), (6, 627), (7, 7), (8, 613), (9, 610), (10, 640), (11, 642), (12, 618), (13, 632), (14, 579), (15, 601), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e918) f279 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_14 code

theorem rest_l10e4c0_12 [Bindings] (code : CodeMap) :
    Rest (n := 564) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 546), (1, 467), (2, 559), (3, 549), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 542), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (16, 562), (22, 22), (39, 39), (50, 50), (51, 51)]
      253 0x10e877 bytes_l10e4c0_12 b_l10e4c0_12 := by
  have f240 : InstrSpec 0x10e877 [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x10e877) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e877 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10e877 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10e877 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f241 : InstrSpec 0x10e87b [0x48, 0x0F, 0xA4, 0xF2, 0x0C] (fun s => s.RIP = 0x10e87b) (shldR64R64Effect 0x10e87b 5 2 6 12)
      [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e87b 5 2 6 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e87b 0x48 (by decide) 0xf2 (by decide) 0xc) pre_rip
  have f242 : InstrSpec 0x10e880 [0x49, 0x89, 0xF1] (fun s => s.RIP = 0x10e880) (movR64R64Effect 0x10e880 9 6)
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10e880 9 6).toInstrSpec (mov_r64_r64_effect_step 0x10e880 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f243 : InstrSpec 0x10e883 [0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x10e883) (movR64Imm64Effect 0x10e883 1 0xffffffffffff)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e883 1 0xffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10e883 0x48 0xb9 (by decide) (by decide) 0xffffffffffff) pre_rip
  have f244 : InstrSpec 0x10e88d [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x10e88d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e88d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e88d 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e88d 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10e88d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f245 : InstrSpec 0x10e892 [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x10e892) (andR64R64Effect 0x10e892 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e892 0 1).toInstrSpec (and_r64_r64_effect_step 0x10e892 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f246 : InstrSpec 0x10e895 [0x48, 0x01, 0xD0] (fun s => s.RIP = 0x10e895) (addR64R64Effect 0x10e895 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e895 0 2).toInstrSpec (add_r64_r64_effect_step 0x10e895 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f247 : InstrSpec 0x10e898 [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x10e898 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e898 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e898 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e898 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10e898 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f248 : InstrSpec 0x10e89d [0x4C, 0x8B, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x10e89d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10e89d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10e89d 14 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x10e89d 14 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x10e89d 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f249 : InstrSpec 0x10e8a5 [0x49, 0x8B, 0x46, 0x28] (LoadPre 0x10e8a5 (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x10e8a5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e8a5 0 (.base 14 (.d8 0x28)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e8a5 0 (.base 14 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10e8a5 0x49 (by decide) 0 (.base 14 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f250 : InstrSpec 0x10e8a9 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x10e8a9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e8a9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e8a9 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e8a9 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10e8a9 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f251 : InstrSpec 0x10e8ae [0x4C, 0x89, 0xFB] (fun s => s.RIP = 0x10e8ae) (movR64R64Effect 0x10e8ae 3 15)
      [.gpr 15] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10e8ae 3 15).toInstrSpec (mov_r64_r64_effect_step 0x10e8ae 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f252 : InstrSpec 0x10e8b1 [0x49, 0xF7, 0xE7] (fun s => s.RIP = 0x10e8b1) (mulR64Effect 0x10e8b1 15)
      [.gpr 15, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e8b1 15).toInstrSpec (mul_r64_effect_step 0x10e8b1 0x49 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f253 : InstrSpec 0x10e8b4 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10e8b4) (movR64R64Effect 0x10e8b4 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10e8b4 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10e8b4 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f254 : InstrSpec 0x10e8b7 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x10e8b7) (movR64R64Effect 0x10e8b7 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10e8b7 6 2).toInstrSpec (mov_r64_r64_effect_step 0x10e8b7 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f255 : InstrSpec 0x10e8ba [0x49, 0x21, 0xE9] (fun s => s.RIP = 0x10e8ba) (andR64R64Effect 0x10e8ba 9 5)
      [.gpr 9, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e8ba 9 5).toInstrSpec (and_r64_r64_effect_step 0x10e8ba 0x49 0xe9 (by decide) (by decide)) pre_rip
  have f256 : InstrSpec 0x10e8bd [0x4C, 0x89, 0x4C, 0x24, 0x78] (StorePre 0x10e8bd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10e8bd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e8bd 9 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e8bd 9 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x10e8bd 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f257 : InstrSpec 0x10e8c2 [0x49, 0x8B, 0x6E, 0x30] (LoadPre 0x10e8c2 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x10e8c2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e8c2 5 (.base 14 (.d8 0x30)))
      [.gpr 14] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10e8c2 5 (.base 14 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10e8c2 0x49 (by decide) 5 (.base 14 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f258 : InstrSpec 0x10e8c6 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x10e8c6) (movR64R64Effect 0x10e8c6 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e8c6 0 5).toInstrSpec (mov_r64_r64_effect_step 0x10e8c6 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f259 : InstrSpec 0x10e8c9 [0x48, 0x89, 0x6C, 0x24, 0x70] (StorePre 0x10e8c9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10e8c9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e8c9 5 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e8c9 5 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x10e8c9 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 564) (RestInside.out (n := 564) f240 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 565) (ρ' := [(0, 546), (1, 467), (2, 564), (3, 549), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 542), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e87b) f240 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 566) (RestInside.out (n := 566) f241 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 567) (ρ' := [(0, 546), (1, 467), (2, 566), (3, 549), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 542), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e880) f241 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 568) (RestInside.out (n := 568) f242 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 569) (ρ' := [(0, 546), (1, 467), (2, 566), (3, 549), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 568), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e883) f242 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 570) (RestInside.out (n := 570) f243 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 571) (ρ' := [(0, 546), (1, 570), (2, 566), (3, 549), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 568), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e88d) f243 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 572) (RestInside.out (n := 572) f244 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 573) (ρ' := [(0, 572), (1, 570), (2, 566), (3, 549), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 568), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e892) f244 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 574) (RestInside.out (n := 574) f245 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 575) (ρ' := [(0, 574), (1, 570), (2, 566), (3, 549), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 568), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e895) f245 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 576) (RestInside.out (n := 576) f246 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 577) (ρ' := [(0, 576), (1, 570), (2, 566), (3, 549), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 568), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e898) f246 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 578) (RestInside.exec (n := 578) (ρ' := [(0, 576), (1, 570), (2, 566), (3, 549), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 568), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e89d) f247 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 579) (RestInside.out (n := 579) f248 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 580) (ρ' := [(0, 576), (1, 570), (2, 566), (3, 549), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 568), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8a5) f248 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 581) (RestInside.out (n := 581) f249 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 582) (ρ' := [(0, 581), (1, 570), (2, 566), (3, 549), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 568), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8a9) f249 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 583) (RestInside.exec (n := 583) (ρ' := [(0, 581), (1, 570), (2, 566), (3, 549), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 568), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8ae) f250 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 584) (RestInside.out (n := 584) f251 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 585) (ρ' := [(0, 581), (1, 570), (2, 566), (3, 584), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 568), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8b1) f251 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 586) (RestInside.out (n := 586) f252 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 587) f252 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 588) (ρ' := [(0, 586), (1, 570), (2, 587), (3, 584), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 568), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8b4) f252 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 589) (RestInside.out (n := 589) f253 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 590) (ρ' := [(0, 586), (1, 589), (2, 587), (3, 584), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 568), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8b7) f253 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 591) (RestInside.out (n := 591) f254 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 592) (ρ' := [(0, 586), (1, 589), (2, 587), (3, 584), (4, 65), (5, 478), (6, 591), (7, 7), (8, 450), (9, 568), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8ba) f254 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 593) (RestInside.out (n := 593) f255 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 594) (ρ' := [(0, 586), (1, 589), (2, 587), (3, 584), (4, 65), (5, 478), (6, 591), (7, 7), (8, 450), (9, 593), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8bd) f255 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 595) (RestInside.exec (n := 595) (ρ' := [(0, 586), (1, 589), (2, 587), (3, 584), (4, 65), (5, 478), (6, 591), (7, 7), (8, 450), (9, 593), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8c2) f256 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 596) (RestInside.out (n := 596) f257 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 597) (ρ' := [(0, 586), (1, 589), (2, 587), (3, 584), (4, 65), (5, 596), (6, 591), (7, 7), (8, 450), (9, 593), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8c6) f257 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 598) (RestInside.out (n := 598) f258 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 599) (ρ' := [(0, 598), (1, 589), (2, 587), (3, 584), (4, 65), (5, 596), (6, 591), (7, 7), (8, 450), (9, 593), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8c9) f258 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 600) (RestInside.exec (n := 600) (ρ' := [(0, 598), (1, 589), (2, 587), (3, 584), (4, 65), (5, 596), (6, 591), (7, 7), (8, 450), (9, 593), (10, 424), (11, 458), (12, 465), (13, 506), (14, 579), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e8ce) f259 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10e4c0_13 code

theorem rest_l10e4c0_11 [Bindings] (code : CodeMap) :
    Rest (n := 517) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 513), (1, 467), (2, 497), (3, 474), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 506), (14, 509), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]
      273 0x10e830 bytes_l10e4c0_11 b_l10e4c0_11 := by
  have f220 : InstrSpec 0x10e830 [0x48, 0xF7, 0xE6] (fun s => s.RIP = 0x10e830) (mulR64Effect 0x10e830 6)
      [.gpr 6, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e830 6).toInstrSpec (mul_r64_effect_step 0x10e830 0x48 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f221 : InstrSpec 0x10e833 [0x48, 0x01, 0xCB] (fun s => s.RIP = 0x10e833) (addR64R64Effect 0x10e833 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e833 3 1).toInstrSpec (add_r64_r64_effect_step 0x10e833 0x48 0xcb (by decide) (by decide)) pre_rip
  have f222 : InstrSpec 0x10e836 [0x4D, 0x11, 0xE1] (fun s => s.RIP = 0x10e836) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e836 9 12))
      [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e836 9 12).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e836 0x4d 0xe1 c (by decide) (by decide))) pre_rip
  have f223 : InstrSpec 0x10e839 [0x4C, 0x01, 0xDB] (fun s => s.RIP = 0x10e839) (addR64R64Effect 0x10e839 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e839 3 11).toInstrSpec (add_r64_r64_effect_step 0x10e839 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f224 : InstrSpec 0x10e83c [0x4C, 0x13, 0x0C, 0x24] (LoadPre 0x10e83c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e83c + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e83c 9 (.sib 4 none 0 .none)))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10e83c 9 (.sib 4 none 0 .none)).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10e83c 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f225 : InstrSpec 0x10e840 [0x48, 0x01, 0xC3] (fun s => s.RIP = 0x10e840) (addR64R64Effect 0x10e840 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e840 3 0).toInstrSpec (add_r64_r64_effect_step 0x10e840 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f226 : InstrSpec 0x10e843 [0x49, 0x11, 0xD1] (fun s => s.RIP = 0x10e843) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e843 9 2))
      [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e843 9 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e843 0x49 0xd1 c (by decide) (by decide))) pre_rip
  have f227 : InstrSpec 0x10e846 [0x4C, 0x01, 0xC3] (fun s => s.RIP = 0x10e846) (addR64R64Effect 0x10e846 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e846 3 8).toInstrSpec (add_r64_r64_effect_step 0x10e846 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f228 : InstrSpec 0x10e849 [0x49, 0x83, 0xD1, 0x00] (fun s => s.RIP = 0x10e849) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e849 9 0x0))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10e849 9 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10e849 0x49 0xd1 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f229 : InstrSpec 0x10e84d [0x4D, 0x0F, 0xA4, 0xEE, 0x0C] (fun s => s.RIP = 0x10e84d) (shldR64R64Effect 0x10e84d 5 14 13 12)
      [.gpr 14, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e84d 5 14 13 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e84d 0x4d (by decide) 0xee (by decide) 0xc) pre_rip
  have f230 : InstrSpec 0x10e852 [0x49, 0x0F, 0xA4, 0xD9, 0x0C] (fun s => s.RIP = 0x10e852) (shldR64R64Effect 0x10e852 5 9 3 12)
      [.gpr 9, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e852 5 9 3 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e852 0x49 (by decide) 0xd9 (by decide) 0xc) pre_rip
  have f231 : InstrSpec 0x10e857 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x10e857) (movR64R64Effect 0x10e857 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e857 0 14).toInstrSpec (mov_r64_r64_effect_step 0x10e857 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f232 : InstrSpec 0x10e85a [0x48, 0xF7, 0xE6] (fun s => s.RIP = 0x10e85a) (mulR64Effect 0x10e85a 6)
      [.gpr 6, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e85a 6).toInstrSpec (mul_r64_effect_step 0x10e85a 0x48 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f233 : InstrSpec 0x10e85d [0x48, 0x21, 0xEB] (fun s => s.RIP = 0x10e85d) (andR64R64Effect 0x10e85d 3 5)
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e85d 3 5).toInstrSpec (and_r64_r64_effect_step 0x10e85d 0x48 0xeb (by decide) (by decide)) pre_rip
  have f234 : InstrSpec 0x10e860 [0x48, 0x89, 0x5C, 0x24, 0x08] (StorePre 0x10e860 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e860 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e860 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e860 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10e860 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f235 : InstrSpec 0x10e865 [0x48, 0x8B, 0x74, 0x24, 0x78] (LoadPre 0x10e865 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10e865 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e865 6 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10e865 6 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x10e865 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f236 : InstrSpec 0x10e86a [0x48, 0x21, 0xEE] (fun s => s.RIP = 0x10e86a) (andR64R64Effect 0x10e86a 6 5)
      [.gpr 6, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e86a 6 5).toInstrSpec (and_r64_r64_effect_step 0x10e86a 0x48 0xee (by decide) (by decide)) pre_rip
  have f237 : InstrSpec 0x10e86d [0x48, 0x01, 0xC6] (fun s => s.RIP = 0x10e86d) (addR64R64Effect 0x10e86d 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e86d 6 0).toInstrSpec (add_r64_r64_effect_step 0x10e86d 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f238 : InstrSpec 0x10e870 [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x10e870) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e870 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10e870 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10e870 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f239 : InstrSpec 0x10e874 [0x4C, 0x01, 0xCE] (fun s => s.RIP = 0x10e874) (addR64R64Effect 0x10e874 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e874 6 9).toInstrSpec (add_r64_r64_effect_step 0x10e874 0x4c 0xce (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 517) (RestInside.out (n := 517) f220 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 518) f220 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 519) (ρ' := [(0, 517), (1, 467), (2, 518), (3, 474), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 506), (14, 509), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e833) f220 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 520) (RestInside.out (n := 520) f221 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 521) f221 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 522) (ρ' := [(0, 517), (1, 467), (2, 518), (3, 520), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 506), (14, 509), (15, 492), (16, 521), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e836) f221 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 523) (RestInside.out (n := 523) f222 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 524) (ρ' := [(0, 517), (1, 467), (2, 518), (3, 520), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 523), (10, 424), (11, 458), (12, 465), (13, 506), (14, 509), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e839) f222 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 525) (RestInside.out (n := 525) f223 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 526) f223 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 527) (ρ' := [(0, 517), (1, 467), (2, 518), (3, 525), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 523), (10, 424), (11, 458), (12, 465), (13, 506), (14, 509), (15, 492), (16, 526), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e83c) f223 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 528) (RestInside.out (n := 528) f224 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 529) (ρ' := [(0, 517), (1, 467), (2, 518), (3, 525), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 528), (10, 424), (11, 458), (12, 465), (13, 506), (14, 509), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e840) f224 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 530) (RestInside.out (n := 530) f225 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 531) f225 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 532) (ρ' := [(0, 517), (1, 467), (2, 518), (3, 530), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 528), (10, 424), (11, 458), (12, 465), (13, 506), (14, 509), (15, 492), (16, 531), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e843) f225 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 533) (RestInside.out (n := 533) f226 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 534) (ρ' := [(0, 517), (1, 467), (2, 518), (3, 530), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 533), (10, 424), (11, 458), (12, 465), (13, 506), (14, 509), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e846) f226 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 535) (RestInside.out (n := 535) f227 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 536) f227 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 537) (ρ' := [(0, 517), (1, 467), (2, 518), (3, 535), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 533), (10, 424), (11, 458), (12, 465), (13, 506), (14, 509), (15, 492), (16, 536), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e849) f227 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 538) (RestInside.out (n := 538) f228 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 539) (ρ' := [(0, 517), (1, 467), (2, 518), (3, 535), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 538), (10, 424), (11, 458), (12, 465), (13, 506), (14, 509), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e84d) f228 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 540) (RestInside.out (n := 540) f229 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 541) (ρ' := [(0, 517), (1, 467), (2, 518), (3, 535), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 538), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e852) f229 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 542) (RestInside.out (n := 542) f230 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 543) (ρ' := [(0, 517), (1, 467), (2, 518), (3, 535), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 542), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e857) f230 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 544) (RestInside.out (n := 544) f231 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 545) (ρ' := [(0, 544), (1, 467), (2, 518), (3, 535), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 542), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e85a) f231 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 546) (RestInside.out (n := 546) f232 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 547) f232 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 548) (ρ' := [(0, 546), (1, 467), (2, 547), (3, 535), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 542), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e85d) f232 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 549) (RestInside.out (n := 549) f233 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 550) (ρ' := [(0, 546), (1, 467), (2, 547), (3, 549), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 542), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e860) f233 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 551) (RestInside.exec (n := 551) (ρ' := [(0, 546), (1, 467), (2, 547), (3, 549), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 542), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e865) f234 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 552) (RestInside.out (n := 552) f235 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 553) (ρ' := [(0, 546), (1, 467), (2, 547), (3, 549), (4, 65), (5, 478), (6, 552), (7, 7), (8, 450), (9, 542), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e86a) f235 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 554) (RestInside.out (n := 554) f236 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 555) (ρ' := [(0, 546), (1, 467), (2, 547), (3, 549), (4, 65), (5, 478), (6, 554), (7, 7), (8, 450), (9, 542), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e86d) f236 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 556) (RestInside.out (n := 556) f237 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 557) f237 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 558) (ρ' := [(0, 546), (1, 467), (2, 547), (3, 549), (4, 65), (5, 478), (6, 556), (7, 7), (8, 450), (9, 542), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (16, 557), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e870) f237 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 559) (RestInside.out (n := 559) f238 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 560) (ρ' := [(0, 546), (1, 467), (2, 559), (3, 549), (4, 65), (5, 478), (6, 556), (7, 7), (8, 450), (9, 542), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e874) f238 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 561) (RestInside.out (n := 561) f239 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 562) f239 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 563) (ρ' := [(0, 546), (1, 467), (2, 559), (3, 549), (4, 65), (5, 478), (6, 561), (7, 7), (8, 450), (9, 542), (10, 424), (11, 458), (12, 465), (13, 506), (14, 540), (15, 492), (16, 562), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e877) f239 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_12 code

theorem rest_l10e4c0_10 [Bindings] (code : CodeMap) :
    Rest (n := 474) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 471), (1, 467), (2, 472), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 450), (9, 333), (10, 424), (11, 458), (12, 465), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]
      293 0x10e7e4 bytes_l10e4c0_10 b_l10e4c0_10 := by
  have f200 : InstrSpec 0x10e7e4 [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x10e7e4) (movR64R64Effect 0x10e7e4 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10e7e4 3 0).toInstrSpec (mov_r64_r64_effect_step 0x10e7e4 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f201 : InstrSpec 0x10e7e7 [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x10e7e7) (movR64R64Effect 0x10e7e7 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10e7e7 9 2).toInstrSpec (mov_r64_r64_effect_step 0x10e7e7 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f202 : InstrSpec 0x10e7ea [0x48, 0x89, 0xF5] (fun s => s.RIP = 0x10e7ea) (movR64R64Effect 0x10e7ea 5 6)
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x10e7ea 5 6).toInstrSpec (mov_r64_r64_effect_step 0x10e7ea 0x48 0xf5 (by decide) (by decide)) pre_rip
  have f203 : InstrSpec 0x10e7ed [0x49, 0x21, 0xF5] (fun s => s.RIP = 0x10e7ed) (andR64R64Effect 0x10e7ed 13 6)
      [.gpr 13, .gpr 6] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e7ed 13 6).toInstrSpec (and_r64_r64_effect_step 0x10e7ed 0x49 0xf5 (by decide) (by decide)) pre_rip
  have f204 : InstrSpec 0x10e7f0 [0x4C, 0x89, 0x6C, 0x24, 0x10] (StorePre 0x10e7f0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e7f0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e7f0 13 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e7f0 13 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10e7f0 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f205 : InstrSpec 0x10e7f5 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x10e7f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10e7f5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e7f5 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e7f5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10e7f5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f206 : InstrSpec 0x10e7fa [0x49, 0xF7, 0xE6] (fun s => s.RIP = 0x10e7fa) (mulR64Effect 0x10e7fa 14)
      [.gpr 14, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e7fa 14).toInstrSpec (mul_r64_effect_step 0x10e7fa 0x49 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f207 : InstrSpec 0x10e7fd [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x10e7fd) (movR64R64Effect 0x10e7fd 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10e7fd 14 2).toInstrSpec (mov_r64_r64_effect_step 0x10e7fd 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f208 : InstrSpec 0x10e800 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x10e800) (movR64R64Effect 0x10e800 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10e800 6 0).toInstrSpec (mov_r64_r64_effect_step 0x10e800 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f209 : InstrSpec 0x10e803 [0x4C, 0x8B, 0x7C, 0x24, 0x50] (LoadPre 0x10e803 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10e803 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e803 15 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10e803 15 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10e803 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f210 : InstrSpec 0x10e808 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x10e808) (movR64R64Effect 0x10e808 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e808 0 15).toInstrSpec (mov_r64_r64_effect_step 0x10e808 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f211 : InstrSpec 0x10e80b [0x48, 0xF7, 0x64, 0x24, 0x40] (LoadPre 0x10e80b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10e80b + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10e80b 5 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10e80b 5 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mul_m64_effect_step 0x10e80b 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f212 : InstrSpec 0x10e810 [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x10e810) (movR64R64Effect 0x10e810 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10e810 13 0).toInstrSpec (mov_r64_r64_effect_step 0x10e810 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f213 : InstrSpec 0x10e813 [0x49, 0x01, 0xF5] (fun s => s.RIP = 0x10e813) (addR64R64Effect 0x10e813 13 6)
      [.gpr 13, .gpr 6] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e813 13 6).toInstrSpec (add_r64_r64_effect_step 0x10e813 0x49 0xf5 (by decide) (by decide)) pre_rip
  have f214 : InstrSpec 0x10e816 [0x49, 0x11, 0xD6] (fun s => s.RIP = 0x10e816) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e816 14 2))
      [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e816 14 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e816 0x49 0xd6 c (by decide) (by decide))) pre_rip
  have f215 : InstrSpec 0x10e819 [0x4D, 0x01, 0xD5] (fun s => s.RIP = 0x10e819) (addR64R64Effect 0x10e819 13 10)
      [.gpr 13, .gpr 10] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e819 13 10).toInstrSpec (add_r64_r64_effect_step 0x10e819 0x4d 0xd5 (by decide) (by decide)) pre_rip
  have f216 : InstrSpec 0x10e81c [0x49, 0x83, 0xD6, 0x00] (fun s => s.RIP = 0x10e81c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e81c 14 0x0))
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10e81c 14 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10e81c 0x49 0xd6 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f217 : InstrSpec 0x10e820 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x10e820) (movR64R64Effect 0x10e820 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e820 0 13).toInstrSpec (mov_r64_r64_effect_step 0x10e820 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f218 : InstrSpec 0x10e823 [0x48, 0x21, 0xE8] (fun s => s.RIP = 0x10e823) (andR64R64Effect 0x10e823 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e823 0 5).toInstrSpec (and_r64_r64_effect_step 0x10e823 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f219 : InstrSpec 0x10e826 [0x48, 0xBE, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10e826) (movR64Imm64Effect 0x10e826 6 0x1000003d10)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x10e826 6 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x10e826 0x48 0xbe (by decide) (by decide) 0x1000003d10) pre_rip
  refine Rest.ofInside (n := 474) (RestInside.out (n := 474) f200 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 475) (ρ' := [(0, 471), (1, 467), (2, 472), (3, 474), (4, 65), (5, 265), (6, 426), (7, 7), (8, 450), (9, 333), (10, 424), (11, 458), (12, 465), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7e7) f200 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 476) (RestInside.out (n := 476) f201 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 477) (ρ' := [(0, 471), (1, 467), (2, 472), (3, 474), (4, 65), (5, 265), (6, 426), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7ea) f201 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 478) (RestInside.out (n := 478) f202 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 479) (ρ' := [(0, 471), (1, 467), (2, 472), (3, 474), (4, 65), (5, 478), (6, 426), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7ed) f202 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 480) (RestInside.out (n := 480) f203 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 481) (ρ' := [(0, 471), (1, 467), (2, 472), (3, 474), (4, 65), (5, 478), (6, 426), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 480), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7f0) f203 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 482) (RestInside.exec (n := 482) (ρ' := [(0, 471), (1, 467), (2, 472), (3, 474), (4, 65), (5, 478), (6, 426), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 480), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7f5) f204 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 483) (RestInside.out (n := 483) f205 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 484) (ρ' := [(0, 483), (1, 467), (2, 472), (3, 474), (4, 65), (5, 478), (6, 426), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 480), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7fa) f205 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 485) (RestInside.out (n := 485) f206 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 486) f206 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 487) (ρ' := [(0, 485), (1, 467), (2, 486), (3, 474), (4, 65), (5, 478), (6, 426), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 480), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7fd) f206 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 488) (RestInside.out (n := 488) f207 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 489) (ρ' := [(0, 485), (1, 467), (2, 486), (3, 474), (4, 65), (5, 478), (6, 426), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 480), (14, 488), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e800) f207 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 490) (RestInside.out (n := 490) f208 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 491) (ρ' := [(0, 485), (1, 467), (2, 486), (3, 474), (4, 65), (5, 478), (6, 490), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 480), (14, 488), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e803) f208 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 492) (RestInside.out (n := 492) f209 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 493) (ρ' := [(0, 485), (1, 467), (2, 486), (3, 474), (4, 65), (5, 478), (6, 490), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 480), (14, 488), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e808) f209 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 494) (RestInside.out (n := 494) f210 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 495) (ρ' := [(0, 494), (1, 467), (2, 486), (3, 474), (4, 65), (5, 478), (6, 490), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 480), (14, 488), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e80b) f210 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 496) (RestInside.out (n := 496) f211 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 497) f211 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 498) (ρ' := [(0, 496), (1, 467), (2, 497), (3, 474), (4, 65), (5, 478), (6, 490), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 480), (14, 488), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e810) f211 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 499) (RestInside.out (n := 499) f212 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 500) (ρ' := [(0, 496), (1, 467), (2, 497), (3, 474), (4, 65), (5, 478), (6, 490), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 499), (14, 488), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e813) f212 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 501) (RestInside.out (n := 501) f213 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 502) f213 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 503) (ρ' := [(0, 496), (1, 467), (2, 497), (3, 474), (4, 65), (5, 478), (6, 490), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 501), (14, 488), (15, 492), (16, 502), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e816) f213 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 504) (RestInside.out (n := 504) f214 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 505) (ρ' := [(0, 496), (1, 467), (2, 497), (3, 474), (4, 65), (5, 478), (6, 490), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 501), (14, 504), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e819) f214 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 506) (RestInside.out (n := 506) f215 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 507) f215 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 508) (ρ' := [(0, 496), (1, 467), (2, 497), (3, 474), (4, 65), (5, 478), (6, 490), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 506), (14, 504), (15, 492), (16, 507), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e81c) f215 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 509) (RestInside.out (n := 509) f216 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 510) (ρ' := [(0, 496), (1, 467), (2, 497), (3, 474), (4, 65), (5, 478), (6, 490), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 506), (14, 509), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e820) f216 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 511) (RestInside.out (n := 511) f217 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 512) (ρ' := [(0, 511), (1, 467), (2, 497), (3, 474), (4, 65), (5, 478), (6, 490), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 506), (14, 509), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e823) f217 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 513) (RestInside.out (n := 513) f218 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 514) (ρ' := [(0, 513), (1, 467), (2, 497), (3, 474), (4, 65), (5, 478), (6, 490), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 506), (14, 509), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e826) f218 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 515) (RestInside.out (n := 515) f219 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 516) (ρ' := [(0, 513), (1, 467), (2, 497), (3, 474), (4, 65), (5, 478), (6, 515), (7, 7), (8, 450), (9, 476), (10, 424), (11, 458), (12, 465), (13, 506), (14, 509), (15, 492), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e830) f219 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_11 code

theorem rest_l10e4c0_9 [Bindings] (code : CodeMap) :
    Rest (n := 428) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 419), (1, 382), (2, 407), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 371), (9, 333), (10, 424), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]
      313 0x10e794 bytes_l10e4c0_9 b_l10e4c0_9 := by
  have f180 : InstrSpec 0x10e794 [0x48, 0x21, 0xF0] (fun s => s.RIP = 0x10e794) (andR64R64Effect 0x10e794 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e794 0 6).toInstrSpec (and_r64_r64_effect_step 0x10e794 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f181 : InstrSpec 0x10e797 [0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10e797) (movR64Imm64Effect 0x10e797 1 0x1000003d10)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e797 1 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x10e797 0x48 0xb9 (by decide) (by decide) 0x1000003d10) pre_rip
  have f182 : InstrSpec 0x10e7a1 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e7a1) (mulR64Effect 0x10e7a1 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e7a1 1).toInstrSpec (mul_r64_effect_step 0x10e7a1 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f183 : InstrSpec 0x10e7a4 [0x4C, 0x03, 0x6C, 0x24, 0x08] (LoadPre 0x10e7a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e7a4 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10e7a4 13 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 13, .gpr 4] [] [.reg 13, .flags, .rip] :=
    (addR64M64Effect_footprint 0x10e7a4 13 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (add_r64_m64_effect_step 0x10e7a4 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f184 : InstrSpec 0x10e7a9 [0x4C, 0x13, 0x44, 0x24, 0x10] (LoadPre 0x10e7a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e7a9 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e7a9 8 (.sib 4 none 0 (.d8 0x10))))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10e7a9 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10e7a9 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f185 : InstrSpec 0x10e7ae [0x49, 0x01, 0xC5] (fun s => s.RIP = 0x10e7ae) (addR64R64Effect 0x10e7ae 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e7ae 13 0).toInstrSpec (add_r64_r64_effect_step 0x10e7ae 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f186 : InstrSpec 0x10e7b1 [0x49, 0x11, 0xD0] (fun s => s.RIP = 0x10e7b1) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e7b1 8 2))
      [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e7b1 8 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e7b1 0x49 0xd0 c (by decide) (by decide))) pre_rip
  have f187 : InstrSpec 0x10e7b4 [0x4D, 0x01, 0xDD] (fun s => s.RIP = 0x10e7b4) (addR64R64Effect 0x10e7b4 13 11)
      [.gpr 13, .gpr 11] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e7b4 13 11).toInstrSpec (add_r64_r64_effect_step 0x10e7b4 0x4d 0xdd (by decide) (by decide)) pre_rip
  have f188 : InstrSpec 0x10e7b7 [0x49, 0x83, 0xD0, 0x00] (fun s => s.RIP = 0x10e7b7) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e7b7 8 0x0))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10e7b7 8 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10e7b7 0x49 0xd0 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f189 : InstrSpec 0x10e7bb [0x4D, 0x0F, 0xA4, 0xE8, 0x0C] (fun s => s.RIP = 0x10e7bb) (shldR64R64Effect 0x10e7bb 5 8 13 12)
      [.gpr 8, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e7bb 5 8 13 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e7bb 0x4d (by decide) 0xe8 (by decide) 0xc) pre_rip
  have f190 : InstrSpec 0x10e7c0 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10e7c0) (movR64R64Effect 0x10e7c0 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e7c0 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10e7c0 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f191 : InstrSpec 0x10e7c3 [0x48, 0xF7, 0x24, 0x24] (LoadPre 0x10e7c3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e7c3 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x10e7c3 4 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10e7c3 4 (.sib 4 none 0 .none)).toInstrSpec (mul_m64_effect_step 0x10e7c3 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f192 : InstrSpec 0x10e7c7 [0x48, 0x89, 0x14, 0x24] (StorePre 0x10e7c7 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e7c7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e7c7 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e7c7 2 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10e7c7 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f193 : InstrSpec 0x10e7cb [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x10e7cb) (movR64R64Effect 0x10e7cb 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10e7cb 11 0).toInstrSpec (mov_r64_r64_effect_step 0x10e7cb 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f194 : InstrSpec 0x10e7ce [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x10e7ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10e7ce + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e7ce 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e7ce 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10e7ce 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f195 : InstrSpec 0x10e7d3 [0x48, 0xF7, 0x64, 0x24, 0x20] (LoadPre 0x10e7d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e7d3 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10e7d3 5 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10e7d3 5 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mul_m64_effect_step 0x10e7d3 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f196 : InstrSpec 0x10e7d8 [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x10e7d8) (movR64R64Effect 0x10e7d8 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10e7d8 12 2).toInstrSpec (mov_r64_r64_effect_step 0x10e7d8 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f197 : InstrSpec 0x10e7db [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10e7db) (movR64R64Effect 0x10e7db 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10e7db 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10e7db 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f198 : InstrSpec 0x10e7de [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x10e7de) (movR64R64Effect 0x10e7de 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e7de 0 5).toInstrSpec (mov_r64_r64_effect_step 0x10e7de 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f199 : InstrSpec 0x10e7e1 [0x49, 0xF7, 0xE7] (fun s => s.RIP = 0x10e7e1) (mulR64Effect 0x10e7e1 15)
      [.gpr 15, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e7e1 15).toInstrSpec (mul_r64_effect_step 0x10e7e1 0x49 0xe7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 428) (RestInside.out (n := 428) f180 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 429) (ρ' := [(0, 428), (1, 382), (2, 407), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 371), (9, 333), (10, 424), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e797) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 430) (RestInside.out (n := 430) f181 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 431) (ρ' := [(0, 428), (1, 430), (2, 407), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 371), (9, 333), (10, 424), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7a1) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 432) (RestInside.out (n := 432) f182 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 433) f182 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 434) (ρ' := [(0, 432), (1, 430), (2, 433), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 371), (9, 333), (10, 424), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7a4) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 435) (RestInside.out (n := 435) f183 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 436) f183 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 437) (ρ' := [(0, 432), (1, 430), (2, 433), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 371), (9, 333), (10, 424), (11, 355), (12, 400), (13, 435), (14, 393), (15, 377), (16, 436), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7a9) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 438) (RestInside.out (n := 438) f184 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 439) (ρ' := [(0, 432), (1, 430), (2, 433), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 438), (9, 333), (10, 424), (11, 355), (12, 400), (13, 435), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7ae) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 440) (RestInside.out (n := 440) f185 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 441) f185 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 442) (ρ' := [(0, 432), (1, 430), (2, 433), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 438), (9, 333), (10, 424), (11, 355), (12, 400), (13, 440), (14, 393), (15, 377), (16, 441), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7b1) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 443) (RestInside.out (n := 443) f186 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 444) (ρ' := [(0, 432), (1, 430), (2, 433), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 443), (9, 333), (10, 424), (11, 355), (12, 400), (13, 440), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7b4) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 445) (RestInside.out (n := 445) f187 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 446) f187 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 447) (ρ' := [(0, 432), (1, 430), (2, 433), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 443), (9, 333), (10, 424), (11, 355), (12, 400), (13, 445), (14, 393), (15, 377), (16, 446), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7b7) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 448) (RestInside.out (n := 448) f188 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 449) (ρ' := [(0, 432), (1, 430), (2, 433), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 448), (9, 333), (10, 424), (11, 355), (12, 400), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7bb) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 450) (RestInside.out (n := 450) f189 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 451) (ρ' := [(0, 432), (1, 430), (2, 433), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 450), (9, 333), (10, 424), (11, 355), (12, 400), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7c0) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 452) (RestInside.out (n := 452) f190 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 453) (ρ' := [(0, 452), (1, 430), (2, 433), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 450), (9, 333), (10, 424), (11, 355), (12, 400), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7c3) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 454) (RestInside.out (n := 454) f191 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 455) f191 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 456) (ρ' := [(0, 454), (1, 430), (2, 455), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 450), (9, 333), (10, 424), (11, 355), (12, 400), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7c7) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 457) (RestInside.exec (n := 457) (ρ' := [(0, 454), (1, 430), (2, 455), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 450), (9, 333), (10, 424), (11, 355), (12, 400), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7cb) f192 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 458) (RestInside.out (n := 458) f193 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 459) (ρ' := [(0, 454), (1, 430), (2, 455), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 450), (9, 333), (10, 424), (11, 458), (12, 400), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7ce) f193 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 460) (RestInside.out (n := 460) f194 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 461) (ρ' := [(0, 460), (1, 430), (2, 455), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 450), (9, 333), (10, 424), (11, 458), (12, 400), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7d3) f194 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 462) (RestInside.out (n := 462) f195 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 463) f195 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 464) (ρ' := [(0, 462), (1, 430), (2, 463), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 450), (9, 333), (10, 424), (11, 458), (12, 400), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7d8) f195 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 465) (RestInside.out (n := 465) f196 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 466) (ρ' := [(0, 462), (1, 430), (2, 463), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 450), (9, 333), (10, 424), (11, 458), (12, 465), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7db) f196 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 467) (RestInside.out (n := 467) f197 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 468) (ρ' := [(0, 462), (1, 467), (2, 463), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 450), (9, 333), (10, 424), (11, 458), (12, 465), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7de) f197 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 469) (RestInside.out (n := 469) f198 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 470) (ρ' := [(0, 469), (1, 467), (2, 463), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 450), (9, 333), (10, 424), (11, 458), (12, 465), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7e1) f198 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 471) (RestInside.out (n := 471) f199 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 472) f199 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 473) (ρ' := [(0, 471), (1, 467), (2, 472), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 450), (9, 333), (10, 424), (11, 458), (12, 465), (13, 445), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e7e4) f199 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_10 code

theorem rest_l10e4c0_8 [Bindings] (code : CodeMap) :
    Rest (n := 384) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 379), (1, 382), (2, 380), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 371), (9, 333), (10, 357), (11, 355), (12, 304), (13, 373), (14, 284), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]
      333 0x10e73f bytes_l10e4c0_8 b_l10e4c0_8 := by
  have f160 : InstrSpec 0x10e73f [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x10e73f) (movR64R64Effect 0x10e73f 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10e73f 6 2).toInstrSpec (mov_r64_r64_effect_step 0x10e73f 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f161 : InstrSpec 0x10e742 [0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x10e742) (movR64Imm64Effect 0x10e742 0 0xfffffffffffff)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x10e742 0 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10e742 0x48 0xb8 (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f162 : InstrSpec 0x10e74c [0x49, 0x21, 0xC2] (fun s => s.RIP = 0x10e74c) (andR64R64Effect 0x10e74c 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e74c 10 0).toInstrSpec (and_r64_r64_effect_step 0x10e74c 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f163 : InstrSpec 0x10e74f [0x4C, 0x89, 0x54, 0x24, 0x18] (StorePre 0x10e74f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e74f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e74f 10 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e74f 10 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10e74f 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f164 : InstrSpec 0x10e754 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x10e754) (movR64R64Effect 0x10e754 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e754 0 14).toInstrSpec (mov_r64_r64_effect_step 0x10e754 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f165 : InstrSpec 0x10e757 [0x4C, 0x8B, 0x74, 0x24, 0x70] (LoadPre 0x10e757 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10e757 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e757 14 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x10e757 14 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x10e757 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f166 : InstrSpec 0x10e75c [0x49, 0xF7, 0xE6] (fun s => s.RIP = 0x10e75c) (mulR64Effect 0x10e75c 14)
      [.gpr 14, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e75c 14).toInstrSpec (mul_r64_effect_step 0x10e75c 0x49 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f167 : InstrSpec 0x10e75f [0x49, 0x89, 0xD2] (fun s => s.RIP = 0x10e75f) (movR64R64Effect 0x10e75f 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10e75f 10 2).toInstrSpec (mov_r64_r64_effect_step 0x10e75f 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f168 : InstrSpec 0x10e762 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x10e762) (movR64R64Effect 0x10e762 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10e762 12 0).toInstrSpec (mov_r64_r64_effect_step 0x10e762 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f169 : InstrSpec 0x10e765 [0x48, 0x8B, 0x5C, 0x24, 0x30] (LoadPre 0x10e765 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10e765 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e765 3 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10e765 3 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10e765 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f170 : InstrSpec 0x10e76a [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10e76a) (movR64R64Effect 0x10e76a 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e76a 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10e76a 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f171 : InstrSpec 0x10e76d [0x48, 0xF7, 0x64, 0x24, 0x40] (LoadPre 0x10e76d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10e76d + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10e76d 5 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10e76d 5 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mul_m64_effect_step 0x10e76d 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f172 : InstrSpec 0x10e772 [0x4C, 0x01, 0xE0] (fun s => s.RIP = 0x10e772) (addR64R64Effect 0x10e772 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e772 0 12).toInstrSpec (add_r64_r64_effect_step 0x10e772 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f173 : InstrSpec 0x10e775 [0x49, 0x11, 0xD2] (fun s => s.RIP = 0x10e775) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e775 10 2))
      [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e775 10 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e775 0x49 0xd2 c (by decide) (by decide))) pre_rip
  have f174 : InstrSpec 0x10e778 [0x48, 0x01, 0xC8] (fun s => s.RIP = 0x10e778) (addR64R64Effect 0x10e778 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e778 0 1).toInstrSpec (add_r64_r64_effect_step 0x10e778 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f175 : InstrSpec 0x10e77b [0x49, 0x11, 0xF2] (fun s => s.RIP = 0x10e77b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e77b 10 6))
      [.gpr 10, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e77b 10 6).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e77b 0x49 0xf2 c (by decide) (by decide))) pre_rip
  have f176 : InstrSpec 0x10e77e [0x4C, 0x01, 0xC8] (fun s => s.RIP = 0x10e77e) (addR64R64Effect 0x10e77e 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e77e 0 9).toInstrSpec (add_r64_r64_effect_step 0x10e77e 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f177 : InstrSpec 0x10e781 [0x49, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x10e781) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e781 10 0x0))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10e781 10 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10e781 0x49 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f178 : InstrSpec 0x10e785 [0x49, 0x0F, 0xA4, 0xC2, 0x0C] (fun s => s.RIP = 0x10e785) (shldR64R64Effect 0x10e785 5 10 0 12)
      [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e785 5 10 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e785 0x49 (by decide) 0xc2 (by decide) 0xc) pre_rip
  have f179 : InstrSpec 0x10e78a [0x48, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x10e78a) (movR64Imm64Effect 0x10e78a 6 0xfffffffffffff)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x10e78a 6 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10e78a 0x48 0xbe (by decide) (by decide) 0xfffffffffffff) pre_rip
  refine Rest.ofInside (n := 384) (RestInside.out (n := 384) f160 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 385) (ρ' := [(0, 379), (1, 382), (2, 380), (3, 295), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 357), (11, 355), (12, 304), (13, 373), (14, 284), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e742) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 386) (RestInside.out (n := 386) f161 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 387) (ρ' := [(0, 386), (1, 382), (2, 380), (3, 295), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 357), (11, 355), (12, 304), (13, 373), (14, 284), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e74c) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 388) (RestInside.out (n := 388) f162 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 389) (ρ' := [(0, 386), (1, 382), (2, 380), (3, 295), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 388), (11, 355), (12, 304), (13, 373), (14, 284), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e74f) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 390) (RestInside.exec (n := 390) (ρ' := [(0, 386), (1, 382), (2, 380), (3, 295), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 388), (11, 355), (12, 304), (13, 373), (14, 284), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e754) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 391) (RestInside.out (n := 391) f164 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 392) (ρ' := [(0, 391), (1, 382), (2, 380), (3, 295), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 388), (11, 355), (12, 304), (13, 373), (14, 284), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e757) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 393) (RestInside.out (n := 393) f165 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 394) (ρ' := [(0, 391), (1, 382), (2, 380), (3, 295), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 388), (11, 355), (12, 304), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e75c) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 395) (RestInside.out (n := 395) f166 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 396) f166 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 397) (ρ' := [(0, 395), (1, 382), (2, 396), (3, 295), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 388), (11, 355), (12, 304), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e75f) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 398) (RestInside.out (n := 398) f167 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 399) (ρ' := [(0, 395), (1, 382), (2, 396), (3, 295), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 398), (11, 355), (12, 304), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e762) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 400) (RestInside.out (n := 400) f168 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 401) (ρ' := [(0, 395), (1, 382), (2, 396), (3, 295), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 398), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e765) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 402) (RestInside.out (n := 402) f169 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 403) (ρ' := [(0, 395), (1, 382), (2, 396), (3, 402), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 398), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e76a) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 404) (RestInside.out (n := 404) f170 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 405) (ρ' := [(0, 404), (1, 382), (2, 396), (3, 402), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 398), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e76d) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 406) (RestInside.out (n := 406) f171 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 407) f171 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 408) (ρ' := [(0, 406), (1, 382), (2, 407), (3, 402), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 398), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e772) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 409) (RestInside.out (n := 409) f172 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 410) f172 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 411) (ρ' := [(0, 409), (1, 382), (2, 407), (3, 402), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 398), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (16, 410), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e775) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 412) (RestInside.out (n := 412) f173 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 413) (ρ' := [(0, 409), (1, 382), (2, 407), (3, 402), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 412), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e778) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 414) (RestInside.out (n := 414) f174 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 415) f174 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 416) (ρ' := [(0, 414), (1, 382), (2, 407), (3, 402), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 412), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (16, 415), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e77b) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 417) (RestInside.out (n := 417) f175 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 418) (ρ' := [(0, 414), (1, 382), (2, 407), (3, 402), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 417), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e77e) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 419) (RestInside.out (n := 419) f176 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 420) f176 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 421) (ρ' := [(0, 419), (1, 382), (2, 407), (3, 402), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 417), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (16, 420), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e781) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 422) (RestInside.out (n := 422) f177 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 423) (ρ' := [(0, 419), (1, 382), (2, 407), (3, 402), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 422), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e785) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 424) (RestInside.out (n := 424) f178 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 425) (ρ' := [(0, 419), (1, 382), (2, 407), (3, 402), (4, 65), (5, 265), (6, 384), (7, 7), (8, 371), (9, 333), (10, 424), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e78a) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 426) (RestInside.out (n := 426) f179 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 427) (ρ' := [(0, 419), (1, 382), (2, 407), (3, 402), (4, 65), (5, 265), (6, 426), (7, 7), (8, 371), (9, 333), (10, 424), (11, 355), (12, 400), (13, 373), (14, 393), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e794) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_9 code

theorem rest_l10e4c0_7 [Bindings] (code : CodeMap) :
    Rest (n := 341) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 339), (1, 337), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]
      353 0x10e6ed bytes_l10e4c0_7 b_l10e4c0_7 := by
  have f140 : InstrSpec 0x10e6ed [0x48, 0x09, 0xD8] (fun s => s.RIP = 0x10e6ed) (orR64R64Effect 0x10e6ed 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10e6ed 0 3).toInstrSpec (or_r64_r64_effect_step 0x10e6ed 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f141 : InstrSpec 0x10e6f0 [0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10e6f0) (movR64Imm64Effect 0x10e6f0 1 0x1000003d1)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e6f0 1 0x1000003d1).toInstrSpec (mov_r64_imm64_effect_step 0x10e6f0 0x48 0xb9 (by decide) (by decide) 0x1000003d1) pre_rip
  have f142 : InstrSpec 0x10e6fa [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e6fa) (mulR64Effect 0x10e6fa 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e6fa 1).toInstrSpec (mul_r64_effect_step 0x10e6fa 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f143 : InstrSpec 0x10e6fd [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x10e6fd) (movR64R64Effect 0x10e6fd 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10e6fd 11 2).toInstrSpec (mov_r64_r64_effect_step 0x10e6fd 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f144 : InstrSpec 0x10e700 [0x48, 0x03, 0x44, 0x24, 0x10] (LoadPre 0x10e700 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e700 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10e700 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (addR64M64Effect_footprint 0x10e700 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (add_r64_m64_effect_step 0x10e700 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f145 : InstrSpec 0x10e705 [0x4C, 0x13, 0x5C, 0x24, 0x18] (LoadPre 0x10e705 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e705 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e705 11 (.sib 4 none 0 (.d8 0x18))))
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10e705 11 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10e705 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f146 : InstrSpec 0x10e70a [0x49, 0x0F, 0xA4, 0xC3, 0x0C] (fun s => s.RIP = 0x10e70a) (shldR64R64Effect 0x10e70a 5 11 0 12)
      [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e70a 5 11 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e70a 0x49 (by decide) 0xc3 (by decide) 0xc) pre_rip
  have f147 : InstrSpec 0x10e70f [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x10e70f) (movR64R64Effect 0x10e70f 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10e70f 10 0).toInstrSpec (mov_r64_r64_effect_step 0x10e70f 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f148 : InstrSpec 0x10e712 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x10e712) (movR64R64Effect 0x10e712 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e712 0 13).toInstrSpec (mov_r64_r64_effect_step 0x10e712 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f149 : InstrSpec 0x10e715 [0x48, 0xF7, 0x24, 0x24] (LoadPre 0x10e715 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e715 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x10e715 4 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10e715 4 (.sib 4 none 0 .none)).toInstrSpec (mul_m64_effect_step 0x10e715 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f150 : InstrSpec 0x10e719 [0x48, 0x89, 0x54, 0x24, 0x10] (StorePre 0x10e719 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e719 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e719 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e719 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10e719 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f151 : InstrSpec 0x10e71e [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x10e71e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e71e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e71e 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e71e 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10e71e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f152 : InstrSpec 0x10e723 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x10e723) (movR64R64Effect 0x10e723 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e723 0 5).toInstrSpec (mov_r64_r64_effect_step 0x10e723 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f153 : InstrSpec 0x10e726 [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x10e726) (mulR64Effect 0x10e726 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e726 8).toInstrSpec (mul_r64_effect_step 0x10e726 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f154 : InstrSpec 0x10e729 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x10e729) (movR64R64Effect 0x10e729 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10e729 8 2).toInstrSpec (mov_r64_r64_effect_step 0x10e729 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f155 : InstrSpec 0x10e72c [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x10e72c) (movR64R64Effect 0x10e72c 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10e72c 13 0).toInstrSpec (mov_r64_r64_effect_step 0x10e72c 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f156 : InstrSpec 0x10e72f [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x10e72f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10e72f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e72f 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e72f 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10e72f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f157 : InstrSpec 0x10e734 [0x4C, 0x8B, 0x7C, 0x24, 0x68] (LoadPre 0x10e734 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10e734 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e734 15 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10e734 15 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x10e734 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f158 : InstrSpec 0x10e739 [0x49, 0xF7, 0xE7] (fun s => s.RIP = 0x10e739) (mulR64Effect 0x10e739 15)
      [.gpr 15, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e739 15).toInstrSpec (mul_r64_effect_step 0x10e739 0x49 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f159 : InstrSpec 0x10e73c [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10e73c) (movR64R64Effect 0x10e73c 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10e73c 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10e73c 0x48 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 341) (RestInside.out (n := 341) f140 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 342) (ρ' := [(0, 341), (1, 337), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6f0) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 343) (RestInside.out (n := 343) f141 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 344) (ρ' := [(0, 341), (1, 343), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6fa) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 345) (RestInside.out (n := 345) f142 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 346) f142 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 347) (ρ' := [(0, 345), (1, 343), (2, 346), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6fd) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 348) (RestInside.out (n := 348) f143 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 349) (ρ' := [(0, 345), (1, 343), (2, 346), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 261), (11, 348), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e700) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 350) (RestInside.out (n := 350) f144 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 351) f144 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 352) (ρ' := [(0, 350), (1, 343), (2, 346), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 261), (11, 348), (12, 304), (13, 306), (14, 284), (15, 293), (16, 351), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e705) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 353) (RestInside.out (n := 353) f145 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 354) (ρ' := [(0, 350), (1, 343), (2, 346), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 261), (11, 353), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e70a) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 355) (RestInside.out (n := 355) f146 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 356) (ρ' := [(0, 350), (1, 343), (2, 346), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 261), (11, 355), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e70f) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 357) (RestInside.out (n := 357) f147 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 358) (ρ' := [(0, 350), (1, 343), (2, 346), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 357), (11, 355), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e712) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 359) (RestInside.out (n := 359) f148 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 360) (ρ' := [(0, 359), (1, 343), (2, 346), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 357), (11, 355), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e715) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 361) (RestInside.out (n := 361) f149 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 362) f149 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 363) (ρ' := [(0, 361), (1, 343), (2, 362), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 357), (11, 355), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e719) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 364) (RestInside.exec (n := 364) (ρ' := [(0, 361), (1, 343), (2, 362), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 357), (11, 355), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e71e) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 365) (RestInside.exec (n := 365) (ρ' := [(0, 361), (1, 343), (2, 362), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 357), (11, 355), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e723) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 366) (RestInside.out (n := 366) f152 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 367) (ρ' := [(0, 366), (1, 343), (2, 362), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 357), (11, 355), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e726) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 368) (RestInside.out (n := 368) f153 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 369) f153 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 370) (ρ' := [(0, 368), (1, 343), (2, 369), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 357), (11, 355), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e729) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 371) (RestInside.out (n := 371) f154 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 372) (ρ' := [(0, 368), (1, 343), (2, 369), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 371), (9, 333), (10, 357), (11, 355), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e72c) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 373) (RestInside.out (n := 373) f155 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 374) (ρ' := [(0, 368), (1, 343), (2, 369), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 371), (9, 333), (10, 357), (11, 355), (12, 304), (13, 373), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e72f) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 375) (RestInside.out (n := 375) f156 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 376) (ρ' := [(0, 375), (1, 343), (2, 369), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 371), (9, 333), (10, 357), (11, 355), (12, 304), (13, 373), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e734) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 377) (RestInside.out (n := 377) f157 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 378) (ρ' := [(0, 375), (1, 343), (2, 369), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 371), (9, 333), (10, 357), (11, 355), (12, 304), (13, 373), (14, 284), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e739) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 379) (RestInside.out (n := 379) f158 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 380) f158 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 381) (ρ' := [(0, 379), (1, 343), (2, 380), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 371), (9, 333), (10, 357), (11, 355), (12, 304), (13, 373), (14, 284), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e73c) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 382) (RestInside.out (n := 382) f159 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 383) (ρ' := [(0, 379), (1, 382), (2, 380), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 371), (9, 333), (10, 357), (11, 355), (12, 304), (13, 373), (14, 284), (15, 377), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e73f) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_8 code

theorem rest_l10e4c0_6 [Bindings] (code : CodeMap) :
    Rest (n := 295) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 288), (1, 214), (2, 289), (3, 263), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 170), (10, 261), (11, 282), (12, 197), (13, 199), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]
      373 0x10e69e bytes_l10e4c0_6 b_l10e4c0_6 := by
  have f120 : InstrSpec 0x10e69e [0x83, 0xE3, 0x0F] (fun s => s.RIP = 0x10e69e) (andR32Imm8Effect 0x10e69e 3 3 0xf)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x10e69e 3 3 0xf).toInstrSpec (and_r32_imm8_effect_step 0x10e69e 0xe3 0xf (by decide) (by decide)) pre_rip
  have f121 : InstrSpec 0x10e6a1 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x10e6a1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10e6a1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e6a1 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e6a1 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10e6a1 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f122 : InstrSpec 0x10e6a6 [0x48, 0xF7, 0x64, 0x24, 0x70] (LoadPre 0x10e6a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10e6a6 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10e6a6 5 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x10e6a6 5 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mul_m64_effect_step 0x10e6a6 0x48 (by decide) (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f123 : InstrSpec 0x10e6ab [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x10e6ab) (movR64R64Effect 0x10e6ab 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10e6ab 9 2).toInstrSpec (mov_r64_r64_effect_step 0x10e6ab 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x10e6ae [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x10e6ae) (movR64R64Effect 0x10e6ae 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10e6ae 12 0).toInstrSpec (mov_r64_r64_effect_step 0x10e6ae 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f125 : InstrSpec 0x10e6b1 [0x4C, 0x8B, 0x6C, 0x24, 0x48] (LoadPre 0x10e6b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10e6b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e6b1 13 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x10e6b1 13 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10e6b1 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f126 : InstrSpec 0x10e6b6 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x10e6b6) (movR64R64Effect 0x10e6b6 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e6b6 0 13).toInstrSpec (mov_r64_r64_effect_step 0x10e6b6 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f127 : InstrSpec 0x10e6b9 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e6b9) (mulR64Effect 0x10e6b9 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e6b9 1).toInstrSpec (mul_r64_effect_step 0x10e6b9 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f128 : InstrSpec 0x10e6bc [0x4C, 0x01, 0xE0] (fun s => s.RIP = 0x10e6bc) (addR64R64Effect 0x10e6bc 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e6bc 0 12).toInstrSpec (add_r64_r64_effect_step 0x10e6bc 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f129 : InstrSpec 0x10e6bf [0x49, 0x11, 0xD1] (fun s => s.RIP = 0x10e6bf) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e6bf 9 2))
      [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e6bf 9 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e6bf 0x49 0xd1 c (by decide) (by decide))) pre_rip
  have f130 : InstrSpec 0x10e6c2 [0x48, 0x01, 0xF0] (fun s => s.RIP = 0x10e6c2) (addR64R64Effect 0x10e6c2 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e6c2 0 6).toInstrSpec (add_r64_r64_effect_step 0x10e6c2 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f131 : InstrSpec 0x10e6c5 [0x4D, 0x11, 0xF9] (fun s => s.RIP = 0x10e6c5) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e6c5 9 15))
      [.gpr 9, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e6c5 9 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e6c5 0x4d 0xf9 c (by decide) (by decide))) pre_rip
  have f132 : InstrSpec 0x10e6c8 [0x4C, 0x01, 0xD8] (fun s => s.RIP = 0x10e6c8) (addR64R64Effect 0x10e6c8 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e6c8 0 11).toInstrSpec (add_r64_r64_effect_step 0x10e6c8 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f133 : InstrSpec 0x10e6cb [0x4C, 0x13, 0x4C, 0x24, 0x08] (LoadPre 0x10e6cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e6cb + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e6cb 9 (.sib 4 none 0 (.d8 0x8))))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10e6cb 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10e6cb 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f134 : InstrSpec 0x10e6d0 [0x4C, 0x01, 0xD0] (fun s => s.RIP = 0x10e6d0) (addR64R64Effect 0x10e6d0 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e6d0 0 10).toInstrSpec (add_r64_r64_effect_step 0x10e6d0 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f135 : InstrSpec 0x10e6d3 [0x49, 0x83, 0xD1, 0x00] (fun s => s.RIP = 0x10e6d3) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e6d3 9 0x0))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10e6d3 9 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10e6d3 0x49 0xd1 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f136 : InstrSpec 0x10e6d7 [0x49, 0x0F, 0xA4, 0xC1, 0x0C] (fun s => s.RIP = 0x10e6d7) (shldR64R64Effect 0x10e6d7 5 9 0 12)
      [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e6d7 5 9 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e6d7 0x49 (by decide) 0xc1 (by decide) 0xc) pre_rip
  have f137 : InstrSpec 0x10e6dc [0x48, 0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x10e6dc) (shlR64Effect 0x10e6dc 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10e6dc 4 0 4).toInstrSpec (shl_r64_imm8_effect_step 0x10e6dc 0x48 0xe0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f138 : InstrSpec 0x10e6e0 [0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00] (fun s => s.RIP = 0x10e6e0) (movR64Imm64Effect 0x10e6e0 1 0xfffffffffffff0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10e6e0 1 0xfffffffffffff0).toInstrSpec (mov_r64_imm64_effect_step 0x10e6e0 0x48 0xb9 (by decide) (by decide) 0xfffffffffffff0) pre_rip
  have f139 : InstrSpec 0x10e6ea [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x10e6ea) (andR64R64Effect 0x10e6ea 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e6ea 0 1).toInstrSpec (and_r64_r64_effect_step 0x10e6ea 0x48 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 295) (RestInside.out (n := 295) f120 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 296) (ρ' := [(0, 288), (1, 214), (2, 289), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 170), (10, 261), (11, 282), (12, 197), (13, 199), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6a1) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.out (n := 297) f121 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 298) (ρ' := [(0, 297), (1, 214), (2, 289), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 170), (10, 261), (11, 282), (12, 197), (13, 199), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6a6) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 299) (RestInside.out (n := 299) f122 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 300) f122 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 301) (ρ' := [(0, 299), (1, 214), (2, 300), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 170), (10, 261), (11, 282), (12, 197), (13, 199), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6ab) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f123 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 299), (1, 214), (2, 300), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 302), (10, 261), (11, 282), (12, 197), (13, 199), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6ae) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f124 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(0, 299), (1, 214), (2, 300), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 302), (10, 261), (11, 282), (12, 304), (13, 199), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6b1) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.out (n := 306) f125 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 307) (ρ' := [(0, 299), (1, 214), (2, 300), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 302), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6b6) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 308) (RestInside.out (n := 308) f126 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 309) (ρ' := [(0, 308), (1, 214), (2, 300), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 302), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6b9) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 310) (RestInside.out (n := 310) f127 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 311) f127 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 312) (ρ' := [(0, 310), (1, 214), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 302), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6bc) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 313) (RestInside.out (n := 313) f128 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 314) f128 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 315) (ρ' := [(0, 313), (1, 214), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 302), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (16, 314), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6bf) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 316) (RestInside.out (n := 316) f129 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 317) (ρ' := [(0, 313), (1, 214), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 316), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6c2) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 318) (RestInside.out (n := 318) f130 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 319) f130 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 320) (ρ' := [(0, 318), (1, 214), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 316), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (16, 319), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6c5) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 321) (RestInside.out (n := 321) f131 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 322) (ρ' := [(0, 318), (1, 214), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 321), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6c8) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 323) (RestInside.out (n := 323) f132 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 324) f132 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 325) (ρ' := [(0, 323), (1, 214), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 321), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (16, 324), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6cb) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 326) (RestInside.out (n := 326) f133 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 327) (ρ' := [(0, 323), (1, 214), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 326), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6d0) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 328) (RestInside.out (n := 328) f134 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 329) f134 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 330) (ρ' := [(0, 328), (1, 214), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 326), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (16, 329), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6d3) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 331) (RestInside.out (n := 331) f135 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 332) (ρ' := [(0, 328), (1, 214), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 331), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6d7) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 333) (RestInside.out (n := 333) f136 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 334) (ρ' := [(0, 328), (1, 214), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6dc) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 335) (RestInside.out (n := 335) f137 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 336) (ρ' := [(0, 335), (1, 214), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6e0) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 337) (RestInside.out (n := 337) f138 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 338) (ρ' := [(0, 335), (1, 337), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6ea) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 339) (RestInside.out (n := 339) f139 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 340) (ρ' := [(0, 339), (1, 337), (2, 311), (3, 295), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 333), (10, 261), (11, 282), (12, 304), (13, 306), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e6ed) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_7 code

theorem rest_l10e4c0_5 [Bindings] (code : CodeMap) :
    Rest (n := 255) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 227), (1, 214), (2, 228), (3, 250), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 253), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]
      393 0x10e650 bytes_l10e4c0_5 b_l10e4c0_5 := by
  have f100 : InstrSpec 0x10e650 [0x4C, 0x01, 0xC3] (fun s => s.RIP = 0x10e650) (addR64R64Effect 0x10e650 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e650 3 8).toInstrSpec (add_r64_r64_effect_step 0x10e650 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f101 : InstrSpec 0x10e653 [0x48, 0x89, 0x5C, 0x24, 0x28] (StorePre 0x10e653 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e653 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e653 3 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e653 3 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10e653 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f102 : InstrSpec 0x10e658 [0x49, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x10e658) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e658 10 0x0))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x10e658 10 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x10e658 0x49 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f103 : InstrSpec 0x10e65c [0x49, 0x0F, 0xA4, 0xDA, 0x0C] (fun s => s.RIP = 0x10e65c) (shldR64R64Effect 0x10e65c 5 10 3 12)
      [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e65c 5 10 3 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e65c 0x49 (by decide) 0xda (by decide) 0xc) pre_rip
  have f104 : InstrSpec 0x10e661 [0x48, 0xC1, 0xEB, 0x30] (fun s => s.RIP = 0x10e661) (shrR64Effect 0x10e661 4 3 48)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x10e661 4 3 48).toInstrSpec (shr_r64_imm8_effect_step 0x10e661 0x48 0xeb 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x10e665 [0x4C, 0x89, 0xFD] (fun s => s.RIP = 0x10e665) (movR64R64Effect 0x10e665 5 15)
      [.gpr 15] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x10e665 5 15).toInstrSpec (mov_r64_r64_effect_step 0x10e665 0x4c 0xfd (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x10e668 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x10e668) (movR64R64Effect 0x10e668 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e668 0 15).toInstrSpec (mov_r64_r64_effect_step 0x10e668 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x10e66b [0x49, 0xF7, 0xE6] (fun s => s.RIP = 0x10e66b) (mulR64Effect 0x10e66b 14)
      [.gpr 14, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e66b 14).toInstrSpec (mul_r64_effect_step 0x10e66b 0x49 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x10e66e [0x48, 0x89, 0x54, 0x24, 0x18] (StorePre 0x10e66e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e66e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e66e 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e66e 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10e66e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f109 : InstrSpec 0x10e673 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x10e673 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e673 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e673 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e673 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10e673 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f110 : InstrSpec 0x10e678 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x10e678 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10e678 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e678 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e678 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10e678 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f111 : InstrSpec 0x10e67d [0x4C, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x10e67d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e67d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e67d 8 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10e67d 8 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10e67d 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f112 : InstrSpec 0x10e682 [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x10e682) (mulR64Effect 0x10e682 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e682 8).toInstrSpec (mul_r64_effect_step 0x10e682 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f113 : InstrSpec 0x10e685 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x10e685 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e685 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e685 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e685 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10e685 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f114 : InstrSpec 0x10e68a [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x10e68a) (movR64R64Effect 0x10e68a 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10e68a 11 0).toInstrSpec (mov_r64_r64_effect_step 0x10e68a 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x10e68d [0x4C, 0x8B, 0x74, 0x24, 0x50] (LoadPre 0x10e68d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10e68d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e68d 14 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x10e68d 14 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10e68d 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f116 : InstrSpec 0x10e692 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x10e692) (movR64R64Effect 0x10e692 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e692 0 14).toInstrSpec (mov_r64_r64_effect_step 0x10e692 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x10e695 [0x48, 0xF7, 0xE6] (fun s => s.RIP = 0x10e695) (mulR64Effect 0x10e695 6)
      [.gpr 6, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e695 6).toInstrSpec (mul_r64_effect_step 0x10e695 0x48 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x10e698 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x10e698) (movR64R64Effect 0x10e698 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10e698 6 0).toInstrSpec (mov_r64_r64_effect_step 0x10e698 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f119 : InstrSpec 0x10e69b [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x10e69b) (movR64R64Effect 0x10e69b 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10e69b 15 2).toInstrSpec (mov_r64_r64_effect_step 0x10e69b 0x49 0xd7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 255) (RestInside.out (n := 255) f100 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 256) f100 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 257) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 255), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 253), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (16, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e653) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 258) (RestInside.exec (n := 258) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 255), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 253), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (16, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e658) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f102 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 255), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 259), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e65c) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.out (n := 261) f103 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 262) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 255), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 261), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e661) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 263) (RestInside.out (n := 263) f104 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 264) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 263), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 261), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e665) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f105 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 266) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 263), (4, 65), (5, 265), (6, 192), (7, 7), (8, 172), (9, 170), (10, 261), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e668) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 267) (RestInside.out (n := 267) f106 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 268) (ρ' := [(0, 267), (1, 214), (2, 228), (3, 263), (4, 65), (5, 265), (6, 192), (7, 7), (8, 172), (9, 170), (10, 261), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e66b) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 269) (RestInside.out (n := 269) f107 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 270) f107 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 271) (ρ' := [(0, 269), (1, 214), (2, 270), (3, 263), (4, 65), (5, 265), (6, 192), (7, 7), (8, 172), (9, 170), (10, 261), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e66e) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 272) (RestInside.exec (n := 272) (ρ' := [(0, 269), (1, 214), (2, 270), (3, 263), (4, 65), (5, 265), (6, 192), (7, 7), (8, 172), (9, 170), (10, 261), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e673) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 273) (RestInside.exec (n := 273) (ρ' := [(0, 269), (1, 214), (2, 270), (3, 263), (4, 65), (5, 265), (6, 192), (7, 7), (8, 172), (9, 170), (10, 261), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e678) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 274) (RestInside.out (n := 274) f110 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 275) (ρ' := [(0, 274), (1, 214), (2, 270), (3, 263), (4, 65), (5, 265), (6, 192), (7, 7), (8, 172), (9, 170), (10, 261), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e67d) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 276) (RestInside.out (n := 276) f111 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 277) (ρ' := [(0, 274), (1, 214), (2, 270), (3, 263), (4, 65), (5, 265), (6, 192), (7, 7), (8, 276), (9, 170), (10, 261), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e682) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 278) (RestInside.out (n := 278) f112 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 279) f112 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 280) (ρ' := [(0, 278), (1, 214), (2, 279), (3, 263), (4, 65), (5, 265), (6, 192), (7, 7), (8, 276), (9, 170), (10, 261), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e685) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 281) (RestInside.exec (n := 281) (ρ' := [(0, 278), (1, 214), (2, 279), (3, 263), (4, 65), (5, 265), (6, 192), (7, 7), (8, 276), (9, 170), (10, 261), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e68a) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 282) (RestInside.out (n := 282) f114 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 283) (ρ' := [(0, 278), (1, 214), (2, 279), (3, 263), (4, 65), (5, 265), (6, 192), (7, 7), (8, 276), (9, 170), (10, 261), (11, 282), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e68d) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 284) (RestInside.out (n := 284) f115 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 285) (ρ' := [(0, 278), (1, 214), (2, 279), (3, 263), (4, 65), (5, 265), (6, 192), (7, 7), (8, 276), (9, 170), (10, 261), (11, 282), (12, 197), (13, 199), (14, 284), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e692) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 286) (RestInside.out (n := 286) f116 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 287) (ρ' := [(0, 286), (1, 214), (2, 279), (3, 263), (4, 65), (5, 265), (6, 192), (7, 7), (8, 276), (9, 170), (10, 261), (11, 282), (12, 197), (13, 199), (14, 284), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e695) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 288) (RestInside.out (n := 288) f117 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 289) f117 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 290) (ρ' := [(0, 288), (1, 214), (2, 289), (3, 263), (4, 65), (5, 265), (6, 192), (7, 7), (8, 276), (9, 170), (10, 261), (11, 282), (12, 197), (13, 199), (14, 284), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e698) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 291) (RestInside.out (n := 291) f118 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 292) (ρ' := [(0, 288), (1, 214), (2, 289), (3, 263), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 170), (10, 261), (11, 282), (12, 197), (13, 199), (14, 284), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e69b) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 293) (RestInside.out (n := 293) f119 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 294) (ρ' := [(0, 288), (1, 214), (2, 289), (3, 263), (4, 65), (5, 265), (6, 291), (7, 7), (8, 276), (9, 170), (10, 261), (11, 282), (12, 197), (13, 199), (14, 284), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e69e) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_6 code

theorem rest_l10e4c0_4 [Bindings] (code : CodeMap) :
    Rest (n := 208) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 203), (1, 136), (2, 204), (3, 112), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 197), (13, 199), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]
      413 0x10e5fe bytes_l10e4c0_4 b_l10e4c0_4 := by
  have f80 : InstrSpec 0x10e5fe [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x10e5fe) (movR64R64Effect 0x10e5fe 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10e5fe 11 0).toInstrSpec (mov_r64_r64_effect_step 0x10e5fe 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x10e601 [0x4C, 0x8B, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x10e601 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10e601 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10e601 15 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10e601 15 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x10e601 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f82 : InstrSpec 0x10e609 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x10e609) (movR64R64Effect 0x10e609 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e609 0 15).toInstrSpec (mov_r64_r64_effect_step 0x10e609 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x10e60c [0x48, 0x8B, 0x4C, 0x24, 0x40] (LoadPre 0x10e60c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10e60c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e60c 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10e60c 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10e60c 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f84 : InstrSpec 0x10e611 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e611) (mulR64Effect 0x10e611 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e611 1).toInstrSpec (mul_r64_effect_step 0x10e611 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x10e614 [0x49, 0x89, 0xD2] (fun s => s.RIP = 0x10e614) (movR64R64Effect 0x10e614 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10e614 10 2).toInstrSpec (mov_r64_r64_effect_step 0x10e614 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x10e617 [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x10e617) (movR64R64Effect 0x10e617 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10e617 3 0).toInstrSpec (mov_r64_r64_effect_step 0x10e617 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x10e61a [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x10e61a) (movR64R64Effect 0x10e61a 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e61a 0 9).toInstrSpec (mov_r64_r64_effect_step 0x10e61a 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x10e61d [0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10e61d) (movR64Imm64Effect 0x10e61d 2 0x1000003d10)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x10e61d 2 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x10e61d 0x48 0xba (by decide) (by decide) 0x1000003d10) pre_rip
  have f89 : InstrSpec 0x10e627 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x10e627) (mulR64Effect 0x10e627 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e627 2).toInstrSpec (mul_r64_effect_step 0x10e627 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x10e62a [0x4C, 0x01, 0xDB] (fun s => s.RIP = 0x10e62a) (addR64R64Effect 0x10e62a 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e62a 3 11).toInstrSpec (add_r64_r64_effect_step 0x10e62a 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x10e62d [0x49, 0x11, 0xEA] (fun s => s.RIP = 0x10e62d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e62d 10 5))
      [.gpr 10, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e62d 10 5).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e62d 0x49 0xea c (by decide) (by decide))) pre_rip
  have f92 : InstrSpec 0x10e630 [0x4C, 0x01, 0xEB] (fun s => s.RIP = 0x10e630) (addR64R64Effect 0x10e630 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e630 3 13).toInstrSpec (add_r64_r64_effect_step 0x10e630 0x4c 0xeb (by decide) (by decide)) pre_rip
  have f93 : InstrSpec 0x10e633 [0x4D, 0x11, 0xE2] (fun s => s.RIP = 0x10e633) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e633 10 12))
      [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e633 10 12).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e633 0x4d 0xe2 c (by decide) (by decide))) pre_rip
  have f94 : InstrSpec 0x10e636 [0x48, 0x03, 0x5C, 0x24, 0x08] (LoadPre 0x10e636 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e636 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10e636 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.reg 3, .flags, .rip] :=
    (addR64M64Effect_footprint 0x10e636 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (add_r64_m64_effect_step 0x10e636 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f95 : InstrSpec 0x10e63b [0x4C, 0x13, 0x54, 0x24, 0x10] (LoadPre 0x10e63b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e63b + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e63b 10 (.sib 4 none 0 (.d8 0x10))))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10e63b 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10e63b 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f96 : InstrSpec 0x10e640 [0x48, 0x03, 0x5C, 0x24, 0x18] (LoadPre 0x10e640 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e640 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10e640 3 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 3, .gpr 4] [] [.reg 3, .flags, .rip] :=
    (addR64M64Effect_footprint 0x10e640 3 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (add_r64_m64_effect_step 0x10e640 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f97 : InstrSpec 0x10e645 [0x4C, 0x13, 0x54, 0x24, 0x28] (LoadPre 0x10e645 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e645 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e645 10 (.sib 4 none 0 (.d8 0x28))))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10e645 10 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10e645 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f98 : InstrSpec 0x10e64a [0x48, 0x01, 0xC3] (fun s => s.RIP = 0x10e64a) (addR64R64Effect 0x10e64a 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e64a 3 0).toInstrSpec (add_r64_r64_effect_step 0x10e64a 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x10e64d [0x49, 0x11, 0xD2] (fun s => s.RIP = 0x10e64d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e64d 10 2))
      [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e64d 10 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e64d 0x49 0xd2 c (by decide) (by decide))) pre_rip
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f80 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 203), (1, 136), (2, 204), (3, 112), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 164), (11, 208), (12, 197), (13, 199), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e601) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f81 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 203), (1, 136), (2, 204), (3, 112), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 164), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e609) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f82 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 212), (1, 136), (2, 204), (3, 112), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 164), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e60c) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f83 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 212), (1, 214), (2, 204), (3, 112), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 164), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e611) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f84 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 217) f84 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 218) (ρ' := [(0, 216), (1, 214), (2, 217), (3, 112), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 164), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e614) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f85 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 216), (1, 214), (2, 217), (3, 112), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 219), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e617) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f86 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 216), (1, 214), (2, 217), (3, 221), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 219), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e61a) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f87 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 223), (1, 214), (2, 217), (3, 221), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 219), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e61d) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f88 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 223), (1, 214), (2, 225), (3, 221), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 219), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e627) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f89 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 228) f89 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 229) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 221), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 219), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e62a) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 230) (RestInside.out (n := 230) f90 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 231) f90 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 232) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 230), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 219), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (16, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e62d) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.out (n := 233) f91 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 234) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 230), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 233), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e630) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 235) (RestInside.out (n := 235) f92 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 236) f92 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 237) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 235), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 233), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (16, 236), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e633) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f93 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 235), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 238), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e636) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f94 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 241) f94 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 242) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 240), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 238), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (16, 241), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e63b) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 243) (RestInside.out (n := 243) f95 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 244) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 240), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 243), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e640) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.out (n := 245) f96 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 246) f96 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 247) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 245), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 243), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (16, 246), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e645) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 248) (RestInside.out (n := 248) f97 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 249) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 245), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 248), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e64a) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 250) (RestInside.out (n := 250) f98 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 251) f98 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 252) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 250), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 248), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (16, 251), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e64d) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f99 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 254) (ρ' := [(0, 227), (1, 214), (2, 228), (3, 250), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 253), (11, 208), (12, 197), (13, 199), (14, 176), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e650) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_5 code

theorem rest_l10e4c0_3 [Bindings] (code : CodeMap) :
    Rest (n := 168) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 146), (1, 136), (2, 147), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 162), (9, 138), (10, 164), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (16, 165), (22, 22), (39, 39), (50, 50), (51, 51)]
      433 0x10e5af bytes_l10e4c0_3 b_l10e4c0_3 := by
  have f60 : InstrSpec 0x10e5af [0x49, 0x11, 0xD0] (fun s => s.RIP = 0x10e5af) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e5af 8 2))
      [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e5af 8 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e5af 0x49 0xd0 c (by decide) (by decide))) pre_rip
  have f61 : InstrSpec 0x10e5b2 [0x49, 0x0F, 0xA4, 0xC9, 0x0C] (fun s => s.RIP = 0x10e5b2) (shldR64R64Effect 0x10e5b2 5 9 1 12)
      [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e5b2 5 9 1 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e5b2 0x49 (by decide) 0xc9 (by decide) 0xc) pre_rip
  have f62 : InstrSpec 0x10e5b7 [0x4D, 0x0F, 0xA4, 0xD0, 0x0C] (fun s => s.RIP = 0x10e5b7) (shldR64R64Effect 0x10e5b7 5 8 10 12)
      [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10e5b7 5 8 10 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10e5b7 0x4d (by decide) 0xd0 (by decide) 0xc) pre_rip
  have f63 : InstrSpec 0x10e5bc [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x10e5bc) (movR64R64Effect 0x10e5bc 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e5bc 0 13).toInstrSpec (mov_r64_r64_effect_step 0x10e5bc 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x10e5bf [0x4C, 0x8B, 0x34, 0x24] (LoadPre 0x10e5bf (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e5bf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e5bf 14 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x10e5bf 14 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10e5bf 0x4c (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f65 : InstrSpec 0x10e5c3 [0x49, 0xF7, 0xE6] (fun s => s.RIP = 0x10e5c3) (mulR64Effect 0x10e5c3 14)
      [.gpr 14, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e5c3 14).toInstrSpec (mul_r64_effect_step 0x10e5c3 0x49 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x10e5c6 [0x48, 0x89, 0x54, 0x24, 0x28] (StorePre 0x10e5c6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e5c6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e5c6 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e5c6 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10e5c6 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f67 : InstrSpec 0x10e5cb [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x10e5cb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e5cb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e5cb 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e5cb 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10e5cb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f68 : InstrSpec 0x10e5d0 [0x48, 0x8B, 0x44, 0x24, 0x50] (LoadPre 0x10e5d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10e5d0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e5d0 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e5d0 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10e5d0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f69 : InstrSpec 0x10e5d5 [0x48, 0xF7, 0xE5] (fun s => s.RIP = 0x10e5d5) (mulR64Effect 0x10e5d5 5)
      [.gpr 5, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e5d5 5).toInstrSpec (mul_r64_effect_step 0x10e5d5 0x48 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x10e5d8 [0x48, 0x89, 0x54, 0x24, 0x10] (StorePre 0x10e5d8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e5d8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e5d8 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e5d8 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10e5d8 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f71 : InstrSpec 0x10e5dd [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x10e5dd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e5dd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e5dd 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e5dd 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10e5dd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f72 : InstrSpec 0x10e5e2 [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x10e5e2) (movR64R64Effect 0x10e5e2 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e5e2 0 11).toInstrSpec (mov_r64_r64_effect_step 0x10e5e2 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x10e5e5 [0x48, 0x8B, 0x74, 0x24, 0x68] (LoadPre 0x10e5e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10e5e5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e5e5 6 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10e5e5 6 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x10e5e5 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f74 : InstrSpec 0x10e5ea [0x48, 0xF7, 0xE6] (fun s => s.RIP = 0x10e5ea) (mulR64Effect 0x10e5ea 6)
      [.gpr 6, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e5ea 6).toInstrSpec (mul_r64_effect_step 0x10e5ea 0x48 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x10e5ed [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x10e5ed) (movR64R64Effect 0x10e5ed 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10e5ed 12 2).toInstrSpec (mov_r64_r64_effect_step 0x10e5ed 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x10e5f0 [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x10e5f0) (movR64R64Effect 0x10e5f0 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10e5f0 13 0).toInstrSpec (mov_r64_r64_effect_step 0x10e5f0 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x10e5f3 [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x10e5f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10e5f3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e5f3 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e5f3 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10e5f3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f78 : InstrSpec 0x10e5f8 [0x48, 0xF7, 0xE3] (fun s => s.RIP = 0x10e5f8) (mulR64Effect 0x10e5f8 3)
      [.gpr 3, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e5f8 3).toInstrSpec (mul_r64_effect_step 0x10e5f8 0x48 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x10e5fb [0x48, 0x89, 0xD5] (fun s => s.RIP = 0x10e5fb) (movR64R64Effect 0x10e5fb 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x10e5fb 5 2).toInstrSpec (mov_r64_r64_effect_step 0x10e5fb 0x48 0xd5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f60 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 146), (1, 136), (2, 147), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 168), (9, 138), (10, 164), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5b2) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f61 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 146), (1, 136), (2, 147), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 168), (9, 170), (10, 164), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5b7) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f62 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 146), (1, 136), (2, 147), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5bc) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f63 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 174), (1, 136), (2, 147), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5bf) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f64 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 174), (1, 136), (2, 147), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 107), (13, 125), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5c3) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.out (n := 178) f65 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 179) f65 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 180) (ρ' := [(0, 178), (1, 136), (2, 179), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 107), (13, 125), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5c6) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.exec (n := 181) (ρ' := [(0, 178), (1, 136), (2, 179), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 107), (13, 125), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5cb) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 182) (RestInside.exec (n := 182) (ρ' := [(0, 178), (1, 136), (2, 179), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 107), (13, 125), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5d0) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f68 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 183), (1, 136), (2, 179), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 107), (13, 125), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5d5) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f69 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 186) f69 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 187) (ρ' := [(0, 185), (1, 136), (2, 186), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 107), (13, 125), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5d8) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 188) (RestInside.exec (n := 188) (ρ' := [(0, 185), (1, 136), (2, 186), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 107), (13, 125), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5dd) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 189) (RestInside.exec (n := 189) (ρ' := [(0, 185), (1, 136), (2, 186), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 107), (13, 125), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5e2) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 190) (RestInside.out (n := 190) f72 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 191) (ρ' := [(0, 190), (1, 136), (2, 186), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 107), (13, 125), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5e5) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f73 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 193) (ρ' := [(0, 190), (1, 136), (2, 186), (3, 112), (4, 65), (5, 72), (6, 192), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 107), (13, 125), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5ea) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f74 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 195) f74 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 196) (ρ' := [(0, 194), (1, 136), (2, 195), (3, 112), (4, 65), (5, 72), (6, 192), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 107), (13, 125), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5ed) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f75 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 194), (1, 136), (2, 195), (3, 112), (4, 65), (5, 72), (6, 192), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 197), (13, 125), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5f0) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f76 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 194), (1, 136), (2, 195), (3, 112), (4, 65), (5, 72), (6, 192), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 197), (13, 199), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5f3) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f77 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 201), (1, 136), (2, 195), (3, 112), (4, 65), (5, 72), (6, 192), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 197), (13, 199), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5f8) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f78 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 204) f78 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 205) (ρ' := [(0, 203), (1, 136), (2, 204), (3, 112), (4, 65), (5, 72), (6, 192), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 197), (13, 199), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5fb) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f79 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 203), (1, 136), (2, 204), (3, 112), (4, 65), (5, 206), (6, 192), (7, 7), (8, 172), (9, 170), (10, 164), (11, 82), (12, 197), (13, 199), (14, 176), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5fe) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_4 code

theorem rest_l10e4c0_2 [Bindings] (code : CodeMap) :
    Rest (n := 125) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 117), (1, 67), (2, 118), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 123), (9, 77), (10, 121), (11, 82), (12, 107), (13, 13), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]
      453 0x10e557 bytes_l10e4c0_2 b_l10e4c0_2 := by
  have f40 : InstrSpec 0x10e557 [0x4C, 0x8B, 0x69, 0x20] (LoadPre 0x10e557 (fun s => AddrMode.addr (.base 1 (.d8 0x20)) s (0x10e557 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e557 13 (.base 1 (.d8 0x20)))
      [.gpr 1] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x10e557 13 (.base 1 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10e557 0x4c (by decide) 5 (.base 1 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x10e55b [0x49, 0x8B, 0x49, 0x20] (LoadPre 0x10e55b (fun s => AddrMode.addr (.base 9 (.d8 0x20)) s (0x10e55b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e55b 1 (.base 9 (.d8 0x20)))
      [.gpr 9] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10e55b 1 (.base 9 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10e55b 0x49 (by decide) 1 (.base 9 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f42 : InstrSpec 0x10e55f [0x48, 0x89, 0x4C, 0x24, 0x40] (StorePre 0x10e55f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10e55f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e55f 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e55f 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x10e55f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f43 : InstrSpec 0x10e564 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x10e564) (movR64R64Effect 0x10e564 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e564 0 13).toInstrSpec (mov_r64_r64_effect_step 0x10e564 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x10e567 [0x4C, 0x89, 0x6C, 0x24, 0x38] (StorePre 0x10e567 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10e567 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e567 13 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e567 13 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10e567 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x10e56c [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x10e56c) (mulR64Effect 0x10e56c 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e56c 1).toInstrSpec (mul_r64_effect_step 0x10e56c 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x10e56f [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10e56f) (movR64R64Effect 0x10e56f 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10e56f 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10e56f 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x10e572 [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x10e572) (movR64R64Effect 0x10e572 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10e572 9 2).toInstrSpec (mov_r64_r64_effect_step 0x10e572 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x10e575 [0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x10e575) (movR64Imm64Effect 0x10e575 2 0xfffffffffffff)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x10e575 2 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10e575 0x48 0xba (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f49 : InstrSpec 0x10e57f [0x48, 0x21, 0xD0] (fun s => s.RIP = 0x10e57f) (andR64R64Effect 0x10e57f 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10e57f 0 2).toInstrSpec (and_r64_r64_effect_step 0x10e57f 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x10e582 [0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10e582) (movR64Imm64Effect 0x10e582 2 0x1000003d10)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x10e582 2 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x10e582 0x48 0xba (by decide) (by decide) 0x1000003d10) pre_rip
  have f51 : InstrSpec 0x10e58c [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x10e58c) (mulR64Effect 0x10e58c 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e58c 2).toInstrSpec (mul_r64_effect_step 0x10e58c 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x10e58f [0x4D, 0x01, 0xE2] (fun s => s.RIP = 0x10e58f) (addR64R64Effect 0x10e58f 10 12)
      [.gpr 10, .gpr 12] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e58f 10 12).toInstrSpec (add_r64_r64_effect_step 0x10e58f 0x4d 0xe2 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x10e592 [0x4D, 0x11, 0xF8] (fun s => s.RIP = 0x10e592) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e592 8 15))
      [.gpr 8, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x10e592 8 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x10e592 0x4d 0xf8 c (by decide) (by decide))) pre_rip
  have f54 : InstrSpec 0x10e595 [0x4D, 0x01, 0xF2] (fun s => s.RIP = 0x10e595) (addR64R64Effect 0x10e595 10 14)
      [.gpr 10, .gpr 14] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e595 10 14).toInstrSpec (add_r64_r64_effect_step 0x10e595 0x4d 0xf2 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x10e598 [0x4C, 0x13, 0x44, 0x24, 0x18] (LoadPre 0x10e598 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e598 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e598 8 (.sib 4 none 0 (.d8 0x18))))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10e598 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10e598 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f56 : InstrSpec 0x10e59d [0x4C, 0x03, 0x54, 0x24, 0x78] (LoadPre 0x10e59d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10e59d + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10e59d 10 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 10, .gpr 4] [] [.reg 10, .flags, .rip] :=
    (addR64M64Effect_footprint 0x10e59d 10 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (add_r64_m64_effect_step 0x10e59d 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f57 : InstrSpec 0x10e5a2 [0x4C, 0x13, 0x44, 0x24, 0x28] (LoadPre 0x10e5a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e5a2 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e5a2 8 (.sib 4 none 0 (.d8 0x28))))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x10e5a2 8 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x10e5a2 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f58 : InstrSpec 0x10e5a7 [0x49, 0x01, 0xC2] (fun s => s.RIP = 0x10e5a7) (addR64R64Effect 0x10e5a7 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10e5a7 10 0).toInstrSpec (add_r64_r64_effect_step 0x10e5a7 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x10e5aa [0x4C, 0x89, 0x54, 0x24, 0x78] (StorePre 0x10e5aa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10e5aa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e5aa 10 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e5aa 10 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x10e5aa 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f40 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 117), (1, 67), (2, 118), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 123), (9, 77), (10, 121), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e55b) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f41 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 117), (1, 127), (2, 118), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 123), (9, 77), (10, 121), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e55f) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.exec (n := 129) (ρ' := [(0, 117), (1, 127), (2, 118), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 123), (9, 77), (10, 121), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e564) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f43 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 130), (1, 127), (2, 118), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 123), (9, 77), (10, 121), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e567) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.exec (n := 132) (ρ' := [(0, 130), (1, 127), (2, 118), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 123), (9, 77), (10, 121), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e56c) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f45 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 134) f45 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 135) (ρ' := [(0, 133), (1, 127), (2, 134), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 123), (9, 77), (10, 121), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e56f) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 133), (1, 136), (2, 134), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 123), (9, 77), (10, 121), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e572) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f47 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 133), (1, 136), (2, 134), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 123), (9, 138), (10, 121), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e575) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f48 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 133), (1, 136), (2, 140), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 123), (9, 138), (10, 121), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e57f) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f49 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 142), (1, 136), (2, 140), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 123), (9, 138), (10, 121), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e582) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f50 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 142), (1, 136), (2, 144), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 123), (9, 138), (10, 121), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e58c) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f51 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 147) f51 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 148) (ρ' := [(0, 146), (1, 136), (2, 147), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 123), (9, 138), (10, 121), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e58f) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f52 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 150) f52 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 151) (ρ' := [(0, 146), (1, 136), (2, 147), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 123), (9, 138), (10, 149), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (16, 150), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e592) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f53 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 146), (1, 136), (2, 147), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 152), (9, 138), (10, 149), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e595) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f54 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 155) f54 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 156) (ρ' := [(0, 146), (1, 136), (2, 147), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 152), (9, 138), (10, 154), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (16, 155), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e598) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f55 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 146), (1, 136), (2, 147), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 157), (9, 138), (10, 154), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e59d) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f56 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 160) f56 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 161) (ρ' := [(0, 146), (1, 136), (2, 147), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 157), (9, 138), (10, 159), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (16, 160), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5a2) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f57 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 146), (1, 136), (2, 147), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 162), (9, 138), (10, 159), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5a7) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f58 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 165) f58 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 166) (ρ' := [(0, 146), (1, 136), (2, 147), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 162), (9, 138), (10, 164), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (16, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5aa) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.exec (n := 167) (ρ' := [(0, 146), (1, 136), (2, 147), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 162), (9, 138), (10, 164), (11, 82), (12, 107), (13, 125), (14, 100), (15, 109), (16, 165), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e5af) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10e4c0_3 code

theorem rest_l10e4c0_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) [(0, 87), (1, 67), (2, 88), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      473 0x10e504 bytes_l10e4c0_1 b_l10e4c0_1 := by
  have f20 : InstrSpec 0x10e504 [0x48, 0x89, 0x54, 0x24, 0x28] (StorePre 0x10e504 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e504 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e504 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e504 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10e504 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x10e509 [0x48, 0x89, 0x44, 0x24, 0x78] (StorePre 0x10e509 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10e509 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e509 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e509 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x10e509 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x10e50e [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x10e50e) (movR64R64Effect 0x10e50e 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e50e 0 11).toInstrSpec (mov_r64_r64_effect_step 0x10e50e 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x10e511 [0x4C, 0x89, 0x5C, 0x24, 0x30] (StorePre 0x10e511 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10e511 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e511 11 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e511 11 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10e511 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x10e516 [0x48, 0xF7, 0xE5] (fun s => s.RIP = 0x10e516) (mulR64Effect 0x10e516 5)
      [.gpr 5, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e516 5).toInstrSpec (mul_r64_effect_step 0x10e516 0x48 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x10e519 [0x48, 0x89, 0x6C, 0x24, 0x20] (StorePre 0x10e519 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e519 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e519 5 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e519 5 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10e519 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x10e51e [0x48, 0x89, 0x54, 0x24, 0x18] (StorePre 0x10e51e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e51e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e51e 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e51e 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10e51e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x10e523 [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x10e523) (movR64R64Effect 0x10e523 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10e523 14 0).toInstrSpec (mov_r64_r64_effect_step 0x10e523 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10e526 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x10e526) (movR64R64Effect 0x10e526 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10e526 0 6).toInstrSpec (mov_r64_r64_effect_step 0x10e526 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x10e529 [0x49, 0xF7, 0xE2] (fun s => s.RIP = 0x10e529) (mulR64Effect 0x10e529 10)
      [.gpr 10, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e529 10).toInstrSpec (mul_r64_effect_step 0x10e529 0x49 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10e52c [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x10e52c) (movR64R64Effect 0x10e52c 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10e52c 12 0).toInstrSpec (mov_r64_r64_effect_step 0x10e52c 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10e52f [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x10e52f) (movR64R64Effect 0x10e52f 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10e52f 15 2).toInstrSpec (mov_r64_r64_effect_step 0x10e52f 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10e532 [0x4C, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x10e532 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10e532 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10e532 9 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e532 9 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x10e532 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x10e53a [0x49, 0x8B, 0x59, 0x18] (LoadPre 0x10e53a (fun s => AddrMode.addr (.base 9 (.d8 0x18)) s (0x10e53a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e53a 3 (.base 9 (.d8 0x18)))
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10e53a 3 (.base 9 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10e53a 0x49 (by decide) 3 (.base 9 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x10e53e [0x48, 0x8B, 0x01] (LoadPre 0x10e53e (fun s => AddrMode.addr (.base 1 .none) s (0x10e53e + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10e53e 0 (.base 1 .none))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e53e 0 (.base 1 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10e53e 0x48 (by decide) 0 (.base 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x10e541 [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x10e541 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10e541 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10e541 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e541 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x10e541 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x10e549 [0x48, 0xF7, 0xE3] (fun s => s.RIP = 0x10e549) (mulR64Effect 0x10e549 3)
      [.gpr 3, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e549 3).toInstrSpec (mul_r64_effect_step 0x10e549 0x48 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x10e54c [0x48, 0x89, 0x5C, 0x24, 0x70] (StorePre 0x10e54c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10e54c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e54c 3 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e54c 3 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x10e54c 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x10e551 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x10e551) (movR64R64Effect 0x10e551 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10e551 10 0).toInstrSpec (mov_r64_r64_effect_step 0x10e551 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10e554 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x10e554) (movR64R64Effect 0x10e554 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10e554 8 2).toInstrSpec (mov_r64_r64_effect_step 0x10e554 0x49 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 87), (1, 67), (2, 88), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e509) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 87), (1, 67), (2, 88), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e50e) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 92), (1, 67), (2, 88), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e511) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 92), (1, 67), (2, 88), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e516) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 96) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 97) (ρ' := [(0, 95), (1, 67), (2, 96), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e519) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 67), (2, 96), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e51e) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 95), (1, 67), (2, 96), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e523) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f27 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 95), (1, 67), (2, 96), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 12), (13, 13), (14, 100), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e526) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f28 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 102), (1, 67), (2, 96), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 12), (13, 13), (14, 100), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e529) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 105) f29 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 106) (ρ' := [(0, 104), (1, 67), (2, 105), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 12), (13, 13), (14, 100), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e52c) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f30 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 104), (1, 67), (2, 105), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 107), (13, 13), (14, 100), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e52f) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f31 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 104), (1, 67), (2, 105), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 107), (13, 13), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e532) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.exec (n := 111) (ρ' := [(0, 104), (1, 67), (2, 105), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 107), (13, 13), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e53a) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f33 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 104), (1, 67), (2, 105), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 107), (13, 13), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e53e) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f34 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 114), (1, 67), (2, 105), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 107), (13, 13), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e541) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.exec (n := 116) (ρ' := [(0, 114), (1, 67), (2, 105), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 107), (13, 13), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e549) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f36 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 118) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 119) (ρ' := [(0, 117), (1, 67), (2, 118), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 107), (13, 13), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e54c) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.exec (n := 120) (ρ' := [(0, 117), (1, 67), (2, 118), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 107), (13, 13), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e551) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f38 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 117), (1, 67), (2, 118), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 121), (11, 82), (12, 107), (13, 13), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e554) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f39 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 117), (1, 67), (2, 118), (3, 112), (4, 65), (5, 72), (6, 79), (7, 7), (8, 123), (9, 77), (10, 121), (11, 82), (12, 107), (13, 13), (14, 100), (15, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e557) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_2 code

theorem rest_l10e4c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10e4c0 bytes_l10e4c0) (entryMap (live .l10e4c0))
      493 0x10e4c0 bytes_l10e4c0 b_l10e4c0 := by
  have f0 : InstrSpec 0x10e4c0 [0x55] (PushPre 0x10e4c0 1) (pushR64Effect 0x10e4c0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10e4c0 1 5).toInstrSpec (push_r64_effect_step 0x10e4c0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10e4c1 [0x41, 0x57] (PushPre 0x10e4c1 2) (pushR64Effect 0x10e4c1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10e4c1 2 15).toInstrSpec (push_r64_rex_effect_step 0x10e4c1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10e4c3 [0x41, 0x56] (PushPre 0x10e4c3 2) (pushR64Effect 0x10e4c3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10e4c3 2 14).toInstrSpec (push_r64_rex_effect_step 0x10e4c3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10e4c5 [0x41, 0x55] (PushPre 0x10e4c5 2) (pushR64Effect 0x10e4c5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10e4c5 2 13).toInstrSpec (push_r64_rex_effect_step 0x10e4c5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10e4c7 [0x41, 0x54] (PushPre 0x10e4c7 2) (pushR64Effect 0x10e4c7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10e4c7 2 12).toInstrSpec (push_r64_rex_effect_step 0x10e4c7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10e4c9 [0x53] (PushPre 0x10e4c9 1) (pushR64Effect 0x10e4c9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10e4c9 1 3).toInstrSpec (push_r64_effect_step 0x10e4c9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10e4ca [0x48, 0x81, 0xEC, 0xE8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10e4ca) (subR64Imm32Effect 0x10e4ca 4 0xe8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10e4ca 4 0xe8).toInstrSpec (sub_r64_imm32_effect_step 0x10e4ca 0x48 0xec 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10e4d1 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x10e4d1) (movR64R64Effect 0x10e4d1 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10e4d1 1 2).toInstrSpec (mov_r64_r64_effect_step 0x10e4d1 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10e4d4 [0x48, 0x8B, 0x16] (LoadPre 0x10e4d4 (fun s => AddrMode.addr (.base 6 .none) s (0x10e4d4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10e4d4 2 (.base 6 .none))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10e4d4 2 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10e4d4 0x48 (by decide) 2 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10e4d7 [0x48, 0x89, 0x14, 0x24] (StorePre 0x10e4d7 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e4d7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e4d7 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e4d7 2 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10e4d7 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10e4db [0x48, 0x8B, 0x6E, 0x08] (LoadPre 0x10e4db (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10e4db + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e4db 5 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10e4db 5 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10e4db 0x48 (by decide) 5 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10e4df [0x4C, 0x8B, 0x56, 0x10] (LoadPre 0x10e4df (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10e4df + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e4df 10 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x10e4df 10 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10e4df 0x4c (by decide) 2 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x10e4e3 [0x4C, 0x89, 0x54, 0x24, 0x68] (StorePre 0x10e4e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10e4e3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e4e3 10 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e4e3 10 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x10e4e3 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x10e4e8 [0x49, 0x89, 0xF1] (fun s => s.RIP = 0x10e4e8) (movR64R64Effect 0x10e4e8 9 6)
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10e4e8 9 6).toInstrSpec (mov_r64_r64_effect_step 0x10e4e8 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10e4eb [0x48, 0x8B, 0x71, 0x08] (LoadPre 0x10e4eb (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x10e4eb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e4eb 6 (.base 1 (.d8 0x8)))
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10e4eb 6 (.base 1 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10e4eb 0x48 (by decide) 6 (.base 1 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10e4ef [0x48, 0x89, 0x74, 0x24, 0x48] (StorePre 0x10e4ef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10e4ef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e4ef 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e4ef 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x10e4ef 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10e4f4 [0x4C, 0x8B, 0x59, 0x10] (LoadPre 0x10e4f4 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x10e4f4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e4f4 11 (.base 1 (.d8 0x10)))
      [.gpr 1] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x10e4f4 11 (.base 1 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10e4f4 0x4c (by decide) 3 (.base 1 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10e4f8 [0x48, 0x8B, 0x41, 0x18] (LoadPre 0x10e4f8 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x10e4f8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e4f8 0 (.base 1 (.d8 0x18)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10e4f8 0 (.base 1 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10e4f8 0x48 (by decide) 0 (.base 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x10e4fc [0x48, 0x89, 0x44, 0x24, 0x50] (StorePre 0x10e4fc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10e4fc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e4fc 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10e4fc 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x10e4fc 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x10e501 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x10e501) (mulR64Effect 0x10e501 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x10e501 2).toInstrSpec (mul_r64_effect_step 0x10e501 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4c3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4c5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4c7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4c9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4ca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4d1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 67), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4d4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4d7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4db) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 72), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4df) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 72), (6, 6), (7, 7), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4e3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 72), (6, 6), (7, 7), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4e8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 72), (6, 6), (7, 7), (9, 77), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4eb) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4ef) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4f4) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(1, 67), (2, 69), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4f8) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 84), (1, 67), (2, 69), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4fc) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 84), (1, 67), (2, 69), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e501) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 88) f19 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 89) (ρ' := [(0, 87), (1, 67), (2, 88), (3, 3), (4, 65), (5, 72), (6, 79), (7, 7), (9, 77), (10, 74), (11, 82), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e504) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10e4c0_1 code

theorem block_l10e4c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10e4c0 :=
  Rest.liftedBlock (rest_l10e4c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10e4c0 x hx)

theorem rest_l10ecb2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ecb2 bytes_l10ecb2) (entryMap (live .l10ecb2))
      3 0x10ecb2 bytes_l10ecb2 b_l10ecb2 := by
  have f0 : InstrSpec 0x10ecb2 [0x48, 0x8D, 0x7B, 0x28] (fun s => s.RIP = 0x10ecb2) (leaR64Effect 0x10ecb2 7 (.base 3 (.d8 0x28)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10ecb2 7 (.base 3 (.d8 0x28))).toInstrSpec (lea_r64_effect_step 0x10ecb2 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10ecb6 [0x48, 0x8D, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ecb6) (leaR64Effect 0x10ecb6 6 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10ecb6 6 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (lea_r64_effect_step 0x10ecb6 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10ecbe [0xE8, 0x6D, 0x5C, 0x00, 0x00] (PushPre 0x10ecbe 5) (callEffect (fun _ => 0x114930) 0x10ecc3)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10ecbe 0x114930 0x10ecc3).toInstrSpec (call_rel32_effect_step 0x10ecbe 0x5c6d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecb6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecbe) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114930) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l10ecb2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ecb2 :=
  Rest.liftedBlock (rest_l10ecb2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ecb2 x hx)

theorem rest_l10ecc3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ecc3 bytes_l10ecc3) (entryMap (live .l10ecc3))
      9 0x10ecc3 bytes_l10ecc3 b_l10ecc3 := by
  have f0 : InstrSpec 0x10ecc3 [0xC6, 0x43, 0x50, 0x00] (StorePre 0x10ecc3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x10ecc3 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x10ecc3 (.base 3 (.d8 0x50)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x10ecc3 (.base 3 (.d8 0x50)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x10ecc3 (.base 3 (.d8 0x50)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10ecc7 [0x48, 0x81, 0xC4, 0xE8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ecc7) (addR64Imm32Effect 0x10ecc7 4 0xe8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x10ecc7 4 0xe8).toInstrSpec (add_r64_imm32_effect_step 0x10ecc7 0x48 0xc4 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10ecce [0x5B] (PopPre 0x10ecce) (popR64Effect 0x10ecce 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10ecce 1 3).toInstrSpec (pop_r64_effect_step 0x10ecce 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10eccf [0x41, 0x5C] (PopPre 0x10eccf) (popR64Effect 0x10eccf 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10eccf 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10eccf 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10ecd1 [0x41, 0x5D] (PopPre 0x10ecd1) (popR64Effect 0x10ecd1 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10ecd1 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10ecd1 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10ecd3 [0x41, 0x5E] (PopPre 0x10ecd3) (popR64Effect 0x10ecd3 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10ecd3 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10ecd3 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10ecd5 [0x41, 0x5F] (PopPre 0x10ecd5) (popR64Effect 0x10ecd5 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10ecd5 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10ecd5 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x10ecd7 [0x5D] (PopPre 0x10ecd7) (popR64Effect 0x10ecd7 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10ecd7 1 5).toInstrSpec (pop_r64_effect_step 0x10ecd7 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x10ecd8 [0xC3] (RetPre 0x10ecd8) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10ecd8).toInstrSpec (ret_effect_step 0x10ecd8) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecc7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecce) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 56), (4, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eccf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 56), (4, 60), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecd1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 56), (4, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecd3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 56), (4, 66), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 62), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecd5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 56), (4, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 62), (14, 65), (15, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecd7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 56), (4, 72), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 62), (14, 65), (15, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecd8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 75) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 56), (4, 75), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 62), (14, 65), (15, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l10ecc3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ecc3 :=
  Rest.liftedBlock (rest_l10ecc3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ecc3 x hx)

section Steps

variable (code : CodeMap)
    (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64)
    (cf pf af zf sf of : Bool) (df : BitVec 1)
    (xmm0 xmm1 xmm2 xmm3 xmm4 xmm5 xmm6 xmm7 xmm8 xmm9 xmm10 xmm11 xmm12 xmm13 xmm14 xmm15 : BitVec 128)
    (mxcsr : BitVec 32) (st0 st1 st2 st3 st4 st5 st6 st7 : BitVec 80) (fsw : BitVec 16)
    (fcc : BitVec 4) (ftw fcw : BitVec 16) (fpuPtr : BitVec 171) (mem : Ram)

set_option hygiene false in
local notation "args" =>
  (#v[⟨64, rax⟩, ⟨64, rcx⟩, ⟨64, rdx⟩, ⟨64, rbx⟩, ⟨64, rsp⟩, ⟨64, rbp⟩, ⟨64, rsi⟩, ⟨64, rdi⟩, ⟨64, r8⟩, ⟨64, r9⟩, ⟨64, r10⟩, ⟨64, r11⟩, ⟨64, r12⟩, ⟨64, r13⟩, ⟨64, r14⟩, ⟨64, r15⟩] : Vector Value 16) ++
  (#v[.ofBool cf, .ofBool pf, .ofBool af, .ofBool zf, .ofBool sf, .ofBool of, ⟨1, df⟩] : Vector Value 7) ++
  (#v[⟨128, xmm0⟩, ⟨128, xmm1⟩, ⟨128, xmm2⟩, ⟨128, xmm3⟩, ⟨128, xmm4⟩, ⟨128, xmm5⟩, ⟨128, xmm6⟩, ⟨128, xmm7⟩, ⟨128, xmm8⟩, ⟨128, xmm9⟩, ⟨128, xmm10⟩, ⟨128, xmm11⟩, ⟨128, xmm12⟩, ⟨128, xmm13⟩, ⟨128, xmm14⟩, ⟨128, xmm15⟩, ⟨32, mxcsr⟩, ⟨80, st0⟩, ⟨80, st1⟩, ⟨80, st2⟩, ⟨80, st3⟩, ⟨80, st4⟩, ⟨80, st5⟩, ⟨80, st6⟩, ⟨80, st7⟩, ⟨16, fsw⟩, ⟨4, fcc⟩, ⟨16, ftw⟩, ⟨16, fcw⟩, ⟨171, fpuPtr⟩] : Vector Value 30)

theorem_by block_l10ecb2_eval :
    program.runBlock (dialect code) ⟨.l10ecb2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10ecc3_eval :
    program.runBlock (dialect code) ⟨.l10ecc3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Ecdh.LIR
