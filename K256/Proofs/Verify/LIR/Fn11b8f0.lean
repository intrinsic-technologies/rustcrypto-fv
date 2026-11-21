import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

theorem rest_l11b8f0_7 [Bindings] (code : CodeMap) :
    Rest (n := 364) code lifted (codeRange 0x11b8f0 bytes_l11b8f0) [(0, 328), (1, 347), (2, 337), (3, 351), (4, 65), (5, 113), (6, 324), (7, 362), (8, 308), (9, 304), (10, 240), (11, 299), (12, 354), (13, 221), (14, 345), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x11bac7 bytes_l11b8f0_7 b_l11b8f0_7 := by
  have f140 : InstrSpec 0x11bac7 [0x48, 0x8D, 0x74, 0x24, 0x28] (fun s => s.RIP = 0x11bac7) (leaR64Effect 0x11bac7 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11bac7 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (lea_r64_effect_step 0x11bac7 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) pre_rip
  have f141 : InstrSpec 0x11bacc [0x48, 0xC7, 0xC2, 0x80, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x11bacc) (movR64Imm32Effect 0x11bacc 2 0x202180)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x11bacc 2 0x202180).toInstrSpec (mov_r64_imm32_effect_step 0x11bacc 0x48 0xc2 (by decide) (by decide) (by decide) 0x202180) pre_rip
  have f142 : InstrSpec 0x11bad3 [0x48, 0xC7, 0xC1, 0xA0, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x11bad3) (movR64Imm32Effect 0x11bad3 1 0x2021a0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x11bad3 1 0x2021a0).toInstrSpec (mov_r64_imm32_effect_step 0x11bad3 0x48 0xc1 (by decide) (by decide) (by decide) 0x2021a0) pre_rip
  have f143 : InstrSpec 0x11bada [0xE8, 0xD1, 0x4E, 0xFF, 0xFF] (PushPre 0x11bada 5) (callEffect (fun _ => 0x1109b0) 0x11badf)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11bada 0x1109b0 0x11badf).toInstrSpec (call_rel32_effect_step 0x11bada 0xffff4ed1 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 364) (RestInside.out (n := 364) f140 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 365) (ρ' := [(0, 328), (1, 347), (2, 337), (3, 351), (4, 65), (5, 113), (6, 364), (7, 362), (8, 308), (9, 304), (10, 240), (11, 299), (12, 354), (13, 221), (14, 345), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bacc) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 366) (RestInside.out (n := 366) f141 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 367) (ρ' := [(0, 328), (1, 347), (2, 366), (3, 351), (4, 65), (5, 113), (6, 364), (7, 362), (8, 308), (9, 304), (10, 240), (11, 299), (12, 354), (13, 221), (14, 345), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bad3) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 368) (RestInside.out (n := 368) f142 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 369) (ρ' := [(0, 328), (1, 368), (2, 366), (3, 351), (4, 65), (5, 113), (6, 364), (7, 362), (8, 308), (9, 304), (10, 240), (11, 299), (12, 354), (13, 221), (14, 345), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bada) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 370) (RestInside.out (n := 370) f143 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 371) (ρ' := [(0, 328), (1, 368), (2, 366), (3, 351), (4, 370), (5, 113), (6, 364), (7, 362), (8, 308), (9, 304), (10, 240), (11, 299), (12, 354), (13, 221), (14, 345), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109b0) f143 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 372) (by decide) (by decide) rfl rfl

theorem rest_l11b8f0_6 [Bindings] (code : CodeMap) :
    Rest (n := 322) code lifted (codeRange 0x11b8f0 bytes_l11b8f0) [(0, 319), (1, 275), (2, 320), (3, 313), (4, 65), (5, 113), (6, 290), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 315), (22, 22), (39, 39), (50, 50), (51, 51)]
      24 0x11ba76 bytes_l11b8f0_6 b_l11b8f0_6 := by
  have f120 : InstrSpec 0x11ba76 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x11ba76) (movR64R64Effect 0x11ba76 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x11ba76 1 2).toInstrSpec (mov_r64_r64_effect_step 0x11ba76 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f121 : InstrSpec 0x11ba79 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11ba79) (movR64R64Effect 0x11ba79 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11ba79 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11ba79 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x11ba7c [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x11ba7c) (movR64R64Effect 0x11ba7c 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11ba7c 0 8).toInstrSpec (mov_r64_r64_effect_step 0x11ba7c 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f123 : InstrSpec 0x11ba7f [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x11ba7f) (mulR64Effect 0x11ba7f 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11ba7f 12).toInstrSpec (mul_r64_effect_step 0x11ba7f 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x11ba82 [0x4D, 0x01, 0xDF] (fun s => s.RIP = 0x11ba82) (addR64R64Effect 0x11ba82 15 11)
      [.gpr 15, .gpr 11] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11ba82 15 11).toInstrSpec (add_r64_r64_effect_step 0x11ba82 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f125 : InstrSpec 0x11ba85 [0x4C, 0x11, 0xCB] (fun s => s.RIP = 0x11ba85) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba85 3 9))
      [.gpr 3, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11ba85 3 9).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11ba85 0x4c 0xcb c (by decide) (by decide))) pre_rip
  have f126 : InstrSpec 0x11ba88 [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x11ba88) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ba88 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x11ba88 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x11ba88 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f127 : InstrSpec 0x11ba8c [0x49, 0x01, 0xF7] (fun s => s.RIP = 0x11ba8c) (addR64R64Effect 0x11ba8c 15 6)
      [.gpr 15, .gpr 6] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11ba8c 15 6).toInstrSpec (add_r64_r64_effect_step 0x11ba8c 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f128 : InstrSpec 0x11ba8f [0x48, 0x11, 0xCB] (fun s => s.RIP = 0x11ba8f) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba8f 3 1))
      [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11ba8f 3 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11ba8f 0x48 0xcb c (by decide) (by decide))) pre_rip
  have f129 : InstrSpec 0x11ba92 [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x11ba92) (movR64R64Effect 0x11ba92 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x11ba92 14 7).toInstrSpec (mov_r64_r64_effect_step 0x11ba92 0x49 0xfe (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x11ba95 [0x0F, 0x92, 0xC1] (fun s => s.RIP = 0x11ba95) (atFlags (condHolds 2) (setccR8Effect 0x11ba95 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x11ba95 3 1 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x11ba95 2 0xc1 (by decide) (by decide) c)) pre_rip
  have f131 : InstrSpec 0x11ba98 [0x44, 0x0F, 0xB6, 0xE1] (fun s => s.RIP = 0x11ba98) (movzxR32R8Effect 0x11ba98 4 12 1)
      [.gpr 1] [] [.reg 12, .rip] :=
    (movzxR32R8Effect_footprint 0x11ba98 4 12 1).toInstrSpec (movzx_r32_r8_rex_effect_step 0x11ba98 0x44 (by decide) 0xe1 (by decide)) pre_rip
  have f132 : InstrSpec 0x11ba9c [0x48, 0x01, 0xC3] (fun s => s.RIP = 0x11ba9c) (addR64R64Effect 0x11ba9c 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11ba9c 3 0).toInstrSpec (add_r64_r64_effect_step 0x11ba9c 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f133 : InstrSpec 0x11ba9f [0x49, 0x11, 0xD4] (fun s => s.RIP = 0x11ba9f) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba9f 12 2))
      [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11ba9f 12 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11ba9f 0x49 0xd4 c (by decide) (by decide))) pre_rip
  have f134 : InstrSpec 0x11baa2 [0x48, 0x89, 0x5C, 0x24, 0x28] (StorePre 0x11baa2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11baa2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11baa2 3 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11baa2 3 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x11baa2 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f135 : InstrSpec 0x11baa7 [0x4C, 0x89, 0x64, 0x24, 0x30] (StorePre 0x11baa7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11baa7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11baa7 12 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11baa7 12 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x11baa7 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f136 : InstrSpec 0x11baac [0x49, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x11baac) (shrR64Effect 0x11baac 4 15 63)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x11baac 4 15 63).toInstrSpec (shr_r64_imm8_effect_step 0x11baac 0x49 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f137 : InstrSpec 0x11bab0 [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x11bab0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11bab0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11bab0 (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11bab0 (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x11bab0 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f138 : InstrSpec 0x11bab9 [0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00] (StorePre 0x11bab9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11bab9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11bab9 (.sib 4 none 0 (.d8 0x40)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11bab9 (.sib 4 none 0 (.d8 0x40)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x11bab9 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f139 : InstrSpec 0x11bac2 [0x48, 0x8D, 0x7C, 0x24, 0x48] (fun s => s.RIP = 0x11bac2) (leaR64Effect 0x11bac2 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11bac2 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x11bac2 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 322) (RestInside.out (n := 322) f120 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 323) (ρ' := [(0, 319), (1, 322), (2, 320), (3, 313), (4, 65), (5, 113), (6, 290), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 315), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba79) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 324) (RestInside.out (n := 324) f121 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 325) (ρ' := [(0, 319), (1, 322), (2, 320), (3, 313), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 315), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba7c) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 326) (RestInside.out (n := 326) f122 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 327) (ρ' := [(0, 326), (1, 322), (2, 320), (3, 313), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 315), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba7f) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 328) (RestInside.out (n := 328) f123 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 329) f123 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 330) (ρ' := [(0, 328), (1, 322), (2, 329), (3, 313), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 315), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba82) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 331) (RestInside.out (n := 331) f124 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 332) f124 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 333) (ρ' := [(0, 328), (1, 322), (2, 329), (3, 313), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 331), (16, 332), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba85) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 334) (RestInside.out (n := 334) f125 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 335) f125 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11ba85 3 9 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 336) (ρ' := [(0, 328), (1, 322), (2, 329), (3, 334), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 331), (16, 335), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba88) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 337) (RestInside.out (n := 337) f126 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 338) (ρ' := [(0, 328), (1, 322), (2, 337), (3, 334), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 331), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba8c) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 339) (RestInside.out (n := 339) f127 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 340) f127 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 341) (ρ' := [(0, 328), (1, 322), (2, 337), (3, 334), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 339), (16, 340), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba8f) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 342) (RestInside.out (n := 342) f128 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 343) f128 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11ba8f 3 1 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 344) (ρ' := [(0, 328), (1, 322), (2, 337), (3, 342), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 339), (16, 343), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba92) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 345) (RestInside.out (n := 345) f129 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 346) (ρ' := [(0, 328), (1, 322), (2, 337), (3, 342), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 345), (15, 339), (16, 343), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba95) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 347) (RestInside.out (n := 347) f130 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 348) (ρ' := [(0, 328), (1, 347), (2, 337), (3, 342), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 345), (15, 339), (16, 343), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba98) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 349) (RestInside.out (n := 349) f131 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 350) (ρ' := [(0, 328), (1, 347), (2, 337), (3, 342), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 349), (13, 221), (14, 345), (15, 339), (16, 343), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba9c) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 351) (RestInside.out (n := 351) f132 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 352) f132 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 353) (ρ' := [(0, 328), (1, 347), (2, 337), (3, 351), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 349), (13, 221), (14, 345), (15, 339), (16, 352), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba9f) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 354) (RestInside.out (n := 354) f133 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 355) (ρ' := [(0, 328), (1, 347), (2, 337), (3, 351), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 354), (13, 221), (14, 345), (15, 339), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11baa2) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 356) (RestInside.exec (n := 356) (ρ' := [(0, 328), (1, 347), (2, 337), (3, 351), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 354), (13, 221), (14, 345), (15, 339), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11baa7) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 357) (RestInside.exec (n := 357) (ρ' := [(0, 328), (1, 347), (2, 337), (3, 351), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 354), (13, 221), (14, 345), (15, 339), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11baac) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 358) (RestInside.out (n := 358) f136 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 359) (ρ' := [(0, 328), (1, 347), (2, 337), (3, 351), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 354), (13, 221), (14, 345), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bab0) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 360) (RestInside.exec (n := 360) (ρ' := [(0, 328), (1, 347), (2, 337), (3, 351), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 354), (13, 221), (14, 345), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bab9) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 361) (RestInside.exec (n := 361) (ρ' := [(0, 328), (1, 347), (2, 337), (3, 351), (4, 65), (5, 113), (6, 324), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 354), (13, 221), (14, 345), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bac2) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 362) (RestInside.out (n := 362) f139 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 363) (ρ' := [(0, 328), (1, 347), (2, 337), (3, 351), (4, 65), (5, 113), (6, 324), (7, 362), (8, 308), (9, 304), (10, 240), (11, 299), (12, 354), (13, 221), (14, 345), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bac7) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b8f0_7 code

theorem rest_l11b8f0_5 [Bindings] (code : CodeMap) :
    Rest (n := 275) code lifted (codeRange 0x11b8f0 bytes_l11b8f0) [(0, 273), (1, 219), (2, 263), (3, 258), (4, 65), (5, 113), (6, 267), (7, 7), (8, 150), (9, 253), (10, 240), (11, 270), (12, 212), (13, 221), (14, 234), (15, 225), (16, 271), (22, 22), (39, 39), (50, 50), (51, 51)]
      44 0x11ba38 bytes_l11b8f0_5 b_l11b8f0_5 := by
  have f100 : InstrSpec 0x11ba38 [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x11ba38) (movzxR32R8Effect 0x11ba38 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x11ba38 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x11ba38 0xc8 (by decide) (by decide)) pre_rip
  have f101 : InstrSpec 0x11ba3b [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x11ba3b) (movR64R64Effect 0x11ba3b 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11ba3b 0 5).toInstrSpec (mov_r64_r64_effect_step 0x11ba3b 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x11ba3e [0x49, 0xF7, 0xE7] (fun s => s.RIP = 0x11ba3e) (mulR64Effect 0x11ba3e 15)
      [.gpr 15, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11ba3e 15).toInstrSpec (mul_r64_effect_step 0x11ba3e 0x49 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x11ba41 [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x11ba41) (movR64R64Effect 0x11ba41 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x11ba41 9 0).toInstrSpec (mov_r64_r64_effect_step 0x11ba41 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f104 : InstrSpec 0x11ba44 [0x49, 0x01, 0xF1] (fun s => s.RIP = 0x11ba44) (addR64R64Effect 0x11ba44 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11ba44 9 6).toInstrSpec (add_r64_r64_effect_step 0x11ba44 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x11ba47 [0x49, 0x11, 0xD3] (fun s => s.RIP = 0x11ba47) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba47 11 2))
      [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11ba47 11 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11ba47 0x49 0xd3 c (by decide) (by decide))) pre_rip
  have f106 : InstrSpec 0x11ba4a [0x40, 0x0F, 0x92, 0xC6] (fun s => s.RIP = 0x11ba4a) (atFlags (condHolds 2) (setccR8Effect 0x11ba4a 4 6))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .rip] :=
    (setccR8Effect_footprint 0x11ba4a 4 6 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11ba4a 2 0x40 (by decide) 0xc6 (by decide) c)) pre_rip
  have f107 : InstrSpec 0x11ba4e [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x11ba4e) (movR64R64Effect 0x11ba4e 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11ba4e 0 13).toInstrSpec (mov_r64_r64_effect_step 0x11ba4e 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x11ba51 [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x11ba51) (mulR64Effect 0x11ba51 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11ba51 12).toInstrSpec (mul_r64_effect_step 0x11ba51 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x11ba54 [0x4C, 0x01, 0xC8] (fun s => s.RIP = 0x11ba54) (addR64R64Effect 0x11ba54 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11ba54 0 9).toInstrSpec (add_r64_r64_effect_step 0x11ba54 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x11ba57 [0x49, 0x11, 0xD3] (fun s => s.RIP = 0x11ba57) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba57 11 2))
      [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11ba57 11 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11ba57 0x49 0xd3 c (by decide) (by decide))) pre_rip
  have f111 : InstrSpec 0x11ba5a [0x44, 0x0F, 0xB6, 0xCE] (fun s => s.RIP = 0x11ba5a) (movzxR32R8Effect 0x11ba5a 4 9 6)
      [.gpr 6] [] [.reg 9, .rip] :=
    (movzxR32R8Effect_footprint 0x11ba5a 4 9 6).toInstrSpec (movzx_r32_r8_rex_effect_step 0x11ba5a 0x44 (by decide) 0xce (by decide)) pre_rip
  have f112 : InstrSpec 0x11ba5e [0x49, 0x11, 0xC9] (fun s => s.RIP = 0x11ba5e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba5e 9 1))
      [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11ba5e 9 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11ba5e 0x49 0xc9 c (by decide) (by decide))) pre_rip
  have f113 : InstrSpec 0x11ba61 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x11ba61) (movR64R64Effect 0x11ba61 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11ba61 0 3).toInstrSpec (mov_r64_r64_effect_step 0x11ba61 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x11ba64 [0x49, 0x89, 0xD8] (fun s => s.RIP = 0x11ba64) (movR64R64Effect 0x11ba64 8 3)
      [.gpr 3] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x11ba64 8 3).toInstrSpec (mov_r64_r64_effect_step 0x11ba64 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x11ba67 [0x49, 0xF7, 0xE7] (fun s => s.RIP = 0x11ba67) (mulR64Effect 0x11ba67 15)
      [.gpr 15, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11ba67 15).toInstrSpec (mul_r64_effect_step 0x11ba67 0x49 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f116 : InstrSpec 0x11ba6a [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x11ba6a) (movR64R64Effect 0x11ba6a 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x11ba6a 3 2).toInstrSpec (mov_r64_r64_effect_step 0x11ba6a 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x11ba6d [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x11ba6d) (movR64R64Effect 0x11ba6d 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x11ba6d 15 0).toInstrSpec (mov_r64_r64_effect_step 0x11ba6d 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x11ba70 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x11ba70) (movR64R64Effect 0x11ba70 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11ba70 0 5).toInstrSpec (mov_r64_r64_effect_step 0x11ba70 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f119 : InstrSpec 0x11ba73 [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x11ba73) (mulR64Effect 0x11ba73 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11ba73 12).toInstrSpec (mul_r64_effect_step 0x11ba73 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 275) (RestInside.out (n := 275) f100 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 276) (ρ' := [(0, 273), (1, 275), (2, 263), (3, 258), (4, 65), (5, 113), (6, 267), (7, 7), (8, 150), (9, 253), (10, 240), (11, 270), (12, 212), (13, 221), (14, 234), (15, 225), (16, 271), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba3b) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 277) (RestInside.out (n := 277) f101 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 278) (ρ' := [(0, 277), (1, 275), (2, 263), (3, 258), (4, 65), (5, 113), (6, 267), (7, 7), (8, 150), (9, 253), (10, 240), (11, 270), (12, 212), (13, 221), (14, 234), (15, 225), (16, 271), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba3e) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 279) (RestInside.out (n := 279) f102 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 280) f102 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 281) (ρ' := [(0, 279), (1, 275), (2, 280), (3, 258), (4, 65), (5, 113), (6, 267), (7, 7), (8, 150), (9, 253), (10, 240), (11, 270), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba41) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 282) (RestInside.out (n := 282) f103 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 283) (ρ' := [(0, 279), (1, 275), (2, 280), (3, 258), (4, 65), (5, 113), (6, 267), (7, 7), (8, 150), (9, 282), (10, 240), (11, 270), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba44) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 284) (RestInside.out (n := 284) f104 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 285) f104 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 286) (ρ' := [(0, 279), (1, 275), (2, 280), (3, 258), (4, 65), (5, 113), (6, 267), (7, 7), (8, 150), (9, 284), (10, 240), (11, 270), (12, 212), (13, 221), (14, 234), (15, 225), (16, 285), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba47) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 287) (RestInside.out (n := 287) f105 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 288) f105 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11ba47 11 2 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 289) (ρ' := [(0, 279), (1, 275), (2, 280), (3, 258), (4, 65), (5, 113), (6, 267), (7, 7), (8, 150), (9, 284), (10, 240), (11, 287), (12, 212), (13, 221), (14, 234), (15, 225), (16, 288), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba4a) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 290) (RestInside.out (n := 290) f106 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 291) (ρ' := [(0, 279), (1, 275), (2, 280), (3, 258), (4, 65), (5, 113), (6, 290), (7, 7), (8, 150), (9, 284), (10, 240), (11, 287), (12, 212), (13, 221), (14, 234), (15, 225), (16, 288), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba4e) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 292) (RestInside.out (n := 292) f107 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 293) (ρ' := [(0, 292), (1, 275), (2, 280), (3, 258), (4, 65), (5, 113), (6, 290), (7, 7), (8, 150), (9, 284), (10, 240), (11, 287), (12, 212), (13, 221), (14, 234), (15, 225), (16, 288), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba51) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 294) (RestInside.out (n := 294) f108 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 295) f108 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 296) (ρ' := [(0, 294), (1, 275), (2, 295), (3, 258), (4, 65), (5, 113), (6, 290), (7, 7), (8, 150), (9, 284), (10, 240), (11, 287), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba54) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.out (n := 297) f109 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 298) (ρ' := [(1, 275), (2, 295), (3, 258), (4, 65), (5, 113), (6, 290), (7, 7), (8, 150), (9, 284), (10, 240), (11, 287), (12, 212), (13, 221), (14, 234), (15, 225), (16, 297), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba57) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 299) (RestInside.out (n := 299) f110 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 300) f110 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11ba57 11 2 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 301) (ρ' := [(1, 275), (2, 295), (3, 258), (4, 65), (5, 113), (6, 290), (7, 7), (8, 150), (9, 284), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 225), (16, 300), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba5a) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f111 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(1, 275), (2, 295), (3, 258), (4, 65), (5, 113), (6, 290), (7, 7), (8, 150), (9, 302), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 225), (16, 300), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba5e) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f112 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(1, 275), (2, 295), (3, 258), (4, 65), (5, 113), (6, 290), (7, 7), (8, 150), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba61) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.out (n := 306) f113 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 307) (ρ' := [(0, 306), (1, 275), (2, 295), (3, 258), (4, 65), (5, 113), (6, 290), (7, 7), (8, 150), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba64) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 308) (RestInside.out (n := 308) f114 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 309) (ρ' := [(0, 306), (1, 275), (2, 295), (3, 258), (4, 65), (5, 113), (6, 290), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba67) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 310) (RestInside.out (n := 310) f115 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 311) f115 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 312) (ρ' := [(0, 310), (1, 275), (2, 311), (3, 258), (4, 65), (5, 113), (6, 290), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba6a) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 313) (RestInside.out (n := 313) f116 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 314) (ρ' := [(0, 310), (1, 275), (2, 311), (3, 313), (4, 65), (5, 113), (6, 290), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba6d) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 315) (RestInside.out (n := 315) f117 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 316) (ρ' := [(0, 310), (1, 275), (2, 311), (3, 313), (4, 65), (5, 113), (6, 290), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 315), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba70) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 317) (RestInside.out (n := 317) f118 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 318) (ρ' := [(0, 317), (1, 275), (2, 311), (3, 313), (4, 65), (5, 113), (6, 290), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 315), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba73) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 319) (RestInside.out (n := 319) f119 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 320) f119 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 321) (ρ' := [(0, 319), (1, 275), (2, 320), (3, 313), (4, 65), (5, 113), (6, 290), (7, 7), (8, 308), (9, 304), (10, 240), (11, 299), (12, 212), (13, 221), (14, 234), (15, 315), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba76) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b8f0_6 code

theorem rest_l11b8f0_4 [Bindings] (code : CodeMap) :
    Rest (n := 227) code lifted (codeRange 0x11b8f0 bytes_l11b8f0) [(0, 223), (1, 219), (2, 192), (3, 202), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 216), (11, 205), (12, 212), (13, 221), (14, 159), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]
      64 0x11b9f6 bytes_l11b8f0_4 b_l11b8f0_4 := by
  have f80 : InstrSpec 0x11b9f6 [0x48, 0xF7, 0xE6] (fun s => s.RIP = 0x11b9f6) (mulR64Effect 0x11b9f6 6)
      [.gpr 6, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b9f6 6).toInstrSpec (mul_r64_effect_step 0x11b9f6 0x48 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x11b9f9 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x11b9f9) (movR64R64Effect 0x11b9f9 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11b9f9 6 2).toInstrSpec (mov_r64_r64_effect_step 0x11b9f9 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x11b9fc [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x11b9fc) (movR64R64Effect 0x11b9fc 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x11b9fc 14 0).toInstrSpec (mov_r64_r64_effect_step 0x11b9fc 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x11b9ff [0x49, 0x01, 0xDE] (fun s => s.RIP = 0x11b9ff) (addR64R64Effect 0x11b9ff 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b9ff 14 3).toInstrSpec (add_r64_r64_effect_step 0x11b9ff 0x49 0xde (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x11ba02 [0x4C, 0x11, 0xDE] (fun s => s.RIP = 0x11ba02) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba02 6 11))
      [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11ba02 6 11).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11ba02 0x4c 0xde c (by decide) (by decide))) pre_rip
  have f85 : InstrSpec 0x11ba05 [0x41, 0x0F, 0x92, 0xC2] (fun s => s.RIP = 0x11ba05) (atFlags (condHolds 2) (setccR8Effect 0x11ba05 4 10))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .rip] :=
    (setccR8Effect_footprint 0x11ba05 4 10 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11ba05 2 0x41 (by decide) 0xc2 (by decide) c)) pre_rip
  have f86 : InstrSpec 0x11ba09 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x11ba09 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ba09 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ba09 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11ba09 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11ba09 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f87 : InstrSpec 0x11ba0e [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x11ba0e) (mulR64Effect 0x11ba0e 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11ba0e 12).toInstrSpec (mul_r64_effect_step 0x11ba0e 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x11ba11 [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x11ba11) (movR64R64Effect 0x11ba11 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x11ba11 9 2).toInstrSpec (mov_r64_r64_effect_step 0x11ba11 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x11ba14 [0x45, 0x0F, 0xB6, 0xDA] (fun s => s.RIP = 0x11ba14) (movzxR32R8Effect 0x11ba14 4 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movzxR32R8Effect_footprint 0x11ba14 4 11 10).toInstrSpec (movzx_r32_r8_rex_effect_step 0x11ba14 0x45 (by decide) 0xda (by decide)) pre_rip
  have f90 : InstrSpec 0x11ba18 [0x4C, 0x01, 0xF0] (fun s => s.RIP = 0x11ba18) (addR64R64Effect 0x11ba18 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11ba18 0 14).toInstrSpec (add_r64_r64_effect_step 0x11ba18 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x11ba1b [0x49, 0x11, 0xF1] (fun s => s.RIP = 0x11ba1b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba1b 9 6))
      [.gpr 9, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11ba1b 9 6).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11ba1b 0x49 0xf1 c (by decide) (by decide))) pre_rip
  have f92 : InstrSpec 0x11ba1e [0x49, 0x11, 0xCB] (fun s => s.RIP = 0x11ba1e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba1e 11 1))
      [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11ba1e 11 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11ba1e 0x49 0xcb c (by decide) (by decide))) pre_rip
  have f93 : InstrSpec 0x11ba21 [0x48, 0x8B, 0x5C, 0x24, 0x10] (LoadPre 0x11ba21 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11ba21 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ba21 3 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x11ba21 3 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x11ba21 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f94 : InstrSpec 0x11ba26 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x11ba26) (movR64R64Effect 0x11ba26 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11ba26 0 3).toInstrSpec (mov_r64_r64_effect_step 0x11ba26 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x11ba29 [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x11ba29) (mulR64Effect 0x11ba29 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11ba29 8).toInstrSpec (mul_r64_effect_step 0x11ba29 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f96 : InstrSpec 0x11ba2c [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11ba2c) (movR64R64Effect 0x11ba2c 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11ba2c 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11ba2c 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f97 : InstrSpec 0x11ba2f [0x4C, 0x01, 0xCE] (fun s => s.RIP = 0x11ba2f) (addR64R64Effect 0x11ba2f 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11ba2f 6 9).toInstrSpec (add_r64_r64_effect_step 0x11ba2f 0x4c 0xce (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x11ba32 [0x49, 0x11, 0xD3] (fun s => s.RIP = 0x11ba32) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba32 11 2))
      [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11ba32 11 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11ba32 0x49 0xd3 c (by decide) (by decide))) pre_rip
  have f99 : InstrSpec 0x11ba35 [0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x11ba35) (atFlags (condHolds 2) (setccR8Effect 0x11ba35 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x11ba35 3 0 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x11ba35 2 0xc0 (by decide) (by decide) c)) pre_rip
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f80 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 228) f80 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 229) (ρ' := [(0, 227), (1, 219), (2, 228), (3, 202), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 216), (11, 205), (12, 212), (13, 221), (14, 159), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9f9) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 230) (RestInside.out (n := 230) f81 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 231) (ρ' := [(0, 227), (1, 219), (2, 228), (3, 202), (4, 65), (5, 113), (6, 230), (7, 7), (8, 150), (9, 136), (10, 216), (11, 205), (12, 212), (13, 221), (14, 159), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9fc) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f82 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 233) (ρ' := [(0, 227), (1, 219), (2, 228), (3, 202), (4, 65), (5, 113), (6, 230), (7, 7), (8, 150), (9, 136), (10, 216), (11, 205), (12, 212), (13, 221), (14, 232), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9ff) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f83 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 235) f83 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 236) (ρ' := [(0, 227), (1, 219), (2, 228), (3, 202), (4, 65), (5, 113), (6, 230), (7, 7), (8, 150), (9, 136), (10, 216), (11, 205), (12, 212), (13, 221), (14, 234), (15, 225), (16, 235), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba02) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 237) (RestInside.out (n := 237) f84 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 238) f84 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11ba02 6 11 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 239) (ρ' := [(0, 227), (1, 219), (2, 228), (3, 202), (4, 65), (5, 113), (6, 237), (7, 7), (8, 150), (9, 136), (10, 216), (11, 205), (12, 212), (13, 221), (14, 234), (15, 225), (16, 238), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba05) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f85 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 241) (ρ' := [(0, 227), (1, 219), (2, 228), (3, 202), (4, 65), (5, 113), (6, 237), (7, 7), (8, 150), (9, 136), (10, 240), (11, 205), (12, 212), (13, 221), (14, 234), (15, 225), (16, 238), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba09) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f86 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 243) (ρ' := [(0, 242), (1, 219), (2, 228), (3, 202), (4, 65), (5, 113), (6, 237), (7, 7), (8, 150), (9, 136), (10, 240), (11, 205), (12, 212), (13, 221), (14, 234), (15, 225), (16, 238), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba0e) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f87 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 245) f87 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 246) (ρ' := [(0, 244), (1, 219), (2, 245), (3, 202), (4, 65), (5, 113), (6, 237), (7, 7), (8, 150), (9, 136), (10, 240), (11, 205), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba11) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f88 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 244), (1, 219), (2, 245), (3, 202), (4, 65), (5, 113), (6, 237), (7, 7), (8, 150), (9, 247), (10, 240), (11, 205), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba14) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 249) (RestInside.out (n := 249) f89 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 250) (ρ' := [(0, 244), (1, 219), (2, 245), (3, 202), (4, 65), (5, 113), (6, 237), (7, 7), (8, 150), (9, 247), (10, 240), (11, 249), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba18) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f90 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(1, 219), (2, 245), (3, 202), (4, 65), (5, 113), (6, 237), (7, 7), (8, 150), (9, 247), (10, 240), (11, 249), (12, 212), (13, 221), (14, 234), (15, 225), (16, 251), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba1b) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f91 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 254) f91 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11ba1b 9 6 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 255) (ρ' := [(1, 219), (2, 245), (3, 202), (4, 65), (5, 113), (6, 237), (7, 7), (8, 150), (9, 253), (10, 240), (11, 249), (12, 212), (13, 221), (14, 234), (15, 225), (16, 254), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba1e) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 256) (RestInside.out (n := 256) f92 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 257) (ρ' := [(1, 219), (2, 245), (3, 202), (4, 65), (5, 113), (6, 237), (7, 7), (8, 150), (9, 253), (10, 240), (11, 256), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba21) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 258) (RestInside.out (n := 258) f93 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 259) (ρ' := [(1, 219), (2, 245), (3, 258), (4, 65), (5, 113), (6, 237), (7, 7), (8, 150), (9, 253), (10, 240), (11, 256), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba26) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 260) (RestInside.out (n := 260) f94 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 261) (ρ' := [(0, 260), (1, 219), (2, 245), (3, 258), (4, 65), (5, 113), (6, 237), (7, 7), (8, 150), (9, 253), (10, 240), (11, 256), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba29) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f95 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 263) f95 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 264) (ρ' := [(0, 262), (1, 219), (2, 263), (3, 258), (4, 65), (5, 113), (6, 237), (7, 7), (8, 150), (9, 253), (10, 240), (11, 256), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba2c) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f96 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 266) (ρ' := [(0, 262), (1, 219), (2, 263), (3, 258), (4, 65), (5, 113), (6, 265), (7, 7), (8, 150), (9, 253), (10, 240), (11, 256), (12, 212), (13, 221), (14, 234), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba2f) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 267) (RestInside.out (n := 267) f97 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 268) f97 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 269) (ρ' := [(0, 262), (1, 219), (2, 263), (3, 258), (4, 65), (5, 113), (6, 267), (7, 7), (8, 150), (9, 253), (10, 240), (11, 256), (12, 212), (13, 221), (14, 234), (15, 225), (16, 268), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba32) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 270) (RestInside.out (n := 270) f98 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 271) f98 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11ba32 11 2 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 272) (ρ' := [(0, 262), (1, 219), (2, 263), (3, 258), (4, 65), (5, 113), (6, 267), (7, 7), (8, 150), (9, 253), (10, 240), (11, 270), (12, 212), (13, 221), (14, 234), (15, 225), (16, 271), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba35) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 273) (RestInside.out (n := 273) f99 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 274) (ρ' := [(0, 273), (1, 219), (2, 263), (3, 258), (4, 65), (5, 113), (6, 267), (7, 7), (8, 150), (9, 253), (10, 240), (11, 270), (12, 212), (13, 221), (14, 234), (15, 225), (16, 271), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ba38) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b8f0_5 code

theorem rest_l11b8f0_3 [Bindings] (code : CodeMap) :
    Rest (n := 180) code lifted (codeRange 0x11b8f0 bytes_l11b8f0) [(1, 69), (2, 167), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 162), (12, 175), (13, 178), (14, 159), (15, 156), (22, 22), (39, 39), (50, 50), (51, 51)]
      84 0x11b9b2 bytes_l11b8f0_3 b_l11b8f0_3 := by
  have f60 : InstrSpec 0x11b9b2 [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x11b9b2) (movR64R64Effect 0x11b9b2 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b9b2 0 9).toInstrSpec (mov_r64_r64_effect_step 0x11b9b2 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x11b9b5 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x11b9b5) (mulR64Effect 0x11b9b5 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b9b5 1).toInstrSpec (mul_r64_effect_step 0x11b9b5 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x11b9b8 [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x11b9b8) (movR64R64Effect 0x11b9b8 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x11b9b8 11 2).toInstrSpec (mov_r64_r64_effect_step 0x11b9b8 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x11b9bb [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x11b9bb) (movR64R64Effect 0x11b9bb 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x11b9bb 3 0).toInstrSpec (mov_r64_r64_effect_step 0x11b9bb 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x11b9be [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x11b9be) (movR64R64Effect 0x11b9be 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b9be 0 5).toInstrSpec (mov_r64_r64_effect_step 0x11b9be 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x11b9c1 [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x11b9c1) (mulR64Effect 0x11b9c1 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b9c1 8).toInstrSpec (mul_r64_effect_step 0x11b9c1 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x11b9c4 [0x4C, 0x01, 0xE3] (fun s => s.RIP = 0x11b9c4) (addR64R64Effect 0x11b9c4 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b9c4 3 12).toInstrSpec (add_r64_r64_effect_step 0x11b9c4 0x4c 0xe3 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x11b9c7 [0x4D, 0x11, 0xEB] (fun s => s.RIP = 0x11b9c7) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b9c7 11 13))
      [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b9c7 11 13).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b9c7 0x4d 0xeb c (by decide) (by decide))) pre_rip
  have f68 : InstrSpec 0x11b9ca [0x41, 0x0F, 0x92, 0xC2] (fun s => s.RIP = 0x11b9ca) (atFlags (condHolds 2) (setccR8Effect 0x11b9ca 4 10))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .rip] :=
    (setccR8Effect_footprint 0x11b9ca 4 10 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11b9ca 2 0x41 (by decide) 0xc2 (by decide) c)) pre_rip
  have f69 : InstrSpec 0x11b9ce [0x48, 0x01, 0xC3] (fun s => s.RIP = 0x11b9ce) (addR64R64Effect 0x11b9ce 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b9ce 3 0).toInstrSpec (add_r64_r64_effect_step 0x11b9ce 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x11b9d1 [0x49, 0x11, 0xD3] (fun s => s.RIP = 0x11b9d1) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b9d1 11 2))
      [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b9d1 11 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b9d1 0x49 0xd3 c (by decide) (by decide))) pre_rip
  have f71 : InstrSpec 0x11b9d4 [0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x11b9d4) (atFlags (condHolds 2) (setccR8Effect 0x11b9d4 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x11b9d4 3 0 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x11b9d4 2 0xc0 (by decide) (by decide) c)) pre_rip
  have f72 : InstrSpec 0x11b9d7 [0x48, 0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x11b9d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11b9d7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b9d7 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11b9d7 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x11b9d7 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f73 : InstrSpec 0x11b9dc [0x4C, 0x8B, 0x61, 0x18] (LoadPre 0x11b9dc (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x11b9dc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b9dc 12 (.base 1 (.d8 0x18)))
      [.gpr 1] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x11b9dc 12 (.base 1 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x11b9dc 0x4c (by decide) 4 (.base 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f74 : InstrSpec 0x11b9e0 [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x11b9e0) (movzxR32R8Effect 0x11b9e0 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x11b9e0 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x11b9e0 0xc8 (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x11b9e3 [0x41, 0x80, 0xC2, 0xFF] (fun s => s.RIP = 0x11b9e3) (addR8Imm8Effect 0x11b9e3 4 10 0xff)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (addR8Imm8Effect_footprint 0x11b9e3 4 10 0xff).toInstrSpec (add_r8_imm8_rex_effect_step 0x11b9e3 0x41 0xc2 0xff (by decide) (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x11b9e7 [0x48, 0x83, 0xD1, 0x00] (fun s => s.RIP = 0x11b9e7) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11b9e7 1 0x0))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x11b9e7 1 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x11b9e7 0x48 0xd1 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f77 : InstrSpec 0x11b9eb [0x4C, 0x8B, 0x6C, 0x24, 0x18] (LoadPre 0x11b9eb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11b9eb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b9eb 13 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x11b9eb 13 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x11b9eb 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f78 : InstrSpec 0x11b9f0 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x11b9f0) (movR64R64Effect 0x11b9f0 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b9f0 0 13).toInstrSpec (mov_r64_r64_effect_step 0x11b9f0 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x11b9f3 [0x49, 0x89, 0xF7] (fun s => s.RIP = 0x11b9f3) (movR64R64Effect 0x11b9f3 15 6)
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x11b9f3 15 6).toInstrSpec (mov_r64_r64_effect_step 0x11b9f3 0x49 0xf7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f60 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 180), (1, 69), (2, 167), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 162), (12, 175), (13, 178), (14, 159), (15, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9b5) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f61 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 183) f61 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 184) (ρ' := [(0, 182), (1, 69), (2, 183), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 162), (12, 175), (13, 178), (14, 159), (15, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9b8) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f62 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 182), (1, 69), (2, 183), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 185), (12, 175), (13, 178), (14, 159), (15, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9bb) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f63 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 182), (1, 69), (2, 183), (3, 187), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 185), (12, 175), (13, 178), (14, 159), (15, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9be) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f64 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 189), (1, 69), (2, 183), (3, 187), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 185), (12, 175), (13, 178), (14, 159), (15, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9c1) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f65 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 192) f65 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 193) (ρ' := [(0, 191), (1, 69), (2, 192), (3, 187), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 185), (12, 175), (13, 178), (14, 159), (15, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9c4) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f66 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 195) f66 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 196) (ρ' := [(0, 191), (1, 69), (2, 192), (3, 194), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 185), (12, 175), (13, 178), (14, 159), (15, 156), (16, 195), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9c7) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f67 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 198) f67 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11b9c7 11 13 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 199) (ρ' := [(0, 191), (1, 69), (2, 192), (3, 194), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 197), (12, 175), (13, 178), (14, 159), (15, 156), (16, 198), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9ca) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f68 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 191), (1, 69), (2, 192), (3, 194), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 200), (11, 197), (12, 175), (13, 178), (14, 159), (15, 156), (16, 198), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9ce) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f69 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 203) f69 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 204) (ρ' := [(0, 191), (1, 69), (2, 192), (3, 202), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 200), (11, 197), (12, 175), (13, 178), (14, 159), (15, 156), (16, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9d1) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 205) (RestInside.out (n := 205) f70 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 206) f70 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11b9d1 11 2 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 207) (ρ' := [(0, 191), (1, 69), (2, 192), (3, 202), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 200), (11, 205), (12, 175), (13, 178), (14, 159), (15, 156), (16, 206), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9d4) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f71 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 208), (1, 69), (2, 192), (3, 202), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 200), (11, 205), (12, 175), (13, 178), (14, 159), (15, 156), (16, 206), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9d7) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f72 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 208), (1, 210), (2, 192), (3, 202), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 200), (11, 205), (12, 175), (13, 178), (14, 159), (15, 156), (16, 206), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9dc) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f73 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 208), (1, 210), (2, 192), (3, 202), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 200), (11, 205), (12, 212), (13, 178), (14, 159), (15, 156), (16, 206), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9e0) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f74 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 208), (1, 214), (2, 192), (3, 202), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 200), (11, 205), (12, 212), (13, 178), (14, 159), (15, 156), (16, 206), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9e3) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f75 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 217) f75 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 218) (ρ' := [(0, 208), (1, 214), (2, 192), (3, 202), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 216), (11, 205), (12, 212), (13, 178), (14, 159), (15, 156), (16, 217), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9e7) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f76 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 208), (1, 219), (2, 192), (3, 202), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 216), (11, 205), (12, 212), (13, 178), (14, 159), (15, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9eb) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f77 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 208), (1, 219), (2, 192), (3, 202), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 216), (11, 205), (12, 212), (13, 221), (14, 159), (15, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9f0) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f78 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 223), (1, 219), (2, 192), (3, 202), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 216), (11, 205), (12, 212), (13, 221), (14, 159), (15, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9f3) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f79 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 223), (1, 219), (2, 192), (3, 202), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 216), (11, 205), (12, 212), (13, 221), (14, 159), (15, 225), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9f6) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b8f0_4 code

theorem rest_l11b8f0_2 [Bindings] (code : CodeMap) :
    Rest (n := 136) code lifted (codeRange 0x11b8f0 bytes_l11b8f0) [(0, 124), (1, 69), (2, 125), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 71), (10, 108), (11, 134), (12, 73), (13, 92), (14, 115), (15, 120), (22, 22), (39, 39), (50, 50), (51, 51)]
      104 0x11b96e bytes_l11b8f0_2 b_l11b8f0_2 := by
  have f40 : InstrSpec 0x11b96e [0x4D, 0x8B, 0x48, 0x18] (LoadPre 0x11b96e (fun s => AddrMode.addr (.base 8 (.d8 0x18)) s (0x11b96e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b96e 9 (.base 8 (.d8 0x18)))
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x11b96e 9 (.base 8 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x11b96e 0x4d (by decide) 1 (.base 8 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x11b972 [0x4C, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x11b972 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11b972 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b972 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b972 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11b972 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x11b977 [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x11b977) (xorR32R32Effect 0x11b977 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b977 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x11b977 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x11b97a [0x4D, 0x39, 0xFB] (fun s => s.RIP = 0x11b97a) (cmpR64R64Effect 0x11b97a 11 15)
      [.gpr 11, .gpr 15] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11b97a 11 15).toInstrSpec (cmp_r64_r64_effect_step 0x11b97a 0x4d 0xfb (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x11b97d [0x41, 0x0F, 0x92, 0xC2] (fun s => s.RIP = 0x11b97d) (atFlags (condHolds 2) (setccR8Effect 0x11b97d 4 10))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .rip] :=
    (setccR8Effect_footprint 0x11b97d 4 10 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11b97d 2 0x41 (by decide) 0xc2 (by decide) c)) pre_rip
  have f45 : InstrSpec 0x11b981 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x11b981) (movR64R64Effect 0x11b981 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b981 0 12).toInstrSpec (mov_r64_r64_effect_step 0x11b981 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x11b984 [0x49, 0xF7, 0xE5] (fun s => s.RIP = 0x11b984) (mulR64Effect 0x11b984 13)
      [.gpr 13, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b984 13).toInstrSpec (mul_r64_effect_step 0x11b984 0x49 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x11b987 [0x4D, 0x89, 0xE8] (fun s => s.RIP = 0x11b987) (movR64R64Effect 0x11b987 8 13)
      [.gpr 13] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x11b987 8 13).toInstrSpec (mov_r64_r64_effect_step 0x11b987 0x4d 0xe8 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x11b98a [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x11b98a) (movR64R64Effect 0x11b98a 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x11b98a 14 2).toInstrSpec (mov_r64_r64_effect_step 0x11b98a 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x11b98d [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x11b98d) (movR64R64Effect 0x11b98d 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x11b98d 15 0).toInstrSpec (mov_r64_r64_effect_step 0x11b98d 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x11b990 [0x49, 0x01, 0xDF] (fun s => s.RIP = 0x11b990) (addR64R64Effect 0x11b990 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b990 15 3).toInstrSpec (add_r64_r64_effect_step 0x11b990 0x49 0xdf (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x11b993 [0x4D, 0x11, 0xDE] (fun s => s.RIP = 0x11b993) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b993 14 11))
      [.gpr 14, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b993 14 11).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b993 0x4d 0xde c (by decide) (by decide))) pre_rip
  have f52 : InstrSpec 0x11b996 [0x41, 0x0F, 0x92, 0xC3] (fun s => s.RIP = 0x11b996) (atFlags (condHolds 2) (setccR8Effect 0x11b996 4 11))
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .rip] :=
    (setccR8Effect_footprint 0x11b996 4 11 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11b996 2 0x41 (by decide) 0xc3 (by decide) c)) pre_rip
  have f53 : InstrSpec 0x11b99a [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x11b99a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b99a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b99a 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11b99a 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11b99a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f54 : InstrSpec 0x11b99f [0x48, 0xF7, 0xE6] (fun s => s.RIP = 0x11b99f) (mulR64Effect 0x11b99f 6)
      [.gpr 6, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b99f 6).toInstrSpec (mul_r64_effect_step 0x11b99f 0x48 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x11b9a2 [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x11b9a2) (movR64R64Effect 0x11b9a2 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x11b9a2 12 2).toInstrSpec (mov_r64_r64_effect_step 0x11b9a2 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x11b9a5 [0x45, 0x0F, 0xB6, 0xEB] (fun s => s.RIP = 0x11b9a5) (movzxR32R8Effect 0x11b9a5 4 13 11)
      [.gpr 11] [] [.reg 13, .rip] :=
    (movzxR32R8Effect_footprint 0x11b9a5 4 13 11).toInstrSpec (movzx_r32_r8_rex_effect_step 0x11b9a5 0x45 (by decide) 0xeb (by decide)) pre_rip
  have f57 : InstrSpec 0x11b9a9 [0x4C, 0x01, 0xF8] (fun s => s.RIP = 0x11b9a9) (addR64R64Effect 0x11b9a9 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b9a9 0 15).toInstrSpec (add_r64_r64_effect_step 0x11b9a9 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x11b9ac [0x4D, 0x11, 0xF4] (fun s => s.RIP = 0x11b9ac) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b9ac 12 14))
      [.gpr 12, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b9ac 12 14).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b9ac 0x4d 0xf4 c (by decide) (by decide))) pre_rip
  have f59 : InstrSpec 0x11b9af [0x4D, 0x11, 0xD5] (fun s => s.RIP = 0x11b9af) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b9af 13 10))
      [.gpr 13, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 13, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b9af 13 10).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b9af 0x4d 0xd5 c (by decide) (by decide))) pre_rip
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f40 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 124), (1, 69), (2, 125), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 136), (10, 108), (11, 134), (12, 73), (13, 92), (14, 115), (15, 120), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b972) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.exec (n := 138) (ρ' := [(0, 124), (1, 69), (2, 125), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 136), (10, 108), (11, 134), (12, 73), (13, 92), (14, 115), (15, 120), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b977) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f42 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 124), (1, 69), (2, 125), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 136), (10, 139), (11, 134), (12, 73), (13, 92), (14, 115), (15, 120), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b97a) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f43 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 124), (1, 69), (2, 125), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 136), (10, 139), (11, 134), (12, 73), (13, 92), (14, 115), (15, 120), (16, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b97d) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f44 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 124), (1, 69), (2, 125), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 136), (10, 143), (11, 134), (12, 73), (13, 92), (14, 115), (15, 120), (16, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b981) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f45 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 145), (1, 69), (2, 125), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 136), (10, 143), (11, 134), (12, 73), (13, 92), (14, 115), (15, 120), (16, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b984) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f46 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 148) f46 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 149) (ρ' := [(0, 147), (1, 69), (2, 148), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 136), (10, 143), (11, 134), (12, 73), (13, 92), (14, 115), (15, 120), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b987) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f47 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 147), (1, 69), (2, 148), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 134), (12, 73), (13, 92), (14, 115), (15, 120), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b98a) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f48 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 147), (1, 69), (2, 148), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 134), (12, 73), (13, 92), (14, 152), (15, 120), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b98d) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f49 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 147), (1, 69), (2, 148), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 134), (12, 73), (13, 92), (14, 152), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b990) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f50 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 157) f50 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 158) (ρ' := [(0, 147), (1, 69), (2, 148), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 134), (12, 73), (13, 92), (14, 152), (15, 156), (16, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b993) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f51 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 160) f51 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11b993 14 11 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 161) (ρ' := [(0, 147), (1, 69), (2, 148), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 134), (12, 73), (13, 92), (14, 159), (15, 156), (16, 160), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b996) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f52 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 147), (1, 69), (2, 148), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 162), (12, 73), (13, 92), (14, 159), (15, 156), (16, 160), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b99a) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f53 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 164), (1, 69), (2, 148), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 162), (12, 73), (13, 92), (14, 159), (15, 156), (16, 160), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b99f) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f54 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 167) f54 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 168) (ρ' := [(0, 166), (1, 69), (2, 167), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 162), (12, 73), (13, 92), (14, 159), (15, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9a2) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f55 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 166), (1, 69), (2, 167), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 162), (12, 169), (13, 92), (14, 159), (15, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9a5) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f56 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 166), (1, 69), (2, 167), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 162), (12, 169), (13, 171), (14, 159), (15, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9a9) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f57 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(1, 69), (2, 167), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 162), (12, 169), (13, 171), (14, 159), (15, 156), (16, 173), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9ac) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f58 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 176) f58 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11b9ac 12 14 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 177) (ρ' := [(1, 69), (2, 167), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 162), (12, 175), (13, 171), (14, 159), (15, 156), (16, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9af) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.out (n := 178) f59 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 179) (ρ' := [(1, 69), (2, 167), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 150), (9, 136), (10, 143), (11, 162), (12, 175), (13, 178), (14, 159), (15, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b9b2) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b8f0_3 code

theorem rest_l11b8f0_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x11b8f0 bytes_l11b8f0) [(0, 85), (1, 69), (2, 86), (3, 90), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 80), (11, 88), (12, 73), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      124 0x11b92a bytes_l11b8f0_1 b_l11b8f0_1 := by
  have f20 : InstrSpec 0x11b92a [0x4C, 0x8B, 0x6E, 0x08] (LoadPre 0x11b92a (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x11b92a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b92a 13 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x11b92a 13 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11b92a 0x4c (by decide) 5 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x11b92e [0x48, 0x89, 0x74, 0x24, 0x20] (StorePre 0x11b92e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11b92e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b92e 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b92e 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x11b92e 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x11b933 [0x4D, 0x8D, 0x3C, 0x02] (fun s => s.RIP = 0x11b933) (leaR64Effect 0x11b933 15 (.sib 10 (some 0) 0 .none))
      [.gpr 10, .gpr 0] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x11b933 15 (.sib 10 (some 0) 0 .none)).toInstrSpec (lea_r64_effect_step 0x11b933 0x4d (by decide) 7 (.sib 10 (some 0) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x11b937 [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x11b937) (movR64R64Effect 0x11b937 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b937 0 9).toInstrSpec (mov_r64_r64_effect_step 0x11b937 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x11b93a [0x49, 0xF7, 0xE5] (fun s => s.RIP = 0x11b93a) (mulR64Effect 0x11b93a 13)
      [.gpr 13, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b93a 13).toInstrSpec (mul_r64_effect_step 0x11b93a 0x49 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x11b93d [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x11b93d) (movR64R64Effect 0x11b93d 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x11b93d 14 2).toInstrSpec (mov_r64_r64_effect_step 0x11b93d 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x11b940 [0x4C, 0x01, 0xF8] (fun s => s.RIP = 0x11b940) (addR64R64Effect 0x11b940 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b940 0 15).toInstrSpec (add_r64_r64_effect_step 0x11b940 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x11b943 [0x49, 0x83, 0xD6, 0x00] (fun s => s.RIP = 0x11b943) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11b943 14 0x0))
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x11b943 14 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x11b943 0x49 0xd6 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f28 : InstrSpec 0x11b947 [0x4D, 0x01, 0xDA] (fun s => s.RIP = 0x11b947) (addR64R64Effect 0x11b947 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b947 10 11).toInstrSpec (add_r64_r64_effect_step 0x11b947 0x4d 0xda (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x11b94a [0x48, 0x8B, 0x76, 0x10] (LoadPre 0x11b94a (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x11b94a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b94a 6 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11b94a 6 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x11b94a 0x48 (by decide) 6 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x11b94e [0x49, 0x8B, 0x68, 0x10] (LoadPre 0x11b94e (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x11b94e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b94e 5 (.base 8 (.d8 0x10)))
      [.gpr 8] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x11b94e 5 (.base 8 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x11b94e 0x49 (by decide) 5 (.base 8 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x11b952 [0x49, 0x11, 0xDE] (fun s => s.RIP = 0x11b952) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b952 14 3))
      [.gpr 14, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b952 14 3).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b952 0x49 0xde c (by decide) (by decide))) pre_rip
  have f32 : InstrSpec 0x11b955 [0x0F, 0x92, 0xC2] (fun s => s.RIP = 0x11b955) (atFlags (condHolds 2) (setccR8Effect 0x11b955 3 2))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .rip] :=
    (setccR8Effect_footprint 0x11b955 3 2 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x11b955 2 0xc2 (by decide) (by decide) c)) pre_rip
  have f33 : InstrSpec 0x11b958 [0x44, 0x0F, 0xB6, 0xFA] (fun s => s.RIP = 0x11b958) (movzxR32R8Effect 0x11b958 4 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movzxR32R8Effect_footprint 0x11b958 4 15 2).toInstrSpec (movzx_r32_r8_rex_effect_step 0x11b958 0x44 (by decide) 0xfa (by decide)) pre_rip
  have f34 : InstrSpec 0x11b95c [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x11b95c) (movR64R64Effect 0x11b95c 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b95c 0 5).toInstrSpec (mov_r64_r64_effect_step 0x11b95c 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x11b95f [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x11b95f) (mulR64Effect 0x11b95f 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b95f 1).toInstrSpec (mul_r64_effect_step 0x11b95f 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x11b962 [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x11b962) (movR64R64Effect 0x11b962 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x11b962 11 2).toInstrSpec (mov_r64_r64_effect_step 0x11b962 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x11b965 [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x11b965) (movR64R64Effect 0x11b965 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x11b965 3 0).toInstrSpec (mov_r64_r64_effect_step 0x11b965 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x11b968 [0x4C, 0x01, 0xF3] (fun s => s.RIP = 0x11b968) (addR64R64Effect 0x11b968 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b968 3 14).toInstrSpec (add_r64_r64_effect_step 0x11b968 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x11b96b [0x4D, 0x11, 0xFB] (fun s => s.RIP = 0x11b96b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b96b 11 15))
      [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b96b 11 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b96b 0x4d 0xfb c (by decide) (by decide))) pre_rip
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 85), (1, 69), (2, 86), (3, 90), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 80), (11, 88), (12, 73), (13, 92), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b92e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 85), (1, 69), (2, 86), (3, 90), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 80), (11, 88), (12, 73), (13, 92), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b933) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 85), (1, 69), (2, 86), (3, 90), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 80), (11, 88), (12, 73), (13, 92), (14, 14), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b937) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 97), (1, 69), (2, 86), (3, 90), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 80), (11, 88), (12, 73), (13, 92), (14, 14), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b93a) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 100) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 101) (ρ' := [(0, 99), (1, 69), (2, 100), (3, 90), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 80), (11, 88), (12, 73), (13, 92), (14, 14), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b93d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f25 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 99), (1, 69), (2, 100), (3, 90), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 80), (11, 88), (12, 73), (13, 92), (14, 102), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b940) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f26 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(1, 69), (2, 100), (3, 90), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 80), (11, 88), (12, 73), (13, 92), (14, 102), (15, 95), (16, 104), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b943) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f27 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(1, 69), (2, 100), (3, 90), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 80), (11, 88), (12, 73), (13, 92), (14, 106), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b947) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f28 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 109) f28 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 110) (ρ' := [(1, 69), (2, 100), (3, 90), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 108), (11, 88), (12, 73), (13, 92), (14, 106), (15, 95), (16, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b94a) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(1, 69), (2, 100), (3, 90), (4, 65), (5, 5), (6, 111), (7, 7), (8, 67), (9, 71), (10, 108), (11, 88), (12, 73), (13, 92), (14, 106), (15, 95), (16, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b94e) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(1, 69), (2, 100), (3, 90), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 71), (10, 108), (11, 88), (12, 73), (13, 92), (14, 106), (15, 95), (16, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b952) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 116) f31 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11b952 14 3 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 117) (ρ' := [(1, 69), (2, 100), (3, 90), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 71), (10, 108), (11, 88), (12, 73), (13, 92), (14, 115), (15, 95), (16, 116), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b955) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f32 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(1, 69), (2, 118), (3, 90), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 71), (10, 108), (11, 88), (12, 73), (13, 92), (14, 115), (15, 95), (16, 116), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b958) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f33 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(1, 69), (2, 118), (3, 90), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 71), (10, 108), (11, 88), (12, 73), (13, 92), (14, 115), (15, 120), (16, 116), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b95c) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f34 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 122), (1, 69), (2, 118), (3, 90), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 71), (10, 108), (11, 88), (12, 73), (13, 92), (14, 115), (15, 120), (16, 116), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b95f) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f35 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 125) f35 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 126) (ρ' := [(0, 124), (1, 69), (2, 125), (3, 90), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 71), (10, 108), (11, 88), (12, 73), (13, 92), (14, 115), (15, 120), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b962) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f36 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 124), (1, 69), (2, 125), (3, 90), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 71), (10, 108), (11, 127), (12, 73), (13, 92), (14, 115), (15, 120), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b965) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f37 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 124), (1, 69), (2, 125), (3, 129), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 71), (10, 108), (11, 127), (12, 73), (13, 92), (14, 115), (15, 120), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b968) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f38 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 132) f38 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 133) (ρ' := [(0, 124), (1, 69), (2, 125), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 71), (10, 108), (11, 127), (12, 73), (13, 92), (14, 115), (15, 120), (16, 132), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b96b) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f39 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 124), (1, 69), (2, 125), (3, 131), (4, 65), (5, 113), (6, 111), (7, 7), (8, 67), (9, 71), (10, 108), (11, 134), (12, 73), (13, 92), (14, 115), (15, 120), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b96e) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b8f0_2 code

theorem rest_l11b8f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11b8f0 bytes_l11b8f0) (entryMap (live .l11b8f0))
      144 0x11b8f0 bytes_l11b8f0 b_l11b8f0 := by
  have f0 : InstrSpec 0x11b8f0 [0x55] (PushPre 0x11b8f0 1) (pushR64Effect 0x11b8f0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11b8f0 1 5).toInstrSpec (push_r64_effect_step 0x11b8f0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x11b8f1 [0x41, 0x57] (PushPre 0x11b8f1 2) (pushR64Effect 0x11b8f1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11b8f1 2 15).toInstrSpec (push_r64_rex_effect_step 0x11b8f1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x11b8f3 [0x41, 0x56] (PushPre 0x11b8f3 2) (pushR64Effect 0x11b8f3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11b8f3 2 14).toInstrSpec (push_r64_rex_effect_step 0x11b8f3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x11b8f5 [0x41, 0x55] (PushPre 0x11b8f5 2) (pushR64Effect 0x11b8f5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11b8f5 2 13).toInstrSpec (push_r64_rex_effect_step 0x11b8f5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x11b8f7 [0x41, 0x54] (PushPre 0x11b8f7 2) (pushR64Effect 0x11b8f7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11b8f7 2 12).toInstrSpec (push_r64_rex_effect_step 0x11b8f7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x11b8f9 [0x53] (PushPre 0x11b8f9 1) (pushR64Effect 0x11b8f9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11b8f9 1 3).toInstrSpec (push_r64_effect_step 0x11b8f9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x11b8fa [0x48, 0x83, 0xEC, 0x68] (fun s => s.RIP = 0x11b8fa) (subR64Imm8Effect 0x11b8fa 4 0x68)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x11b8fa 4 0x68).toInstrSpec (sub_r64_imm8_effect_step 0x11b8fa 0x48 0xec 0x68 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11b8fe [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x11b8fe) (movR64R64Effect 0x11b8fe 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x11b8fe 8 2).toInstrSpec (mov_r64_r64_effect_step 0x11b8fe 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11b901 [0x48, 0x8B, 0x0E] (LoadPre 0x11b901 (fun s => AddrMode.addr (.base 6 .none) s (0x11b901 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11b901 1 (.base 6 .none))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11b901 1 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11b901 0x48 (by decide) 1 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x11b904 [0x4C, 0x8B, 0x0A] (LoadPre 0x11b904 (fun s => AddrMode.addr (.base 2 .none) s (0x11b904 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11b904 9 (.base 2 .none))
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x11b904 9 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11b904 0x4c (by decide) 1 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x11b907 [0x4C, 0x8B, 0x62, 0x08] (LoadPre 0x11b907 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x11b907 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b907 12 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x11b907 12 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11b907 0x4c (by decide) 4 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x11b90b [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x11b90b) (movR64R64Effect 0x11b90b 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b90b 0 9).toInstrSpec (mov_r64_r64_effect_step 0x11b90b 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11b90e [0x4C, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x11b90e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b90e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b90e 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b90e 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11b90e 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x11b913 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x11b913) (mulR64Effect 0x11b913 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b913 1).toInstrSpec (mul_r64_effect_step 0x11b913 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11b916 [0x49, 0x89, 0xD2] (fun s => s.RIP = 0x11b916) (movR64R64Effect 0x11b916 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x11b916 10 2).toInstrSpec (mov_r64_r64_effect_step 0x11b916 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11b919 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x11b919) (movR64R64Effect 0x11b919 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b919 0 12).toInstrSpec (mov_r64_r64_effect_step 0x11b919 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11b91c [0x4C, 0x89, 0x64, 0x24, 0x18] (StorePre 0x11b91c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11b91c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b91c 12 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b91c 12 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x11b91c 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x11b921 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x11b921) (mulR64Effect 0x11b921 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b921 1).toInstrSpec (mul_r64_effect_step 0x11b921 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11b924 [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x11b924) (movR64R64Effect 0x11b924 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x11b924 11 0).toInstrSpec (mov_r64_r64_effect_step 0x11b924 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11b927 [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x11b927) (movR64R64Effect 0x11b927 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x11b927 3 2).toInstrSpec (mov_r64_r64_effect_step 0x11b927 0x48 0xd3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8f1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8f3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8f5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8f7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8f9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8fa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8fe) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b901) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 69), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b904) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 69), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b907) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 69), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (12, 73), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b90b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 69), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (12, 73), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b90e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 69), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (12, 73), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b913) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(1, 69), (2, 78), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (12, 73), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b916) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(1, 69), (2, 78), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 80), (12, 73), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b919) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 69), (2, 78), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 80), (12, 73), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b91c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 82), (1, 69), (2, 78), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 80), (12, 73), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b921) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 85), (1, 69), (2, 86), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 80), (12, 73), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b924) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 85), (1, 69), (2, 86), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 80), (11, 88), (12, 73), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b927) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 85), (1, 69), (2, 86), (3, 90), (4, 65), (5, 5), (6, 6), (7, 7), (8, 67), (9, 71), (10, 80), (11, 88), (12, 73), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b92a) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b8f0_1 code

theorem block_l11b8f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11b8f0 :=
  Rest.liftedBlock (rest_l11b8f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11b8f0 x hx)

theorem rest_l11badf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11badf bytes_l11badf) (entryMap (live .l11badf))
      2 0x11badf bytes_l11badf b_l11badf := by
  have f0 : InstrSpec 0x11badf [0x44, 0x89, 0xFF] (fun s => s.RIP = 0x11badf) (movR32R32Effect 0x11badf 3 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x11badf 3 7 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x11badf 0x44 0xff (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11bae2 [0xE8, 0x69, 0xC2, 0x00, 0x00] (PushPre 0x11bae2 5) (callEffect (fun _ => 0x127d50) 0x11bae7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11bae2 0x127d50 0x11bae7).toInstrSpec (call_rel32_effect_step 0x11bae2 0xc269 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bae2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l11badf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11badf :=
  Rest.liftedBlock (rest_l11badf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11badf x hx)

theorem rest_l11bae7_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x11bae7 bytes_l11bae7) [(0, 55), (1, 79), (2, 83), (3, 63), (4, 4), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]
      9 0x11bb30 bytes_l11bae7_1 b_l11bae7_1 := by
  have f20 : InstrSpec 0x11bb30 [0x49, 0x89, 0x56, 0x18] (StorePre 0x11bb30 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x11bb30 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11bb30 2 (.base 14 (.d8 0x18)))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x11bb30 2 (.base 14 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x11bb30 0x49 (by decide) 2 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x11bb34 [0x48, 0x83, 0xC4, 0x68] (fun s => s.RIP = 0x11bb34) (addR64Imm8Effect 0x11bb34 4 0x68)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11bb34 4 0x68).toInstrSpec (add_r64_imm8_effect_step 0x11bb34 0x48 0xc4 0x68 (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x11bb38 [0x5B] (PopPre 0x11bb38) (popR64Effect 0x11bb38 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11bb38 1 3).toInstrSpec (pop_r64_effect_step 0x11bb38 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f23 : InstrSpec 0x11bb39 [0x41, 0x5C] (PopPre 0x11bb39) (popR64Effect 0x11bb39 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11bb39 2 12).toInstrSpec (pop_r64_rex_effect_step 0x11bb39 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f24 : InstrSpec 0x11bb3b [0x41, 0x5D] (PopPre 0x11bb3b) (popR64Effect 0x11bb3b 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11bb3b 2 13).toInstrSpec (pop_r64_rex_effect_step 0x11bb3b 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f25 : InstrSpec 0x11bb3d [0x41, 0x5E] (PopPre 0x11bb3d) (popR64Effect 0x11bb3d 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11bb3d 2 14).toInstrSpec (pop_r64_rex_effect_step 0x11bb3d 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f26 : InstrSpec 0x11bb3f [0x41, 0x5F] (PopPre 0x11bb3f) (popR64Effect 0x11bb3f 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11bb3f 2 15).toInstrSpec (pop_r64_rex_effect_step 0x11bb3f 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f27 : InstrSpec 0x11bb41 [0x5D] (PopPre 0x11bb41) (popR64Effect 0x11bb41 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11bb41 1 5).toInstrSpec (pop_r64_effect_step 0x11bb41 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f28 : InstrSpec 0x11bb42 [0xC3] (RetPre 0x11bb42) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x11bb42).toInstrSpec (ret_effect_step 0x11bb42) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 55), (1, 79), (2, 83), (3, 63), (4, 4), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb34) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f21 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 55), (1, 79), (2, 83), (3, 63), (4, 89), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb38) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f22 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 92) f22 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 93) (ρ' := [(0, 55), (1, 79), (2, 83), (3, 91), (4, 92), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb39) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f23 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 95) f23 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 96) (ρ' := [(0, 55), (1, 79), (2, 83), (3, 91), (4, 95), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 94), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb3b) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f24 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 98) f24 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 99) (ρ' := [(0, 55), (1, 79), (2, 83), (3, 91), (4, 98), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 94), (13, 97), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb3d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f25 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 101) f25 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 102) (ρ' := [(0, 55), (1, 79), (2, 83), (3, 91), (4, 101), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 94), (13, 97), (14, 100), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb3f) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 104) f26 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 105) (ρ' := [(0, 55), (1, 79), (2, 83), (3, 91), (4, 104), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 94), (13, 97), (14, 100), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb41) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f27 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 107) f27 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 108) (ρ' := [(0, 55), (1, 79), (2, 83), (3, 91), (4, 107), (5, 106), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 94), (13, 97), (14, 100), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb42) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 110) f28 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 111) (ρ' := [(0, 55), (1, 79), (2, 83), (3, 91), (4, 110), (5, 106), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 94), (13, 97), (14, 100), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) f28 (by decide) rfl rfl rfl (by decide)

theorem rest_l11bae7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11bae7 bytes_l11bae7) (entryMap (live .l11bae7))
      29 0x11bae7 bytes_l11bae7 b_l11bae7 := by
  have f0 : InstrSpec 0x11bae7 [0x88, 0x44, 0x24, 0x07] (StorePre 0x11bae7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x11bae7 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11bae7 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11bae7 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x11bae7 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11baeb [0x48, 0x8D, 0x44, 0x24, 0x07] (fun s => s.RIP = 0x11baeb) (leaR64Effect 0x11baeb 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11baeb 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x11baeb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11baf0 [0x0F, 0xB6, 0x44, 0x24, 0x07] (LoadPre 0x11baf0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x11baf0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11baf0 5 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x11baf0 5 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x11baf0 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11baf5 [0x48, 0x8B, 0x4C, 0x24, 0x48] (LoadPre 0x11baf5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11baf5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11baf5 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11baf5 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x11baf5 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x11bafa [0x48, 0x8B, 0x54, 0x24, 0x50] (LoadPre 0x11bafa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11bafa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11bafa 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11bafa 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x11bafa 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x11baff [0x84, 0xC0] (fun s => s.RIP = 0x11baff) (testR8R8Effect 0x11baff 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11baff 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11baff 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11bb01 [0x48, 0x0F, 0x45, 0xD9] (fun s => s.RIP = 0x11bb01) (atFlags (condHolds 5) (cmovR64R64Effect 0x11bb01 4 3 1))
      [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 3, .rip] :=
    (cmovR64R64Effect_footprint 0x11bb01 4 3 1 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11bb01 5 0x48 (by decide) 0xd9 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x11bb05 [0x84, 0xC0] (fun s => s.RIP = 0x11bb05) (testR8R8Effect 0x11bb05 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11bb05 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11bb05 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11bb07 [0x4C, 0x0F, 0x45, 0xE2] (fun s => s.RIP = 0x11bb07) (atFlags (condHolds 5) (cmovR64R64Effect 0x11bb07 4 12 2))
      [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 12, .rip] :=
    (cmovR64R64Effect_footprint 0x11bb07 4 12 2 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11bb07 5 0x4c (by decide) 0xe2 (by decide) c)) pre_rip
  have f9 : InstrSpec 0x11bb0b [0x48, 0x8B, 0x4C, 0x24, 0x58] (LoadPre 0x11bb0b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11bb0b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11bb0b 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11bb0b 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x11bb0b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x11bb10 [0x31, 0xD2] (fun s => s.RIP = 0x11bb10) (xorR32R32Effect 0x11bb10 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11bb10 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x11bb10 0xd2 (by decide)) pre_rip
  have f11 : InstrSpec 0x11bb12 [0x31, 0xF6] (fun s => s.RIP = 0x11bb12) (xorR32R32Effect 0x11bb12 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11bb12 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x11bb12 0xf6 (by decide)) pre_rip
  have f12 : InstrSpec 0x11bb14 [0x84, 0xC0] (fun s => s.RIP = 0x11bb14) (testR8R8Effect 0x11bb14 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11bb14 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11bb14 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11bb16 [0x48, 0x0F, 0x45, 0xF1] (fun s => s.RIP = 0x11bb16) (atFlags (condHolds 5) (cmovR64R64Effect 0x11bb16 4 6 1))
      [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 6, .rip] :=
    (cmovR64R64Effect_footprint 0x11bb16 4 6 1 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11bb16 5 0x48 (by decide) 0xf1 (by decide) c)) pre_rip
  have f14 : InstrSpec 0x11bb1a [0x48, 0x8B, 0x4C, 0x24, 0x60] (LoadPre 0x11bb1a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11bb1a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11bb1a 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11bb1a 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x11bb1a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x11bb1f [0x84, 0xC0] (fun s => s.RIP = 0x11bb1f) (testR8R8Effect 0x11bb1f 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11bb1f 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11bb1f 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11bb21 [0x48, 0x0F, 0x45, 0xD1] (fun s => s.RIP = 0x11bb21) (atFlags (condHolds 5) (cmovR64R64Effect 0x11bb21 4 2 1))
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x11bb21 4 2 1 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11bb21 5 0x48 (by decide) 0xd1 (by decide) c)) pre_rip
  have f17 : InstrSpec 0x11bb25 [0x49, 0x89, 0x1E] (StorePre 0x11bb25 3 (fun s => AddrMode.addr (.base 14 .none) s (0x11bb25 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11bb25 3 (.base 14 .none))
      [.gpr 3, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x11bb25 3 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x11bb25 0x49 (by decide) 3 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x11bb28 [0x4D, 0x89, 0x66, 0x08] (StorePre 0x11bb28 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x11bb28 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11bb28 12 (.base 14 (.d8 0x8)))
      [.gpr 12, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x11bb28 12 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11bb28 0x4d (by decide) 4 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x11bb2c [0x49, 0x89, 0x76, 0x10] (StorePre 0x11bb2c 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x11bb2c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11bb2c 6 (.base 14 (.d8 0x10)))
      [.gpr 6, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x11bb2c 6 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11bb2c 0x49 (by decide) 6 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11baeb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11baf0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11baf5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bafa) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11baff) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb01) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 63), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb05) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 63), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb07) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 63), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb0b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 69), (2, 59), (3, 63), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb10) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 69), (2, 71), (3, 63), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb12) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 69), (2, 71), (3, 63), (4, 4), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb14) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 69), (2, 71), (3, 63), (4, 4), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb16) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 55), (1, 69), (2, 71), (3, 63), (4, 4), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb1a) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 55), (1, 79), (2, 71), (3, 63), (4, 4), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb1f) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 55), (1, 79), (2, 71), (3, 63), (4, 4), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb21) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 55), (1, 79), (2, 83), (3, 63), (4, 4), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb25) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 55), (1, 79), (2, 83), (3, 63), (4, 4), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb28) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 55), (1, 79), (2, 83), (3, 63), (4, 4), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb2c) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 55), (1, 79), (2, 83), (3, 63), (4, 4), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (14, 14), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11bb30) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l11bae7_1 code

theorem block_l11bae7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11bae7 :=
  Rest.liftedBlock (rest_l11bae7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11bae7 x hx)

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

theorem_by block_l11b8f0_eval :
    program.runBlock (dialect code) ⟨.l11b8f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11badf_eval :
    program.runBlock (dialect code) ⟨.l11badf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11bae7_eval :
    program.runBlock (dialect code) ⟨.l11bae7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
