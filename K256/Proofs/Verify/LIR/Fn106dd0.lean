import K256.Proofs.Verify.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

theorem rest_l106dd0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106dd0 bytes_l106dd0) (entryMap (live .l106dd0))
      20 0x106dd0 bytes_l106dd0 b_l106dd0 := by
  have f0 : InstrSpec 0x106dd0 [0x55] (PushPre 0x106dd0 1) (pushR64Effect 0x106dd0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106dd0 1 5).toInstrSpec (push_r64_effect_step 0x106dd0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x106dd1 [0x41, 0x57] (PushPre 0x106dd1 2) (pushR64Effect 0x106dd1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106dd1 2 15).toInstrSpec (push_r64_rex_effect_step 0x106dd1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x106dd3 [0x41, 0x56] (PushPre 0x106dd3 2) (pushR64Effect 0x106dd3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106dd3 2 14).toInstrSpec (push_r64_rex_effect_step 0x106dd3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x106dd5 [0x41, 0x55] (PushPre 0x106dd5 2) (pushR64Effect 0x106dd5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106dd5 2 13).toInstrSpec (push_r64_rex_effect_step 0x106dd5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x106dd7 [0x41, 0x54] (PushPre 0x106dd7 2) (pushR64Effect 0x106dd7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106dd7 2 12).toInstrSpec (push_r64_rex_effect_step 0x106dd7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x106dd9 [0x53] (PushPre 0x106dd9 1) (pushR64Effect 0x106dd9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106dd9 1 3).toInstrSpec (push_r64_effect_step 0x106dd9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x106dda [0x48, 0x83, 0xEC, 0x48] (fun s => s.RIP = 0x106dda) (subR64Imm8Effect 0x106dda 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x106dda 4 0x48).toInstrSpec (sub_r64_imm8_effect_step 0x106dda 0x48 0xec 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x106dde [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x106dde) (movR64R64Effect 0x106dde 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x106dde 0 6).toInstrSpec (mov_r64_r64_effect_step 0x106dde 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x106de1 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x106de1) (movR64R64Effect 0x106de1 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x106de1 3 7).toInstrSpec (mov_r64_r64_effect_step 0x106de1 0x48 0xfb (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x106de4 [0xC7, 0x44, 0x24, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x106de4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x106de4 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x106de4 8 (.sib 4 none 0 (.d8 0x24)) 0x100)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x106de4 8 (.sib 4 none 0 (.d8 0x24)) 0x100).toInstrSpec (mov_m32_imm32_effect_step 0x106de4 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide) 0x100) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x106dec [0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00] (StorePre 0x106dec 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x106dec + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106dec (.sib 4 none 0 (.d8 0x40)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x106dec (.sib 4 none 0 (.d8 0x40)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x106dec 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x106df5 [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x106df5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x106df5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106df5 (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x106df5 (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x106df5 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x106dfe [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x106dfe 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106dfe + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106dfe (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x106dfe (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x106dfe 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x106e07 [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x106e07 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106e07 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106e07 (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x106e07 (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x106e07 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x106e10 [0x48, 0x8D, 0x54, 0x24, 0x28] (fun s => s.RIP = 0x106e10) (leaR64Effect 0x106e10 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x106e10 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (lea_r64_effect_step 0x106e10 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x106e15 [0xBE, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106e15) (movR32Imm32Effect 0x106e15 5 6 0x20)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x106e15 5 6 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x106e15 0xbe (by decide) 0x20) pre_rip
  have f16 : InstrSpec 0x106e1a [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106e1a) (movR32Imm32Effect 0x106e1a 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x106e1a 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x106e1a 0xb9 (by decide) 0x4) pre_rip
  have f17 : InstrSpec 0x106e1f [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x106e1f) (movR64R64Effect 0x106e1f 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x106e1f 7 0).toInstrSpec (mov_r64_r64_effect_step 0x106e1f 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x106e22 [0x41, 0xB8, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x106e22) (movR32Imm32Effect 0x106e22 6 8 0x100)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x106e22 6 8 0x100).toInstrSpec (mov_r32_imm32_rex_effect_step 0x106e22 0x41 0xb8 (by decide) (by decide) 0x100) pre_rip
  have f19 : InstrSpec 0x106e28 [0xE8, 0x43, 0x0F, 0x02, 0x00] (PushPre 0x106e28 5) (callEffect (fun _ => 0x127d70) 0x106e2d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106e28 0x127d70 0x106e2d).toInstrSpec (call_rel32_effect_step 0x106e28 0x20f43 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dd1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dd3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dd5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dd7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dd9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dda) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dde) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106de1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (3, 69), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106de4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 67), (3, 69), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dec) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 67), (3, 69), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106df5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 67), (3, 69), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dfe) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 67), (3, 69), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e07) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 67), (3, 69), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e10) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 67), (2, 76), (3, 69), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e15) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 67), (2, 76), (3, 69), (4, 65), (5, 5), (6, 78), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e1a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 67), (1, 80), (2, 76), (3, 69), (4, 65), (5, 5), (6, 78), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e1f) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 67), (1, 80), (2, 76), (3, 69), (4, 65), (5, 5), (6, 78), (7, 82), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e22) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f18 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 67), (1, 80), (2, 76), (3, 69), (4, 65), (5, 5), (6, 78), (7, 82), (8, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e28) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 67), (1, 80), (2, 76), (3, 69), (4, 86), (5, 5), (6, 78), (7, 82), (8, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d70) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 88) (by decide) (by decide) rfl rfl

theorem block_l106dd0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106dd0 :=
  Rest.liftedBlock (rest_l106dd0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106dd0 x hx)

theorem rest_l106e2d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106e2d bytes_l106e2d) (entryMap (live .l106e2d))
      2 0x106e2d bytes_l106e2d b_l106e2d := by
  have f0 : InstrSpec 0x106e2d [0x3C, 0xFF] (fun s => s.RIP = 0x106e2d) (cmpAlImm8Effect 0x106e2d 0xff)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x106e2d 0xff).toInstrSpec (cmp_al_imm8_effect_step 0x106e2d 0xff) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e2f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x106e2f 5 0x13b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106e2d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106e2d :=
  Rest.liftedBlock (rest_l106e2d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106e2d x hx)

theorem rest_l106e35_2 [Bindings] (code : CodeMap) :
    Rest (n := 129) code lifted (codeRange 0x106e35 bytes_l106e35) [(1, 121), (2, 127), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x106ece bytes_l106e35_2 b_l106e35_2 := by
  have f40 : InstrSpec 0x106ece [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x106ece) (shrR64Effect 0x106ece 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x106ece 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x106ece 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x106ed2 [0x48, 0x89, 0x14, 0x24] (StorePre 0x106ed2 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106ed2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106ed2 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106ed2 2 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x106ed2 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x106ed6 [0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x106ed6 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106ed6 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x106ed6 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x106ed6 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x106ed6 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x106eda [0x24, 0x01] (fun s => s.RIP = 0x106eda) (andAlImm8Effect 0x106eda 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x106eda 0x1).toInstrSpec (and_al_imm8_effect_step 0x106eda 0x1) pre_rip
  have f44 : InstrSpec 0x106edc [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x106edc) (movzxR32R8Effect 0x106edc 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x106edc 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x106edc 0xf8 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x106edf [0xE8, 0x6C, 0x0E, 0x02, 0x00] (PushPre 0x106edf 5) (callEffect (fun _ => 0x127d50) 0x106ee4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106edf 0x127d50 0x106ee4).toInstrSpec (call_rel32_effect_step 0x106edf 0x20e6c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f40 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(1, 121), (2, 129), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ed2) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.exec (n := 131) (ρ' := [(1, 121), (2, 129), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ed6) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f42 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 132), (1, 121), (2, 129), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106eda) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f43 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 134), (1, 121), (2, 129), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106edc) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f44 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 134), (1, 121), (2, 129), (3, 3), (4, 4), (5, 5), (6, 87), (7, 136), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106edf) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f45 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 134), (1, 121), (2, 129), (3, 3), (4, 138), (5, 5), (6, 87), (7, 136), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f45 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 140) (by decide) (by decide) rfl rfl

theorem rest_l106e35_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x106e35 bytes_l106e35) [(1, 75), (2, 89), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]
      26 0x106e89 bytes_l106e35_1 b_l106e35_1 := by
  have f20 : InstrSpec 0x106e89 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x106e89) (notR64Effect 0x106e89 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x106e89 2).toInstrSpec (not_r64_effect_step 0x106e89 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x106e8c [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x106e8c) (orR64R64Effect 0x106e8c 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x106e8c 2 6).toInstrSpec (or_r64_r64_effect_step 0x106e8c 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x106e8f [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x106e8f) (shrR64Effect 0x106e8f 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x106e8f 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x106e8f 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x106e93 [0x48, 0x89, 0x14, 0x24] (StorePre 0x106e93 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106e93 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106e93 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106e93 2 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x106e93 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x106e97 [0x48, 0x2B, 0x0C, 0x24] (LoadPre 0x106e97 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106e97 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x106e97 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x106e97 1 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x106e97 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x106e9b [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x106e9b) (sarR64Effect 0x106e9b 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x106e9b 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x106e9b 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x106e9f [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x106e9f) (movR64R64Effect 0x106e9f 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x106e9f 2 12).toInstrSpec (mov_r64_r64_effect_step 0x106e9f 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x106ea2 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x106ea2) (notR64Effect 0x106ea2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x106ea2 2).toInstrSpec (not_r64_effect_step 0x106ea2 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x106ea5 [0x4C, 0x01, 0xE1] (fun s => s.RIP = 0x106ea5) (addR64R64Effect 0x106ea5 1 12)
      [.gpr 1, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x106ea5 1 12).toInstrSpec (add_r64_r64_effect_step 0x106ea5 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x106ea8 [0x48, 0x83, 0xC1, 0x02] (fun s => s.RIP = 0x106ea8) (addR64Imm8Effect 0x106ea8 1 0x2)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x106ea8 1 0x2).toInstrSpec (add_r64_imm8_effect_step 0x106ea8 0x48 0xc1 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x106eac [0x48, 0x09, 0xD1] (fun s => s.RIP = 0x106eac) (orR64R64Effect 0x106eac 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x106eac 1 2).toInstrSpec (or_r64_r64_effect_step 0x106eac 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x106eaf [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x106eaf) (shrR64Effect 0x106eaf 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x106eaf 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x106eaf 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x106eb3 [0x48, 0x89, 0x0C, 0x24] (StorePre 0x106eb3 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106eb3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106eb3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106eb3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x106eb3 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x106eb7 [0x48, 0x8B, 0x0C, 0x24] (LoadPre 0x106eb7 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106eb7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x106eb7 1 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x106eb7 1 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x106eb7 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x106ebb [0x48, 0xFF, 0xC9] (fun s => s.RIP = 0x106ebb) (decR64Effect 0x106ebb 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (decR64Effect_footprint 0x106ebb 1).toInstrSpec (dec_r64_effect_step 0x106ebb 0x48 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x106ebe [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x106ebe) (shrR64Effect 0x106ebe 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x106ebe 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x106ebe 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x106ec2 [0x4C, 0x01, 0xE9] (fun s => s.RIP = 0x106ec2) (addR64R64Effect 0x106ec2 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x106ec2 1 13).toInstrSpec (add_r64_r64_effect_step 0x106ec2 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x106ec5 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x106ec5) (movR64R64Effect 0x106ec5 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x106ec5 2 13).toInstrSpec (mov_r64_r64_effect_step 0x106ec5 0x4c 0xea (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x106ec8 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x106ec8) (notR64Effect 0x106ec8 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x106ec8 2).toInstrSpec (not_r64_effect_step 0x106ec8 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x106ecb [0x48, 0x09, 0xCA] (fun s => s.RIP = 0x106ecb) (orR64R64Effect 0x106ecb 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x106ecb 2 1).toInstrSpec (or_r64_r64_effect_step 0x106ecb 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(1, 75), (2, 91), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e8c) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(1, 75), (2, 93), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e8f) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(1, 75), (2, 95), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e93) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(1, 75), (2, 95), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e97) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(1, 98), (2, 95), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e9b) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f25 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(1, 100), (2, 95), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e9f) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(1, 100), (2, 102), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ea2) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(1, 100), (2, 104), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ea5) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(1, 106), (2, 104), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ea8) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f29 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(1, 108), (2, 104), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106eac) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(1, 110), (2, 104), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106eaf) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f31 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(1, 112), (2, 104), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106eb3) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.exec (n := 114) (ρ' := [(1, 112), (2, 104), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106eb7) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f33 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(1, 115), (2, 104), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ebb) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(1, 117), (2, 104), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ebe) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(1, 119), (2, 104), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ec2) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(1, 121), (2, 104), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ec5) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(1, 121), (2, 123), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ec8) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(1, 121), (2, 125), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ecb) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f39 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(1, 121), (2, 127), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ece) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106e35_2 code

theorem rest_l106e35 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106e35 bytes_l106e35) (entryMap (live .l106e35))
      46 0x106e35 bytes_l106e35 b_l106e35 := by
  have f0 : InstrSpec 0x106e35 [0x4C, 0x8B, 0x74, 0x24, 0x28] (LoadPre 0x106e35 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106e35 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106e35 14 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x106e35 14 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x106e35 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106e3a [0x4C, 0x8B, 0x7C, 0x24, 0x30] (LoadPre 0x106e3a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106e3a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106e3a 15 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x106e3a 15 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x106e3a 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106e3f [0x4C, 0x8B, 0x64, 0x24, 0x38] (LoadPre 0x106e3f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x106e3f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106e3f 12 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x106e3f 12 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x106e3f 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x106e44 [0x4C, 0x8B, 0x6C, 0x24, 0x40] (LoadPre 0x106e44 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x106e44 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106e44 13 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x106e44 13 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x106e44 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x106e49 [0x48, 0xB8, 0xBF, 0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40] (fun s => s.RIP = 0x106e49) (movR64Imm64Effect 0x106e49 0 0x402da1732fc9bebf)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x106e49 0 0x402da1732fc9bebf).toInstrSpec (mov_r64_imm64_effect_step 0x106e49 0x48 0xb8 (by decide) (by decide) 0x402da1732fc9bebf) pre_rip
  have f5 : InstrSpec 0x106e53 [0x4C, 0x01, 0xF0] (fun s => s.RIP = 0x106e53) (addR64R64Effect 0x106e53 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x106e53 0 14).toInstrSpec (add_r64_r64_effect_step 0x106e53 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x106e56 [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x106e56) (movR64R64Effect 0x106e56 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x106e56 1 14).toInstrSpec (mov_r64_r64_effect_step 0x106e56 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x106e59 [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x106e59) (notR64Effect 0x106e59 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x106e59 1).toInstrSpec (not_r64_effect_step 0x106e59 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x106e5c [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x106e5c) (orR64R64Effect 0x106e5c 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x106e5c 1 0).toInstrSpec (or_r64_r64_effect_step 0x106e5c 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x106e5f [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x106e5f) (shrR64Effect 0x106e5f 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x106e5f 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x106e5f 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x106e63 [0x48, 0x89, 0x0C, 0x24] (StorePre 0x106e63 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106e63 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106e63 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106e63 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x106e63 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x106e67 [0x48, 0x89, 0xE0] (fun s => s.RIP = 0x106e67) (movR64R64Effect 0x106e67 0 4)
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x106e67 0 4).toInstrSpec (mov_r64_r64_effect_step 0x106e67 0x48 0xe0 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x106e6a [0x31, 0xC9] (fun s => s.RIP = 0x106e6a) (xorR32R32Effect 0x106e6a 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106e6a 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x106e6a 0xc9 (by decide)) pre_rip
  have f13 : InstrSpec 0x106e6c [0x31, 0xD2] (fun s => s.RIP = 0x106e6c) (xorR32R32Effect 0x106e6c 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106e6c 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x106e6c 0xd2 (by decide)) pre_rip
  have f14 : InstrSpec 0x106e6e [0x48, 0x2B, 0x14, 0x24] (LoadPre 0x106e6e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106e6e + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x106e6e 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x106e6e 2 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x106e6e 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x106e72 [0x48, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x106e72) (sarR64Effect 0x106e72 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (sarR64Effect_footprint 0x106e72 4 2 63).toInstrSpec (sar_r64_imm8_effect_step 0x106e72 0x48 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x106e76 [0x48, 0xBE, 0xC5, 0x5F, 0xB7, 0x50, 0x19, 0x23, 0x51, 0x45] (fun s => s.RIP = 0x106e76) (movR64Imm64Effect 0x106e76 6 0x4551231950b75fc5)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x106e76 6 0x4551231950b75fc5).toInstrSpec (mov_r64_imm64_effect_step 0x106e76 0x48 0xbe (by decide) (by decide) 0x4551231950b75fc5) pre_rip
  have f17 : InstrSpec 0x106e80 [0x4C, 0x01, 0xFE] (fun s => s.RIP = 0x106e80) (addR64R64Effect 0x106e80 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x106e80 6 15).toInstrSpec (add_r64_r64_effect_step 0x106e80 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x106e83 [0x48, 0x01, 0xD6] (fun s => s.RIP = 0x106e83) (addR64R64Effect 0x106e83 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x106e83 6 2).toInstrSpec (add_r64_r64_effect_step 0x106e83 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x106e86 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x106e86) (movR64R64Effect 0x106e86 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x106e86 2 15).toInstrSpec (mov_r64_r64_effect_step 0x106e86 0x4c 0xfa (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e3a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e3f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e44) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e49) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e53) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e56) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e59) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 63), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e5c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 63), (1, 69), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e5f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 63), (1, 71), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e63) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 63), (1, 71), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e67) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(1, 71), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e6a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 75), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e6c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 75), (2, 77), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e6e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 75), (2, 79), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e72) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(1, 75), (2, 81), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e76) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(1, 75), (2, 81), (3, 3), (4, 4), (5, 5), (6, 83), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e80) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(1, 75), (2, 81), (3, 3), (4, 4), (5, 5), (6, 85), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e83) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(1, 75), (2, 81), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e86) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(1, 75), (2, 89), (3, 3), (4, 4), (5, 5), (6, 87), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e89) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106e35_1 code

theorem block_l106e35 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106e35 :=
  Rest.liftedBlock (rest_l106e35 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106e35 x hx)

theorem rest_l106ee4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106ee4 bytes_l106ee4) (entryMap (live .l106ee4))
      3 0x106ee4 bytes_l106ee4 b_l106ee4 := by
  have f0 : InstrSpec 0x106ee4 [0xBD, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106ee4) (movR32Imm32Effect 0x106ee4 5 5 0x1)
      [] [] [.reg 5, .rip] :=
    (movR32Imm32Effect_footprint 0x106ee4 5 5 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x106ee4 0xbd (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x106ee9 [0x3C, 0x01] (fun s => s.RIP = 0x106ee9) (cmpAlImm8Effect 0x106ee9 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x106ee9 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x106ee9 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ee9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106eeb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x106eeb 5 0x6e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106ee4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106ee4 :=
  Rest.liftedBlock (rest_l106ee4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106ee4 x hx)

theorem rest_l106eed [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106eed bytes_l106eed) (entryMap (live .l106eed))
      13 0x106eed bytes_l106eed b_l106eed := by
  have f0 : InstrSpec 0x106eed [0x4C, 0x89, 0x74, 0x24, 0x28] (StorePre 0x106eed 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106eed + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106eed 14 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106eed 14 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x106eed 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x106ef2 [0x4C, 0x89, 0x7C, 0x24, 0x30] (StorePre 0x106ef2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106ef2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106ef2 15 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106ef2 15 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x106ef2 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x106ef7 [0x4C, 0x89, 0x64, 0x24, 0x38] (StorePre 0x106ef7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x106ef7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106ef7 12 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106ef7 12 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x106ef7 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x106efc [0x4C, 0x89, 0x6C, 0x24, 0x40] (StorePre 0x106efc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x106efc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106efc 13 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106efc 13 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x106efc 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x106f01 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x106f01 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x106f01 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106f01 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x106f01 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x106f01 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x106f0a [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x106f0a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106f0a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106f0a (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x106f0a (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x106f0a 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x106f13 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x106f13 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106f13 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106f13 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x106f13 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x106f13 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x106f1c [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x106f1c 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106f1c + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x106f1c (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x106f1c (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x106f1c 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x106f24 [0x48, 0x8D, 0x7C, 0x24, 0x28] (fun s => s.RIP = 0x106f24) (leaR64Effect 0x106f24 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x106f24 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (lea_r64_effect_step 0x106f24 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x106f29 [0x48, 0x89, 0xE2] (fun s => s.RIP = 0x106f29) (movR64R64Effect 0x106f29 2 4)
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x106f29 2 4).toInstrSpec (mov_r64_r64_effect_step 0x106f29 0x48 0xe2 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x106f2c [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106f2c) (movR32Imm32Effect 0x106f2c 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x106f2c 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x106f2c 0xbe (by decide) 0x4) pre_rip
  have f11 : InstrSpec 0x106f31 [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106f31) (movR32Imm32Effect 0x106f31 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x106f31 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x106f31 0xb9 (by decide) 0x4) pre_rip
  have f12 : InstrSpec 0x106f36 [0xE8, 0x15, 0x10, 0x02, 0x00] (PushPre 0x106f36 5) (callEffect (fun _ => 0x127f50) 0x106f3b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106f36 0x127f50 0x106f3b).toInstrSpec (call_rel32_effect_step 0x106f36 0x21015 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ef2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ef7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106efc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f01) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f0a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f13) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f1c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f24) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f29) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (2, 63), (3, 3), (4, 4), (5, 5), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f2c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (2, 63), (3, 3), (4, 4), (5, 5), (6, 65), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f31) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 63), (3, 3), (4, 4), (5, 5), (6, 65), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f36) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 67), (2, 63), (3, 3), (4, 69), (5, 5), (6, 65), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f50) f12 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l106eed [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106eed :=
  Rest.liftedBlock (rest_l106eed code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106eed x hx)

theorem rest_l106f3b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106f3b bytes_l106f3b) (entryMap (live .l106f3b))
      3 0x106f3b bytes_l106f3b b_l106f3b := by
  have f0 : InstrSpec 0x106f3b [0x24, 0x01] (fun s => s.RIP = 0x106f3b) (andAlImm8Effect 0x106f3b 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x106f3b 0x1).toInstrSpec (and_al_imm8_effect_step 0x106f3b 0x1) pre_rip
  have f1 : InstrSpec 0x106f3d [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x106f3d) (movzxR32R8Effect 0x106f3d 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x106f3d 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x106f3d 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106f40 [0xE8, 0x0B, 0x0E, 0x02, 0x00] (PushPre 0x106f40 5) (callEffect (fun _ => 0x127d50) 0x106f45)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106f40 0x127d50 0x106f45).toInstrSpec (call_rel32_effect_step 0x106f40 0x20e0b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f3d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f40) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l106f3b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106f3b :=
  Rest.liftedBlock (rest_l106f3b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106f3b x hx)

theorem rest_l106f45 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106f45 bytes_l106f45) (entryMap (live .l106f45))
      2 0x106f45 bytes_l106f45 b_l106f45 := by
  have f0 : InstrSpec 0x106f45 [0x84, 0xC0] (fun s => s.RIP = 0x106f45) (testR8R8Effect 0x106f45 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x106f45 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x106f45 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f47) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x106f47 5 0x12) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106f45 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106f45 :=
  Rest.liftedBlock (rest_l106f45 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106f45 x hx)

theorem rest_l106f49 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106f49 bytes_l106f49) (entryMap (live .l106f49))
      5 0x106f49 bytes_l106f49 b_l106f49 := by
  have f0 : InstrSpec 0x106f49 [0x4C, 0x89, 0x73, 0x08] (StorePre 0x106f49 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106f49 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106f49 14 (.base 3 (.d8 0x8)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106f49 14 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x106f49 0x4c (by decide) 6 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x106f4d [0x4C, 0x89, 0x7B, 0x10] (StorePre 0x106f4d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x106f4d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106f4d 15 (.base 3 (.d8 0x10)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106f4d 15 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x106f4d 0x4c (by decide) 7 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x106f51 [0x4C, 0x89, 0x63, 0x18] (StorePre 0x106f51 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x106f51 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106f51 12 (.base 3 (.d8 0x18)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106f51 12 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x106f51 0x4c (by decide) 4 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x106f55 [0x4C, 0x89, 0x6B, 0x20] (StorePre 0x106f55 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x106f55 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106f55 13 (.base 3 (.d8 0x20)))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106f55 13 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x106f55 0x4c (by decide) 5 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x106f59 [0x31, 0xED] (fun s => s.RIP = 0x106f59) (xorR32R32Effect 0x106f59 2 5 5)
      [.gpr 5, .gpr 5] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f59 2 5 5).toInstrSpec (xor_r32_r32_effect_step 0x106f59 0xed (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f4d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f51) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f55) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f59) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f5b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l106f49 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106f49 :=
  Rest.liftedBlock (rest_l106f49 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106f49 x hx)

theorem rest_l106f5b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106f5b bytes_l106f5b) (entryMap (live .l106f5b))
      10 0x106f5b bytes_l106f5b b_l106f5b := by
  have f0 : InstrSpec 0x106f5b [0x48, 0x89, 0x2B] (StorePre 0x106f5b 3 (fun s => AddrMode.addr (.base 3 .none) s (0x106f5b + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x106f5b 5 (.base 3 .none))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106f5b 5 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x106f5b 0x48 (by decide) 5 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x106f5e [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x106f5e) (movR64R64Effect 0x106f5e 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x106f5e 0 3).toInstrSpec (mov_r64_r64_effect_step 0x106f5e 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106f61 [0x48, 0x83, 0xC4, 0x48] (fun s => s.RIP = 0x106f61) (addR64Imm8Effect 0x106f61 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x106f61 4 0x48).toInstrSpec (add_r64_imm8_effect_step 0x106f61 0x48 0xc4 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106f65 [0x5B] (PopPre 0x106f65) (popR64Effect 0x106f65 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106f65 1 3).toInstrSpec (pop_r64_effect_step 0x106f65 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x106f66 [0x41, 0x5C] (PopPre 0x106f66) (popR64Effect 0x106f66 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106f66 2 12).toInstrSpec (pop_r64_rex_effect_step 0x106f66 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x106f68 [0x41, 0x5D] (PopPre 0x106f68) (popR64Effect 0x106f68 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106f68 2 13).toInstrSpec (pop_r64_rex_effect_step 0x106f68 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x106f6a [0x41, 0x5E] (PopPre 0x106f6a) (popR64Effect 0x106f6a 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106f6a 2 14).toInstrSpec (pop_r64_rex_effect_step 0x106f6a 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x106f6c [0x41, 0x5F] (PopPre 0x106f6c) (popR64Effect 0x106f6c 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106f6c 2 15).toInstrSpec (pop_r64_rex_effect_step 0x106f6c 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x106f6e [0x5D] (PopPre 0x106f6e) (popR64Effect 0x106f6e 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106f6e 1 5).toInstrSpec (pop_r64_effect_step 0x106f6e 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x106f6f [0xC3] (RetPre 0x106f6f) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x106f6f).toInstrSpec (ret_effect_step 0x106f6f) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f5e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f61) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f65) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f66) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f68) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f6a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f6c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 71), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f6e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 74), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f6f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f9 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 78) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 77), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) f9 (by decide) rfl rfl rfl (by decide)

theorem block_l106f5b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106f5b :=
  Rest.liftedBlock (rest_l106f5b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106f5b x hx)

theorem rest_l106f70 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106f70 bytes_l106f70) (entryMap (live .l106f70))
      9 0x106f70 bytes_l106f70 b_l106f70 := by
  have f0 : InstrSpec 0x106f70 [0x48, 0xC7, 0x04, 0x24, 0x98, 0x24, 0x20, 0x00] (StorePre 0x106f70 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106f70 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x106f70 (.sib 4 none 0 .none) 0x202498)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x106f70 (.sib 4 none 0 .none) 0x202498).toInstrSpec (mov_m64_imm32_effect_step 0x106f70 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x202498) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x106f78 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x106f78 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106f78 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106f78 (.sib 4 none 0 (.d8 0x8)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x106f78 (.sib 4 none 0 (.d8 0x8)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x106f78 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x106f81 [0x48, 0x8D, 0x44, 0x24, 0x24] (fun s => s.RIP = 0x106f81) (leaR64Effect 0x106f81 0 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x106f81 0 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (lea_r64_effect_step 0x106f81 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106f86 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x106f86 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106f86 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106f86 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106f86 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x106f86 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x106f8b [0x48, 0xC7, 0x44, 0x24, 0x18, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x106f8b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x106f8b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106f8b (.sib 4 none 0 (.d8 0x18)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x106f8b (.sib 4 none 0 (.d8 0x18)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x106f8b 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x106f94 [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x106f94) (movR64R64Effect 0x106f94 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x106f94 6 4).toInstrSpec (mov_r64_r64_effect_step 0x106f94 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x106f97 [0x48, 0xC7, 0xC7, 0x8F, 0x02, 0x20, 0x00] (fun s => s.RIP = 0x106f97) (movR64Imm32Effect 0x106f97 7 0x20028f)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x106f97 7 0x20028f).toInstrSpec (mov_r64_imm32_effect_step 0x106f97 0x48 0xc7 (by decide) (by decide) (by decide) 0x20028f) pre_rip
  have f7 : InstrSpec 0x106f9e [0x48, 0xC7, 0xC2, 0x18, 0x25, 0x20, 0x00] (fun s => s.RIP = 0x106f9e) (movR64Imm32Effect 0x106f9e 2 0x202518)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x106f9e 2 0x202518).toInstrSpec (mov_r64_imm32_effect_step 0x106f9e 0x48 0xc2 (by decide) (by decide) (by decide) 0x202518) pre_rip
  have f8 : InstrSpec 0x106fa5 [0xE8, 0xC6, 0x27, 0x02, 0x00] (PushPre 0x106fa5 5) (callEffect (fun _ => 0x129770) 0x106faa)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106fa5 0x129770 0x106faa).toInstrSpec (call_rel32_effect_step 0x106fa5 0x227c6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x106f78) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5)]) (p' := 0x106f81) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x106f86) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x106f8b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x106f94) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (4, 4), (5, 5), (6, 59)]) (p' := 0x106f97) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (4, 4), (5, 5), (6, 59), (7, 61)]) (p' := 0x106f9e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (2, 63), (4, 4), (5, 5), (6, 59), (7, 61)]) (p' := 0x106fa5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (2, 63), (4, 65), (5, 5), (6, 59), (7, 61)]) (p' := 0x129770) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l106f70 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106f70 :=
  Rest.liftedBlock (rest_l106f70 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106f70 x hx)

theorem rest_l106faa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106faa bytes_l106faa) (entryMap (live .l106faa))
      12 0x106faa bytes_l106faa b_l106faa := by
  have f0 : InstrSpec 0x106faa [0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x106faa) (fun _ => nopEffect 0x106faa 6)
      [] [] [.rip] :=
    (nopEffect_footprint 0x106faa 6).toInstrSpec (nop_m_effect_step 0x106faa [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106fb0 [0x55] (PushPre 0x106fb0 1) (pushR64Effect 0x106fb0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106fb0 1 5).toInstrSpec (push_r64_effect_step 0x106fb0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x106fb1 [0x41, 0x57] (PushPre 0x106fb1 2) (pushR64Effect 0x106fb1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106fb1 2 15).toInstrSpec (push_r64_rex_effect_step 0x106fb1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x106fb3 [0x41, 0x56] (PushPre 0x106fb3 2) (pushR64Effect 0x106fb3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106fb3 2 14).toInstrSpec (push_r64_rex_effect_step 0x106fb3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x106fb5 [0x41, 0x55] (PushPre 0x106fb5 2) (pushR64Effect 0x106fb5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106fb5 2 13).toInstrSpec (push_r64_rex_effect_step 0x106fb5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x106fb7 [0x41, 0x54] (PushPre 0x106fb7 2) (pushR64Effect 0x106fb7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106fb7 2 12).toInstrSpec (push_r64_rex_effect_step 0x106fb7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x106fb9 [0x53] (PushPre 0x106fb9 1) (pushR64Effect 0x106fb9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106fb9 1 3).toInstrSpec (push_r64_effect_step 0x106fb9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x106fba [0x48, 0x81, 0xEC, 0xD8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x106fba) (subR64Imm32Effect 0x106fba 4 0x1d8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x106fba 4 0x1d8).toInstrSpec (sub_r64_imm32_effect_step 0x106fba 0x48 0xec 0x1d8 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x106fc1 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x106fc1) (movR64R64Effect 0x106fc1 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x106fc1 3 7).toInstrSpec (mov_r64_r64_effect_step 0x106fc1 0x48 0xfb (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x106fc4 [0x48, 0x8D, 0xAC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106fc4) (leaR64Effect 0x106fc4 5 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x106fc4 5 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x106fc4 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x106fcc [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x106fcc) (movR64R64Effect 0x106fcc 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x106fcc 7 5).toInstrSpec (mov_r64_r64_effect_step 0x106fcc 0x48 0xef (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x106fcf [0xE8, 0xBC, 0xE7, 0x01, 0x00] (PushPre 0x106fcf 5) (callEffect (fun _ => 0x125790) 0x106fd4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106fcf 0x125790 0x106fd4).toInstrSpec (call_rel32_effect_step 0x106fcf 0x1e7bc (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fb0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fb1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fb3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fb5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fb7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 2), (3, 3), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fb9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 2), (3, 3), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fba) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fc1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(2, 2), (3, 68), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fc4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(2, 2), (3, 68), (4, 66), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fcc) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(2, 2), (3, 68), (4, 66), (5, 70), (6, 6), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fcf) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(2, 2), (3, 68), (4, 74), (5, 70), (6, 6), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125790) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 76) (by decide) (by decide) rfl rfl

theorem block_l106faa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106faa :=
  Rest.liftedBlock (rest_l106faa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106faa x hx)

theorem rest_l106fd4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106fd4 bytes_l106fd4) (entryMap (live .l106fd4))
      7 0x106fd4 bytes_l106fd4 b_l106fd4 := by
  have f0 : InstrSpec 0x106fd4 [0x4C, 0x8B, 0xA4, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x106fd4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x106fd4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106fd4 12 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x106fd4 12 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x106fd4 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106fdc [0x4C, 0x8B, 0xAC, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x106fdc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x106fdc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106fdc 13 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x106fdc 13 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x106fdc 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106fe4 [0x4C, 0x8B, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x106fe4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x106fe4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106fe4 15 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x106fe4 15 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x106fe4 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x106fec [0x4C, 0x8B, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x106fec (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x106fec + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106fec 14 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x106fec 14 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x106fec 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x106ff4 [0x0F, 0xB6, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x106ff4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x106ff4 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x106ff4 8 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x106ff4 8 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (movzx_r32_m8_effect_step 0x106ff4 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x106ffc [0x83, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x01] (LoadPre 0x106ffc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x106ffc + BitVec.ofNat 64 8)) 4) (cmpMImm8Effect 0x106ffc 8 32 (.sib 4 none 0 (.d32 0x88)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x106ffc 8 (.sib 4 none 0 (.d32 0x88)) 0x1).toInstrSpec (cmp_m32_imm8_effect_step 0x106ffc (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fdc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fe4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 55), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fec) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 55), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ff4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 55), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ffc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 55), (14, 59), (15, 57), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107004) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 65) (jcc_rel8_effect_step 0x107004 5 0x4c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106fd4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106fd4 :=
  Rest.liftedBlock (rest_l106fd4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106fd4 x hx)

theorem rest_l107006 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107006 bytes_l107006) (entryMap (live .l107006))
      18 0x107006 bytes_l107006 b_l107006 := by
  have f0 : InstrSpec 0x107006 [0x48, 0x8B, 0x4D, 0x38] (LoadPre 0x107006 (fun s => AddrMode.addr (.base 5 (.d8 0x38)) s (0x107006 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107006 1 (.base 5 (.d8 0x38)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x107006 1 (.base 5 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x107006 0x48 (by decide) 1 (.base 5 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10700a [0x48, 0x89, 0x4C, 0x24, 0x3F] (StorePre 0x10700a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x10700a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10700a 1 (.sib 4 none 0 (.d8 0x3f)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10700a 1 (.sib 4 none 0 (.d8 0x3f))).toInstrSpec (mov_m64_r64_effect_step 0x10700a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x3f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10700f [0x48, 0x8B, 0x4D, 0x29] (LoadPre 0x10700f (fun s => AddrMode.addr (.base 5 (.d8 0x29)) s (0x10700f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10700f 1 (.base 5 (.d8 0x29)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10700f 1 (.base 5 (.d8 0x29))).toInstrSpec (mov_r64_m64_effect_step 0x10700f 0x48 (by decide) 1 (.base 5 (.d8 0x29)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x107013 [0x48, 0x8B, 0x55, 0x31] (LoadPre 0x107013 (fun s => AddrMode.addr (.base 5 (.d8 0x31)) s (0x107013 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107013 2 (.base 5 (.d8 0x31)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x107013 2 (.base 5 (.d8 0x31))).toInstrSpec (mov_r64_m64_effect_step 0x107013 0x48 (by decide) 2 (.base 5 (.d8 0x31)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x107017 [0x48, 0x89, 0x54, 0x24, 0x38] (StorePre 0x107017 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107017 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107017 2 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107017 2 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x107017 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10701c [0x48, 0x89, 0x4C, 0x24, 0x30] (StorePre 0x10701c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10701c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10701c 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10701c 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10701c 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x107021 [0x48, 0x8B, 0x54, 0x24, 0x38] (LoadPre 0x107021 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107021 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107021 2 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x107021 2 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x107021 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x107026 [0x48, 0x8B, 0x74, 0x24, 0x3F] (LoadPre 0x107026 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x107026 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107026 6 (.sib 4 none 0 (.d8 0x3f)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x107026 6 (.sib 4 none 0 (.d8 0x3f))).toInstrSpec (mov_r64_m64_effect_step 0x107026 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x3f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10702b [0x48, 0x89, 0x73, 0x38] (StorePre 0x10702b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x10702b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10702b 6 (.base 3 (.d8 0x38)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10702b 6 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10702b 0x48 (by decide) 6 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10702f [0x48, 0x89, 0x53, 0x31] (StorePre 0x10702f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x31)) s (0x10702f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10702f 2 (.base 3 (.d8 0x31)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10702f 2 (.base 3 (.d8 0x31))).toInstrSpec (mov_m64_r64_effect_step 0x10702f 0x48 (by decide) 2 (.base 3 (.d8 0x31)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x107033 [0x48, 0x89, 0x4B, 0x29] (StorePre 0x107033 4 (fun s => AddrMode.addr (.base 3 (.d8 0x29)) s (0x107033 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107033 1 (.base 3 (.d8 0x29)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x107033 1 (.base 3 (.d8 0x29))).toInstrSpec (mov_m64_r64_effect_step 0x107033 0x48 (by decide) 1 (.base 3 (.d8 0x29)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x107037 [0xC6, 0x03, 0xFF] (StorePre 0x107037 3 (fun s => AddrMode.addr (.base 3 .none) s (0x107037 + BitVec.ofNat 64 3)) 1) (movM8Imm8Effect 0x107037 (.base 3 .none) 0xff)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x107037 (.base 3 .none) 0xff).toInstrSpec (mov_m8_imm8_effect_step 0x107037 (.base 3 .none) (by decide) (by decide) (by decide) 0xff) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10703a [0x4C, 0x89, 0x63, 0x08] (StorePre 0x10703a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10703a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10703a 12 (.base 3 (.d8 0x8)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10703a 12 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10703a 0x4c (by decide) 4 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x10703e [0x4C, 0x89, 0x6B, 0x10] (StorePre 0x10703e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10703e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10703e 13 (.base 3 (.d8 0x10)))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10703e 13 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10703e 0x4c (by decide) 5 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x107042 [0x4C, 0x89, 0x7B, 0x18] (StorePre 0x107042 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x107042 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107042 15 (.base 3 (.d8 0x18)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x107042 15 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x107042 0x4c (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x107046 [0x4C, 0x89, 0x73, 0x20] (StorePre 0x107046 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x107046 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107046 14 (.base 3 (.d8 0x20)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x107046 14 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x107046 0x4c (by decide) 6 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10704a [0x88, 0x43, 0x28] (StorePre 0x10704a 3 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x10704a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10704a 3 0 (.base 3 (.d8 0x28)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x10704a 3 0 (.base 3 (.d8 0x28))).toInstrSpec (mov_m8_r8_effect_step 0x10704a 0 (by decide) (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10700a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10700f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107013) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 56), (2, 58), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107017) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 56), (2, 58), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10701c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 56), (2, 58), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107021) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 56), (2, 62), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107026) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 56), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10702b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 56), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10702f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 56), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107033) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 56), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107037) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 56), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10703a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 56), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10703e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 56), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107042) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 56), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107046) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 56), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10704a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 56), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10704d) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 75) (jmp_rel32_effect_step 0x10704d 0x639 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l107006 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107006 :=
  Rest.liftedBlock (rest_l107006 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107006 x hx)

theorem rest_l107052 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107052 bytes_l107052) (entryMap (live .l107052))
      13 0x107052 bytes_l107052 b_l107052 := by
  have f0 : InstrSpec 0x107052 [0x48, 0x8B, 0x4D, 0x49] (LoadPre 0x107052 (fun s => AddrMode.addr (.base 5 (.d8 0x49)) s (0x107052 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107052 1 (.base 5 (.d8 0x49)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x107052 1 (.base 5 (.d8 0x49))).toInstrSpec (mov_r64_m64_effect_step 0x107052 0x48 (by decide) 1 (.base 5 (.d8 0x49)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107056 [0x48, 0x89, 0x4C, 0x24, 0x50] (StorePre 0x107056 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x107056 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107056 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107056 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x107056 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10705b [0x48, 0x8B, 0x55, 0x41] (LoadPre 0x10705b (fun s => AddrMode.addr (.base 5 (.d8 0x41)) s (0x10705b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10705b 2 (.base 5 (.d8 0x41)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10705b 2 (.base 5 (.d8 0x41))).toInstrSpec (mov_r64_m64_effect_step 0x10705b 0x48 (by decide) 2 (.base 5 (.d8 0x41)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10705f [0x48, 0x8B, 0x75, 0x39] (LoadPre 0x10705f (fun s => AddrMode.addr (.base 5 (.d8 0x39)) s (0x10705f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10705f 6 (.base 5 (.d8 0x39)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10705f 6 (.base 5 (.d8 0x39))).toInstrSpec (mov_r64_m64_effect_step 0x10705f 0x48 (by decide) 6 (.base 5 (.d8 0x39)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x107063 [0x48, 0x8B, 0x7D, 0x29] (LoadPre 0x107063 (fun s => AddrMode.addr (.base 5 (.d8 0x29)) s (0x107063 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107063 7 (.base 5 (.d8 0x29)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x107063 7 (.base 5 (.d8 0x29))).toInstrSpec (mov_r64_m64_effect_step 0x107063 0x48 (by decide) 7 (.base 5 (.d8 0x29)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x107067 [0x4C, 0x8B, 0x45, 0x31] (LoadPre 0x107067 (fun s => AddrMode.addr (.base 5 (.d8 0x31)) s (0x107067 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107067 8 (.base 5 (.d8 0x31)))
      [.gpr 5] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x107067 8 (.base 5 (.d8 0x31))).toInstrSpec (mov_r64_m64_effect_step 0x107067 0x4c (by decide) 0 (.base 5 (.d8 0x31)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10706b [0x48, 0x89, 0xBC, 0x24, 0x68, 0x01, 0x00, 0x00] (StorePre 0x10706b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10706b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10706b 7 (.sib 4 none 0 (.d32 0x168)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10706b 7 (.sib 4 none 0 (.d32 0x168))).toInstrSpec (mov_m64_r64_effect_step 0x10706b 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x107073 [0x4C, 0x89, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00] (StorePre 0x107073 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x107073 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107073 8 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107073 8 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (mov_m64_r64_effect_step 0x107073 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10707b [0x48, 0x89, 0xB4, 0x24, 0x78, 0x01, 0x00, 0x00] (StorePre 0x10707b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x10707b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10707b 6 (.sib 4 none 0 (.d32 0x178)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10707b 6 (.sib 4 none 0 (.d32 0x178))).toInstrSpec (mov_m64_r64_effect_step 0x10707b 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x178)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x107083 [0x48, 0x89, 0x94, 0x24, 0x80, 0x01, 0x00, 0x00] (StorePre 0x107083 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x107083 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107083 2 (.sib 4 none 0 (.d32 0x180)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107083 2 (.sib 4 none 0 (.d32 0x180))).toInstrSpec (mov_m64_r64_effect_step 0x107083 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x180)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10708b [0x48, 0x89, 0x8C, 0x24, 0x88, 0x01, 0x00, 0x00] (StorePre 0x10708b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x10708b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10708b 1 (.sib 4 none 0 (.d32 0x188)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10708b 1 (.sib 4 none 0 (.d32 0x188))).toInstrSpec (mov_m64_r64_effect_step 0x10708b 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x188)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x107093 [0x3C, 0x01] (fun s => s.RIP = 0x107093) (cmpAlImm8Effect 0x107093 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x107093 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x107093 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107056) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10705b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 56), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10705f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (2, 56), (3, 3), (4, 4), (5, 5), (6, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107063) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 56), (3, 3), (4, 4), (5, 5), (6, 58), (7, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107067) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 56), (3, 3), (4, 4), (5, 5), (6, 58), (7, 60), (8, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10706b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 56), (3, 3), (4, 4), (5, 5), (6, 58), (7, 60), (8, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107073) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 53), (2, 56), (3, 3), (4, 4), (5, 5), (6, 58), (7, 60), (8, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10707b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 56), (3, 3), (4, 4), (5, 5), (6, 58), (7, 60), (8, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107083) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 53), (2, 56), (3, 3), (4, 4), (5, 5), (6, 58), (7, 60), (8, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10708b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 53), (2, 56), (3, 3), (4, 4), (5, 5), (6, 58), (7, 60), (8, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107093) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 53), (2, 56), (3, 3), (4, 4), (5, 5), (6, 58), (7, 60), (8, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107095) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel8_effect_step 0x107095 5 0x79) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l107052 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107052 :=
  Rest.liftedBlock (rest_l107052 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107052 x hx)

theorem rest_l107097 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107097 bytes_l107097) (entryMap (live .l107097))
      12 0x107097 bytes_l107097 b_l107097 := by
  have f0 : InstrSpec 0x107097 [0x48, 0x8B, 0x84, 0x24, 0x88, 0x01, 0x00, 0x00] (LoadPre 0x107097 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x107097 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107097 0 (.sib 4 none 0 (.d32 0x188)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107097 0 (.sib 4 none 0 (.d32 0x188))).toInstrSpec (mov_r64_m64_effect_step 0x107097 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x188)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10709f [0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x10709f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10709f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10709f 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10709f 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x10709f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1070a7 [0x48, 0x8B, 0x84, 0x24, 0x80, 0x01, 0x00, 0x00] (LoadPre 0x1070a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x1070a7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1070a7 0 (.sib 4 none 0 (.d32 0x180)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1070a7 0 (.sib 4 none 0 (.d32 0x180))).toInstrSpec (mov_r64_m64_effect_step 0x1070a7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x180)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1070af [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x1070af 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1070af + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1070af 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1070af 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x1070af 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1070b7 [0x48, 0x8B, 0x84, 0x24, 0x78, 0x01, 0x00, 0x00] (LoadPre 0x1070b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x1070b7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1070b7 0 (.sib 4 none 0 (.d32 0x178)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1070b7 0 (.sib 4 none 0 (.d32 0x178))).toInstrSpec (mov_r64_m64_effect_step 0x1070b7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x178)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1070bf [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x1070bf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1070bf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1070bf 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1070bf 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x1070bf 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1070c7 [0x48, 0x8B, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00] (LoadPre 0x1070c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x1070c7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1070c7 0 (.sib 4 none 0 (.d32 0x168)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1070c7 0 (.sib 4 none 0 (.d32 0x168))).toInstrSpec (mov_r64_m64_effect_step 0x1070c7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1070cf [0x48, 0x8B, 0x8C, 0x24, 0x70, 0x01, 0x00, 0x00] (LoadPre 0x1070cf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x1070cf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1070cf 1 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1070cf 1 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (mov_r64_m64_effect_step 0x1070cf 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1070d7 [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x1070d7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1070d7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1070d7 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1070d7 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x1070d7 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1070df [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1070df 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1070df + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1070df 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1070df 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x1070df 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1070e7 [0x3C, 0x05] (fun s => s.RIP = 0x1070e7) (cmpAlImm8Effect 0x1070e7 0x5)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x1070e7 0x5).toInstrSpec (cmp_al_imm8_effect_step 0x1070e7 0x5) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10709f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070a7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070af) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070b7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070bf) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070c7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070cf) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070d7) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070df) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070e7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070e9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 70) (jcc_rel8_effect_step 0x1070e9 5 0x1e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l107097 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107097 :=
  Rest.liftedBlock (rest_l107097 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107097 x hx)

theorem rest_l1070eb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1070eb bytes_l1070eb) (entryMap (live .l1070eb))
      4 0x1070eb bytes_l1070eb b_l1070eb := by
  have f0 : InstrSpec 0x1070eb [0x48, 0x8D, 0xB4, 0x24, 0x89, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1070eb) (leaR64Effect 0x1070eb 6 (.sib 4 none 0 (.d32 0x89)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1070eb 6 (.sib 4 none 0 (.d32 0x89))).toInstrSpec (lea_r64_effect_step 0x1070eb 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x89)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1070f3 [0xBA, 0x27, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1070f3) (movR32Imm32Effect 0x1070f3 5 2 0x27)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1070f3 5 2 0x27).toInstrSpec (mov_r32_imm32_effect_step 0x1070f3 0xba (by decide) 0x27) pre_rip
  have f2 : InstrSpec 0x1070f8 [0x48, 0xC7, 0xC7, 0xB9, 0x28, 0x20, 0x00] (fun s => s.RIP = 0x1070f8) (movR64Imm32Effect 0x1070f8 7 0x2028b9)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x1070f8 7 0x2028b9).toInstrSpec (mov_r64_imm32_effect_step 0x1070f8 0x48 0xc7 (by decide) (by decide) (by decide) 0x2028b9) pre_rip
  have f3 : InstrSpec 0x1070ff [0xFF, 0x15, 0xFB, 0xCC, 0x0F, 0x00] (GoesTo (CallMemPre 0x1070ff (.rip 0xfccfb)) (callEffect (callMemPtr 0x1070ff (.rip 0xfccfb)) (0x1070ff + BitVec.ofNat 64 (callMemLen (.rip 0xfccfb)))) 0x12a750) (callEffect (callMemPtr 0x1070ff (.rip 0xfccfb)) (0x1070ff + BitVec.ofNat 64 (callMemLen (.rip 0xfccfb))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1070ff (.rip 0xfccfb)).toInstrSpec (call_m64_effect_step 0x1070ff (.rip 0xfccfb) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a750
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070f3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070f8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1070ff) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 59), (5, 5), (6, 53), (7, 57), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a750) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1070eb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1070eb :=
  Rest.liftedBlock (rest_l1070eb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1070eb x hx)

theorem rest_l107105 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107105 bytes_l107105) (entryMap (live .l107105))
      2 0x107105 bytes_l107105 b_l107105 := by
  have f0 : InstrSpec 0x107105 [0x85, 0xC0] (fun s => s.RIP = 0x107105) (testR32R32Effect 0x107105 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR32R32Effect_footprint 0x107105 2 0 0).toInstrSpec (test_r32_r32_effect_step 0x107105 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107107) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x107107 4 0x7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l107105 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107105 :=
  Rest.liftedBlock (rest_l107105 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107105 x hx)

theorem rest_l107109 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107109 bytes_l107109) (entryMap (live .l107109))
      2 0x107109 bytes_l107109 b_l107109 := by
  have f0 : InstrSpec 0x107109 [0xB0, 0x05] (fun s => s.RIP = 0x107109) (movR8Imm8Effect 0x107109 2 0 0x5)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x107109 2 0 0x5).toInstrSpec (mov_r8_imm8_effect_step 0x107109 0xb0 (by decide) 0x5) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10710b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x10710b 0x513 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l107109 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107109 :=
  Rest.liftedBlock (rest_l107109 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107109 x hx)

theorem rest_l107110 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107110 bytes_l107110) (entryMap (live .l107110))
      2 0x107110 bytes_l107110 b_l107110 := by
  have f0 : InstrSpec 0x107110 [0x49, 0x83, 0xFD, 0x20] (fun s => s.RIP = 0x107110) (cmpR64Imm8Effect 0x107110 13 0x20)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x107110 13 0x20).toInstrSpec (cmp_r64_imm8_effect_step 0x107110 0x49 0xfd 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107114) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x107114 5 0x23) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l107110 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107110 :=
  Rest.liftedBlock (rest_l107110 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107110 x hx)

theorem rest_l107116 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107116 bytes_l107116) (entryMap (live .l107116))
      3 0x107116 bytes_l107116 b_l107116 := by
  have f0 : InstrSpec 0x107116 [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107116) (leaR64Effect 0x107116 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x107116 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x107116 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10711e [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x10711e) (movR64R64Effect 0x10711e 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10711e 6 12).toInstrSpec (mov_r64_r64_effect_step 0x10711e 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x107121 [0xE8, 0xAA, 0xFC, 0xFF, 0xFF] (PushPre 0x107121 5) (callEffect (fun _ => 0x106dd0) 0x107126)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107121 0x106dd0 0x107126).toInstrSpec (call_rel32_effect_step 0x107121 0xfffffcaa (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10711e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107121) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dd0) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l107116 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107116 :=
  Rest.liftedBlock (rest_l107116 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107116 x hx)

theorem rest_l107126 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107126 bytes_l107126) (entryMap (live .l107126))
      2 0x107126 bytes_l107126 b_l107126 := by
  have f0 : InstrSpec 0x107126 [0x80, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00] (LoadPre 0x107126 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107126 + BitVec.ofNat 64 8)) 1) (cmpM8Imm8Effect 0x107126 8 (.sib 4 none 0 (.d32 0x88)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x107126 8 (.sib 4 none 0 (.d32 0x88)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x107126 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10712e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10712e 4 0x119) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l107126 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107126 :=
  Rest.liftedBlock (rest_l107126 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107126 x hx)

theorem rest_l107134 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107134 bytes_l107134) (entryMap (live .l107134))
      1 0x107134 bytes_l107134 b_l107134 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x107134 0x3fc (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l107134 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107134 :=
  Rest.liftedBlock (rest_l107134 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107134 x hx)

theorem rest_l107139 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107139 bytes_l107139) (entryMap (live .l107139))
      4 0x107139 bytes_l107139 b_l107139 := by
  have f0 : InstrSpec 0x107139 [0x48, 0xB8, 0xF8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x107139) (movR64Imm64Effect 0x107139 0 0x7ffffffffffffff8)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x107139 0 0x7ffffffffffffff8).toInstrSpec (mov_r64_imm64_effect_step 0x107139 0x48 0xb8 (by decide) (by decide) 0x7ffffffffffffff8) pre_rip
  have f1 : InstrSpec 0x107143 [0x4C, 0x21, 0xE8] (fun s => s.RIP = 0x107143) (andR64R64Effect 0x107143 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107143 0 13).toInstrSpec (and_r64_r64_effect_step 0x107143 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x107146 [0x48, 0x83, 0xF8, 0x18] (fun s => s.RIP = 0x107146) (cmpR64Imm8Effect 0x107146 0 0x18)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x107146 0 0x18).toInstrSpec (cmp_r64_imm8_effect_step 0x107146 0x48 0xf8 0x18 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107143) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107146) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10714a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x10714a 5 0x3cb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l107139 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107139 :=
  Rest.liftedBlock (rest_l107139 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107139 x hx)

theorem rest_l107150 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107150 bytes_l107150) (entryMap (live .l107150))
      11 0x107150 bytes_l107150 b_l107150 := by
  have f0 : InstrSpec 0x107150 [0x48, 0xC7, 0x44, 0x24, 0x48, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107150 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x107150 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107150 (.sib 4 none 0 (.d8 0x48)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107150 (.sib 4 none 0 (.d8 0x48)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107150 0x48 (by decide) (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x107159 [0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107159 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107159 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107159 (.sib 4 none 0 (.d8 0x40)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107159 (.sib 4 none 0 (.d8 0x40)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107159 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x107162 [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107162 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107162 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107162 (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107162 (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107162 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10716b [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10716b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10716b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10716b (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10716b (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10716b 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x107174 [0x48, 0x8D, 0x6C, 0x24, 0x30] (fun s => s.RIP = 0x107174) (leaR64Effect 0x107174 5 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x107174 5 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x107174 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x107179 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x107179) (movR64R64Effect 0x107179 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107179 7 5).toInstrSpec (mov_r64_r64_effect_step 0x107179 0x48 0xef (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10717c [0x4C, 0x29, 0xEF] (fun s => s.RIP = 0x10717c) (subR64R64Effect 0x10717c 7 13)
      [.gpr 7, .gpr 13] [] [.reg 7, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10717c 7 13).toInstrSpec (sub_r64_r64_effect_step 0x10717c 0x4c 0xef (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10717f [0x48, 0x83, 0xC7, 0x20] (fun s => s.RIP = 0x10717f) (addR64Imm8Effect 0x10717f 7 0x20)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10717f 7 0x20).toInstrSpec (add_r64_imm8_effect_step 0x10717f 0x48 0xc7 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x107183 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x107183) (movR64R64Effect 0x107183 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x107183 6 12).toInstrSpec (mov_r64_r64_effect_step 0x107183 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x107186 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x107186) (movR64R64Effect 0x107186 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x107186 2 13).toInstrSpec (mov_r64_r64_effect_step 0x107186 0x4c 0xea (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x107189 [0xFF, 0x15, 0x41, 0xCC, 0x0F, 0x00] (GoesTo (CallMemPre 0x107189 (.rip 0xfcc41)) (callEffect (callMemPtr 0x107189 (.rip 0xfcc41)) (0x107189 + BitVec.ofNat 64 (callMemLen (.rip 0xfcc41)))) 0x12a820) (callEffect (callMemPtr 0x107189 (.rip 0xfcc41)) (0x107189 + BitVec.ofNat 64 (callMemLen (.rip 0xfcc41))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x107189 (.rip 0xfcc41)).toInstrSpec (call_m64_effect_step 0x107189 (.rip 0xfcc41) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107159) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107162) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10716b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107174) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107179) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 57), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10717c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 57), (7, 61), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10717f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 4), (5, 57), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107183) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 4), (5, 57), (6, 65), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107186) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 67), (3, 3), (4, 4), (5, 57), (6, 65), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107189) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 67), (3, 3), (4, 69), (5, 57), (6, 65), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f10 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l107150 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107150 :=
  Rest.liftedBlock (rest_l107150 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107150 x hx)

theorem rest_l10718f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10718f bytes_l10718f) (entryMap (live .l10718f))
      3 0x10718f bytes_l10718f b_l10718f := by
  have f0 : InstrSpec 0x10718f [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10718f) (leaR64Effect 0x10718f 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10718f 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x10718f 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x107197 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x107197) (movR64R64Effect 0x107197 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x107197 6 5).toInstrSpec (mov_r64_r64_effect_step 0x107197 0x48 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10719a [0xE8, 0x31, 0xFC, 0xFF, 0xFF] (PushPre 0x10719a 5) (callEffect (fun _ => 0x106dd0) 0x10719f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10719a 0x106dd0 0x10719f).toInstrSpec (call_rel32_effect_step 0x10719a 0xfffffc31 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107197) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10719a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dd0) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l10718f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10718f :=
  Rest.liftedBlock (rest_l10718f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10718f x hx)

theorem rest_l10719f_1 [Bindings] (code : CodeMap) :
    Rest (n := 73) code lifted (codeRange 0x10719f bytes_l10719f) [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      14 0x107203 bytes_l10719f_1 b_l10719f_1 := by
  have f20 : InstrSpec 0x107203 [0xC6, 0x44, 0x24, 0x44, 0x00] (StorePre 0x107203 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x107203 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107203 (.sib 4 none 0 (.d8 0x44)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x107203 (.sib 4 none 0 (.d8 0x44)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x107203 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x107208 [0xC6, 0x44, 0x24, 0x45, 0x00] (StorePre 0x107208 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x45)) s (0x107208 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107208 (.sib 4 none 0 (.d8 0x45)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x107208 (.sib 4 none 0 (.d8 0x45)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x107208 (.sib 4 none 0 (.d8 0x45)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x10720d [0xC6, 0x44, 0x24, 0x46, 0x00] (StorePre 0x10720d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x10720d + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x10720d (.sib 4 none 0 (.d8 0x46)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x10720d (.sib 4 none 0 (.d8 0x46)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x10720d (.sib 4 none 0 (.d8 0x46)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x107212 [0xC6, 0x44, 0x24, 0x47, 0x00] (StorePre 0x107212 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x107212 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107212 (.sib 4 none 0 (.d8 0x47)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x107212 (.sib 4 none 0 (.d8 0x47)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x107212 (.sib 4 none 0 (.d8 0x47)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x107217 [0xC6, 0x44, 0x24, 0x48, 0x00] (StorePre 0x107217 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x107217 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107217 (.sib 4 none 0 (.d8 0x48)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x107217 (.sib 4 none 0 (.d8 0x48)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x107217 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x10721c [0xC6, 0x44, 0x24, 0x49, 0x00] (StorePre 0x10721c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x49)) s (0x10721c + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x10721c (.sib 4 none 0 (.d8 0x49)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x10721c (.sib 4 none 0 (.d8 0x49)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x10721c (.sib 4 none 0 (.d8 0x49)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x107221 [0xC6, 0x44, 0x24, 0x4A, 0x00] (StorePre 0x107221 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x107221 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107221 (.sib 4 none 0 (.d8 0x4a)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x107221 (.sib 4 none 0 (.d8 0x4a)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x107221 (.sib 4 none 0 (.d8 0x4a)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x107226 [0xC6, 0x44, 0x24, 0x4B, 0x00] (StorePre 0x107226 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x107226 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107226 (.sib 4 none 0 (.d8 0x4b)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x107226 (.sib 4 none 0 (.d8 0x4b)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x107226 (.sib 4 none 0 (.d8 0x4b)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x10722b [0xC6, 0x44, 0x24, 0x4C, 0x00] (StorePre 0x10722b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x10722b + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x10722b (.sib 4 none 0 (.d8 0x4c)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x10722b (.sib 4 none 0 (.d8 0x4c)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x10722b (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x107230 [0xC6, 0x44, 0x24, 0x4D, 0x00] (StorePre 0x107230 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x107230 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107230 (.sib 4 none 0 (.d8 0x4d)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x107230 (.sib 4 none 0 (.d8 0x4d)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x107230 (.sib 4 none 0 (.d8 0x4d)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x107235 [0xC6, 0x44, 0x24, 0x4E, 0x00] (StorePre 0x107235 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x107235 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107235 (.sib 4 none 0 (.d8 0x4e)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x107235 (.sib 4 none 0 (.d8 0x4e)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x107235 (.sib 4 none 0 (.d8 0x4e)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x10723a [0xC6, 0x44, 0x24, 0x4F, 0x00] (StorePre 0x10723a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x10723a + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x10723a (.sib 4 none 0 (.d8 0x4f)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x10723a (.sib 4 none 0 (.d8 0x4f)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x10723a (.sib 4 none 0 (.d8 0x4f)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x10723f [0x80, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00] (LoadPre 0x10723f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10723f + BitVec.ofNat 64 8)) 1) (cmpM8Imm8Effect 0x10723f 8 (.sib 4 none 0 (.d32 0x88)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x10723f 8 (.sib 4 none 0 (.d32 0x88)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x10723f (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107208) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10720d) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107212) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107217) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10721c) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107221) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107226) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10722b) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107230) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107235) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10723a) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10723f) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f32 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107247) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 87) (jcc_rel32_effect_step 0x107247 5 0x2e8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l10719f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10719f bytes_l10719f) (entryMap (live .l10719f))
      34 0x10719f bytes_l10719f b_l10719f := by
  have f0 : InstrSpec 0x10719f [0xC6, 0x44, 0x24, 0x30, 0x00] (StorePre 0x10719f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10719f + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x10719f (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x10719f (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x10719f (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1071a4 [0xC6, 0x44, 0x24, 0x31, 0x00] (StorePre 0x1071a4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x1071a4 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071a4 (.sib 4 none 0 (.d8 0x31)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071a4 (.sib 4 none 0 (.d8 0x31)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071a4 (.sib 4 none 0 (.d8 0x31)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1071a9 [0xC6, 0x44, 0x24, 0x32, 0x00] (StorePre 0x1071a9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x1071a9 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071a9 (.sib 4 none 0 (.d8 0x32)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071a9 (.sib 4 none 0 (.d8 0x32)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071a9 (.sib 4 none 0 (.d8 0x32)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1071ae [0xC6, 0x44, 0x24, 0x33, 0x00] (StorePre 0x1071ae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x33)) s (0x1071ae + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071ae (.sib 4 none 0 (.d8 0x33)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071ae (.sib 4 none 0 (.d8 0x33)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071ae (.sib 4 none 0 (.d8 0x33)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1071b3 [0xC6, 0x44, 0x24, 0x34, 0x00] (StorePre 0x1071b3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1071b3 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071b3 (.sib 4 none 0 (.d8 0x34)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071b3 (.sib 4 none 0 (.d8 0x34)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071b3 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1071b8 [0xC6, 0x44, 0x24, 0x35, 0x00] (StorePre 0x1071b8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x1071b8 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071b8 (.sib 4 none 0 (.d8 0x35)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071b8 (.sib 4 none 0 (.d8 0x35)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071b8 (.sib 4 none 0 (.d8 0x35)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1071bd [0xC6, 0x44, 0x24, 0x36, 0x00] (StorePre 0x1071bd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x1071bd + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071bd (.sib 4 none 0 (.d8 0x36)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071bd (.sib 4 none 0 (.d8 0x36)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071bd (.sib 4 none 0 (.d8 0x36)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1071c2 [0xC6, 0x44, 0x24, 0x37, 0x00] (StorePre 0x1071c2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x37)) s (0x1071c2 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071c2 (.sib 4 none 0 (.d8 0x37)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071c2 (.sib 4 none 0 (.d8 0x37)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071c2 (.sib 4 none 0 (.d8 0x37)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1071c7 [0xC6, 0x44, 0x24, 0x38, 0x00] (StorePre 0x1071c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1071c7 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071c7 (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071c7 (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071c7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1071cc [0xC6, 0x44, 0x24, 0x39, 0x00] (StorePre 0x1071cc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x1071cc + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071cc (.sib 4 none 0 (.d8 0x39)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071cc (.sib 4 none 0 (.d8 0x39)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071cc (.sib 4 none 0 (.d8 0x39)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1071d1 [0xC6, 0x44, 0x24, 0x3A, 0x00] (StorePre 0x1071d1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x1071d1 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071d1 (.sib 4 none 0 (.d8 0x3a)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071d1 (.sib 4 none 0 (.d8 0x3a)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071d1 (.sib 4 none 0 (.d8 0x3a)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1071d6 [0xC6, 0x44, 0x24, 0x3B, 0x00] (StorePre 0x1071d6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3b)) s (0x1071d6 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071d6 (.sib 4 none 0 (.d8 0x3b)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071d6 (.sib 4 none 0 (.d8 0x3b)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071d6 (.sib 4 none 0 (.d8 0x3b)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1071db [0xC6, 0x44, 0x24, 0x3C, 0x00] (StorePre 0x1071db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x1071db + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071db (.sib 4 none 0 (.d8 0x3c)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071db (.sib 4 none 0 (.d8 0x3c)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071db (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1071e0 [0xC6, 0x44, 0x24, 0x3D, 0x00] (StorePre 0x1071e0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3d)) s (0x1071e0 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071e0 (.sib 4 none 0 (.d8 0x3d)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071e0 (.sib 4 none 0 (.d8 0x3d)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071e0 (.sib 4 none 0 (.d8 0x3d)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1071e5 [0xC6, 0x44, 0x24, 0x3E, 0x00] (StorePre 0x1071e5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x1071e5 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071e5 (.sib 4 none 0 (.d8 0x3e)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071e5 (.sib 4 none 0 (.d8 0x3e)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071e5 (.sib 4 none 0 (.d8 0x3e)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1071ea [0xC6, 0x44, 0x24, 0x3F, 0x00] (StorePre 0x1071ea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x1071ea + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071ea (.sib 4 none 0 (.d8 0x3f)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071ea (.sib 4 none 0 (.d8 0x3f)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071ea (.sib 4 none 0 (.d8 0x3f)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1071ef [0xC6, 0x44, 0x24, 0x40, 0x00] (StorePre 0x1071ef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1071ef + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071ef (.sib 4 none 0 (.d8 0x40)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071ef (.sib 4 none 0 (.d8 0x40)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071ef (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1071f4 [0xC6, 0x44, 0x24, 0x41, 0x00] (StorePre 0x1071f4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x1071f4 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071f4 (.sib 4 none 0 (.d8 0x41)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071f4 (.sib 4 none 0 (.d8 0x41)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071f4 (.sib 4 none 0 (.d8 0x41)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1071f9 [0xC6, 0x44, 0x24, 0x42, 0x00] (StorePre 0x1071f9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x1071f9 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071f9 (.sib 4 none 0 (.d8 0x42)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071f9 (.sib 4 none 0 (.d8 0x42)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071f9 (.sib 4 none 0 (.d8 0x42)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1071fe [0xC6, 0x44, 0x24, 0x43, 0x00] (StorePre 0x1071fe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x43)) s (0x1071fe + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071fe (.sib 4 none 0 (.d8 0x43)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1071fe (.sib 4 none 0 (.d8 0x43)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1071fe (.sib 4 none 0 (.d8 0x43)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071a4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071a9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071ae) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071b3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071b8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071bd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071c2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071c7) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071cc) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071d1) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071d6) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071db) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071e0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071e5) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071ea) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071ef) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071f4) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071f9) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1071fe) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107203) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10719f_1 code

theorem block_l10719f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10719f :=
  Rest.liftedBlock (rest_l10719f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10719f x hx)

theorem rest_l10724d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10724d bytes_l10724d) (entryMap (live .l10724d))
      16 0x10724d bytes_l10724d b_l10724d := by
  have f0 : InstrSpec 0x10724d [0x0F, 0xB6, 0xAC, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x10724d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10724d + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10724d 8 5 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x10724d 8 5 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (movzx_r32_m8_effect_step 0x10724d 5 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107255 [0x0F, 0xB7, 0x84, 0x24, 0x91, 0x00, 0x00, 0x00] (LoadPre 0x107255 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x91)) s (0x107255 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x107255 8 0 (.sib 4 none 0 (.d32 0x91)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x107255 8 0 (.sib 4 none 0 (.d32 0x91))).toInstrSpec (movzx_r32_m16_effect_step 0x107255 0 (.sib 4 none 0 (.d32 0x91)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10725d [0x66, 0x89, 0x04, 0x24] (StorePre 0x10725d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10725d + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10725d 4 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10725d 4 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m16_r16_effect_step 0x10725d 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x107261 [0x0F, 0xB6, 0x84, 0x24, 0x93, 0x00, 0x00, 0x00] (LoadPre 0x107261 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x93)) s (0x107261 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107261 8 0 (.sib 4 none 0 (.d32 0x93)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x107261 8 0 (.sib 4 none 0 (.d32 0x93))).toInstrSpec (movzx_r32_m8_effect_step 0x107261 0 (.sib 4 none 0 (.d32 0x93)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x107269 [0x88, 0x44, 0x24, 0x02] (StorePre 0x107269 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x107269 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107269 4 0 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107269 4 0 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (mov_m8_r8_effect_step 0x107269 0 (by decide) (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10726d [0x44, 0x0F, 0xB6, 0xA4, 0x24, 0x94, 0x00, 0x00, 0x00] (LoadPre 0x10726d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x10726d + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x10726d 9 12 (.sib 4 none 0 (.d32 0x94)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x10726d 9 12 (.sib 4 none 0 (.d32 0x94))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10726d 0x44 (by decide) 4 (.sib 4 none 0 (.d32 0x94)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x107276 [0x48, 0x8B, 0x84, 0x24, 0x95, 0x00, 0x00, 0x00] (LoadPre 0x107276 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x95)) s (0x107276 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107276 0 (.sib 4 none 0 (.d32 0x95)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107276 0 (.sib 4 none 0 (.d32 0x95))).toInstrSpec (mov_r64_m64_effect_step 0x107276 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x95)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10727e [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x10727e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10727e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10727e 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10727e 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10727e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x107283 [0x48, 0x8B, 0x84, 0x24, 0x9D, 0x00, 0x00, 0x00] (LoadPre 0x107283 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9d)) s (0x107283 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107283 0 (.sib 4 none 0 (.d32 0x9d)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107283 0 (.sib 4 none 0 (.d32 0x9d))).toInstrSpec (mov_r64_m64_effect_step 0x107283 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x9d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10728b [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x10728b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10728b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10728b 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10728b 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10728b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x107290 [0x48, 0x8B, 0x84, 0x24, 0xA5, 0x00, 0x00, 0x00] (LoadPre 0x107290 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa5)) s (0x107290 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107290 0 (.sib 4 none 0 (.d32 0xa5)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107290 0 (.sib 4 none 0 (.d32 0xa5))).toInstrSpec (mov_r64_m64_effect_step 0x107290 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x107298 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x107298 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107298 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107298 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107298 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x107298 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10729d [0x8B, 0x84, 0x24, 0xAC, 0x00, 0x00, 0x00] (LoadPre 0x10729d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x10729d + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x10729d 0 (.sib 4 none 0 (.d32 0xac)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x10729d 0 (.sib 4 none 0 (.d32 0xac))).toInstrSpec (mov_r32_m32_low_effect_step 0x10729d 0 (.sib 4 none 0 (.d32 0xac)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1072a4 [0x89, 0x44, 0x24, 0x27] (StorePre 0x1072a4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x1072a4 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1072a4 0 (.sib 4 none 0 (.d8 0x27)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1072a4 0 (.sib 4 none 0 (.d8 0x27))).toInstrSpec (mov_m32_r32_low_effect_step 0x1072a4 0 (.sib 4 none 0 (.d8 0x27)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1072a8 [0x4D, 0x85, 0xFF] (fun s => s.RIP = 0x1072a8) (testR64R64Effect 0x1072a8 15 15)
      [.gpr 15, .gpr 15] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1072a8 15 15).toInstrSpec (test_r64_r64_effect_step 0x1072a8 0x4d 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107255) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10725d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107261) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107269) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10726d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 58), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107276) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10727e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107283) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10728b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107290) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107298) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10729d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072a4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072a8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 72), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072ab) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 77) (jcc_rel32_effect_step 0x1072ab 4 0x3ef) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10724d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10724d :=
  Rest.liftedBlock (rest_l10724d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10724d x hx)

theorem rest_l1072b1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1072b1 bytes_l1072b1) (entryMap (live .l1072b1))
      2 0x1072b1 bytes_l1072b1 b_l1072b1 := by
  have f0 : InstrSpec 0x1072b1 [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x1072b1) (testR64R64Effect 0x1072b1 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1072b1 14 14).toInstrSpec (test_r64_r64_effect_step 0x1072b1 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072b4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1072b4 4 0x2b2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1072b1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1072b1 :=
  Rest.liftedBlock (rest_l1072b1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1072b1 x hx)

theorem rest_l1072ba [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1072ba bytes_l1072ba) (entryMap (live .l1072ba))
      8 0x1072ba bytes_l1072ba b_l1072ba := by
  have f0 : InstrSpec 0x1072ba [0x41, 0x0F, 0xB6, 0x0F] (LoadPre 0x1072ba (fun s => AddrMode.addr (.base 15 .none) s (0x1072ba + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1072ba 4 1 (.base 15 .none))
      [.gpr 15] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1072ba 4 1 (.base 15 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1072ba 0x41 (by decide) 1 (.base 15 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1072be [0x48, 0x83, 0xF9, 0x06] (fun s => s.RIP = 0x1072be) (cmpR64Imm8Effect 0x1072be 1 0x6)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1072be 1 0x6).toInstrSpec (cmp_r64_imm8_effect_step 0x1072be 0x48 0xf9 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1072c2 [0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x1072c2) (atFlags (condHolds 2) (setccR8Effect 0x1072c2 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x1072c2 3 0 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1072c2 2 0xc0 (by decide) (by decide) c)) pre_rip
  have f3 : InstrSpec 0x1072c5 [0xB2, 0x3D] (fun s => s.RIP = 0x1072c5) (movR8Imm8Effect 0x1072c5 2 2 0x3d)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR8Imm8Effect_footprint 0x1072c5 2 2 0x3d).toInstrSpec (mov_r8_imm8_effect_step 0x1072c5 0xb2 (by decide) 0x3d) pre_rip
  have f4 : InstrSpec 0x1072c7 [0xD2, 0xEA] (fun s => s.RIP = 0x1072c7) (shrR8ClEffect 0x1072c7 2 2)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR8ClEffect_footprint 0x1072c7 2 2).toInstrSpec (shr_r8_cl_effect_step 0x1072c7 0xea (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1072c9 [0x20, 0xC2] (fun s => s.RIP = 0x1072c9) (andR8R8Effect 0x1072c9 2 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (andR8R8Effect_footprint 0x1072c9 2 2 0).toInstrSpec (and_r8_r8_effect_step 0x1072c9 0xc2 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1072cb [0x80, 0xFA, 0x01] (fun s => s.RIP = 0x1072cb) (cmpR8Imm8Effect 0x1072cb 3 2 0x1)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1072cb 3 2 0x1).toInstrSpec (cmp_r8_imm8_effect_step 0x1072cb 0xfa 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072be) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072c2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072c5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 53), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072c7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 53), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072c9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 53), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072cb) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 53), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072ce) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 67) (jcc_rel32_effect_step 0x1072ce 5 0x298) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1072ba [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1072ba :=
  Rest.liftedBlock (rest_l1072ba code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1072ba x hx)

theorem rest_l1072d4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1072d4 bytes_l1072d4) (entryMap (live .l1072d4))
      2 0x1072d4 bytes_l1072d4 b_l1072d4 := by
  have f0 : InstrSpec 0x1072d4 [0x4C, 0x3B, 0x34, 0xCD, 0xD8, 0x2A, 0x20, 0x00] (LoadPre 0x1072d4 (fun s => AddrMode.addr (.abs (some 1) 3 0x202ad8) s (0x1072d4 + BitVec.ofNat 64 8)) 8) (cmpR64M64Effect 0x1072d4 14 (.abs (some 1) 3 0x202ad8))
      [.gpr 14, .gpr 1] [] [.flags, .rip] :=
    (cmpR64M64Effect_footprint 0x1072d4 14 (.abs (some 1) 3 0x202ad8)).toInstrSpec (cmp_r64_m64_effect_step 0x1072d4 0x4c (by decide) 6 (.abs (some 1) 3 0x202ad8) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072dc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1072dc 5 0x28a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1072d4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1072d4 :=
  Rest.liftedBlock (rest_l1072d4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1072d4 x hx)

theorem rest_l1072e2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1072e2 bytes_l1072e2) (entryMap (live .l1072e2))
      9 0x1072e2 bytes_l1072e2 b_l1072e2 := by
  have f0 : InstrSpec 0x1072e2 [0xB8, 0x41, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1072e2) (movR32Imm32Effect 0x1072e2 5 0 0x41)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1072e2 5 0 0x41).toInstrSpec (mov_r32_imm32_effect_step 0x1072e2 0xb8 (by decide) 0x41) pre_rip
  have f1 : InstrSpec 0x1072e7 [0x4C, 0x29, 0xF0] (fun s => s.RIP = 0x1072e7) (subR64R64Effect 0x1072e7 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1072e7 0 14).toInstrSpec (sub_r64_r64_effect_step 0x1072e7 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1072ea [0x31, 0xD2] (fun s => s.RIP = 0x1072ea) (xorR32R32Effect 0x1072ea 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1072ea 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x1072ea 0xd2 (by decide)) pre_rip
  have f3 : InstrSpec 0x1072ec [0x49, 0x83, 0xFE, 0x41] (fun s => s.RIP = 0x1072ec) (cmpR64Imm8Effect 0x1072ec 14 0x41)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1072ec 14 0x41).toInstrSpec (cmp_r64_imm8_effect_step 0x1072ec 0x49 0xfe 0x41 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1072f0 [0x48, 0x0F, 0x42, 0xD0] (fun s => s.RIP = 0x1072f0) (atFlags (condHolds 2) (cmovR64R64Effect 0x1072f0 4 2 0))
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x1072f0 4 2 0 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1072f0 2 0x48 (by decide) 0xd0 (by decide) c)) pre_rip
  have f5 : InstrSpec 0x1072f4 [0x4A, 0x8D, 0x3C, 0x34] (fun s => s.RIP = 0x1072f4) (leaR64Effect 0x1072f4 7 (.sib 4 (some 14) 0 .none))
      [.gpr 4, .gpr 14] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1072f4 7 (.sib 4 (some 14) 0 .none)).toInstrSpec (lea_r64_effect_step 0x1072f4 0x4a (by decide) 7 (.sib 4 (some 14) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1072f8 [0x48, 0x81, 0xC7, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1072f8) (addR64Imm32Effect 0x1072f8 7 0x88)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1072f8 7 0x88).toInstrSpec (add_r64_imm32_effect_step 0x1072f8 0x48 0xc7 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1072ff [0x31, 0xF6] (fun s => s.RIP = 0x1072ff) (xorR32R32Effect 0x1072ff 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1072ff 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x1072ff 0xf6 (by decide)) pre_rip
  have f8 : InstrSpec 0x107301 [0xFF, 0x15, 0x09, 0xCB, 0x0F, 0x00] (GoesTo (CallMemPre 0x107301 (.rip 0xfcb09)) (callEffect (callMemPtr 0x107301 (.rip 0xfcb09)) (0x107301 + BitVec.ofNat 64 (callMemLen (.rip 0xfcb09)))) 0x12a700) (callEffect (callMemPtr 0x107301 (.rip 0xfcb09)) (0x107301 + BitVec.ofNat 64 (callMemLen (.rip 0xfcb09))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x107301 (.rip 0xfcb09)).toInstrSpec (call_m64_effect_step 0x107301 (.rip 0xfcb09) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a700
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072e7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072ea) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072ec) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072f0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072f4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072f8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1072ff) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107301) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a700) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l1072e2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1072e2 :=
  Rest.liftedBlock (rest_l1072e2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1072e2 x hx)

theorem rest_l107307 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107307 bytes_l107307) (entryMap (live .l107307))
      4 0x107307 bytes_l107307 b_l107307 := by
  have f0 : InstrSpec 0x107307 [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107307) (leaR64Effect 0x107307 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x107307 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x107307 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10730f [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10730f) (movR64R64Effect 0x10730f 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10730f 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10730f 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x107312 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x107312) (movR64R64Effect 0x107312 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x107312 2 14).toInstrSpec (mov_r64_r64_effect_step 0x107312 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x107315 [0xFF, 0x15, 0xB5, 0xCA, 0x0F, 0x00] (GoesTo (CallMemPre 0x107315 (.rip 0xfcab5)) (callEffect (callMemPtr 0x107315 (.rip 0xfcab5)) (0x107315 + BitVec.ofNat 64 (callMemLen (.rip 0xfcab5)))) 0x12a820) (callEffect (callMemPtr 0x107315 (.rip 0xfcab5)) (0x107315 + BitVec.ofNat 64 (callMemLen (.rip 0xfcab5))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x107315 (.rip 0xfcab5)).toInstrSpec (call_m64_effect_step 0x107315 (.rip 0xfcab5) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10730f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107312) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107315) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l107307 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107307 :=
  Rest.liftedBlock (rest_l107307 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107307 x hx)

theorem rest_l10731b_2 [Bindings] (code : CodeMap) :
    Rest (n := 109) code lifted (codeRange 0x10731b bytes_l10731b) [(0, 107), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      11 0x107436 bytes_l10731b_2 b_l10731b_2 := by
  have f40 : InstrSpec 0x107436 [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x107436 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107436 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107436 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x107436 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x107436 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x10743b [0x48, 0x89, 0x84, 0x24, 0x05, 0x01, 0x00, 0x00] (StorePre 0x10743b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x105)) s (0x10743b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10743b 0 (.sib 4 none 0 (.d32 0x105)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10743b 0 (.sib 4 none 0 (.d32 0x105))).toInstrSpec (mov_m64_r64_effect_step 0x10743b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x105)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x107443 [0x48, 0x89, 0x8C, 0x24, 0x0D, 0x01, 0x00, 0x00] (StorePre 0x107443 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10d)) s (0x107443 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107443 1 (.sib 4 none 0 (.d32 0x10d)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107443 1 (.sib 4 none 0 (.d32 0x10d))).toInstrSpec (mov_m64_r64_effect_step 0x107443 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x10d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f43 : InstrSpec 0x10744b [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x10744b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10744b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10744b 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10744b 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10744b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f44 : InstrSpec 0x107450 [0x48, 0x89, 0x84, 0x24, 0x15, 0x01, 0x00, 0x00] (StorePre 0x107450 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x115)) s (0x107450 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107450 0 (.sib 4 none 0 (.d32 0x115)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107450 0 (.sib 4 none 0 (.d32 0x115))).toInstrSpec (mov_m64_r64_effect_step 0x107450 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x115)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x107458 [0x8B, 0x44, 0x24, 0x27] (LoadPre 0x107458 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x107458 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107458 0 (.sib 4 none 0 (.d8 0x27)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x107458 0 (.sib 4 none 0 (.d8 0x27))).toInstrSpec (mov_r32_m32_low_effect_step 0x107458 0 (.sib 4 none 0 (.d8 0x27)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f46 : InstrSpec 0x10745c [0x89, 0x84, 0x24, 0x1C, 0x01, 0x00, 0x00] (StorePre 0x10745c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11c)) s (0x10745c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10745c 0 (.sib 4 none 0 (.d32 0x11c)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10745c 0 (.sib 4 none 0 (.d32 0x11c))).toInstrSpec (mov_m32_r32_low_effect_step 0x10745c 0 (.sib 4 none 0 (.d32 0x11c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f47 : InstrSpec 0x107463 [0x4C, 0x8D, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107463) (leaR64Effect 0x107463 14 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x107463 14 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x107463 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x10746b [0x48, 0x8D, 0xB4, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10746b) (leaR64Effect 0x10746b 6 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10746b 6 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x10746b 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x107473 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x107473) (movR64R64Effect 0x107473 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107473 7 14).toInstrSpec (mov_r64_r64_effect_step 0x107473 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x107476 [0xE8, 0x05, 0x7A, 0x00, 0x00] (PushPre 0x107476 5) (callEffect (fun _ => 0x10ee80) 0x10747b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107476 0x10ee80 0x10747b).toInstrSpec (call_rel32_effect_step 0x107476 0x7a05 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f40 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 107), (1, 109), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10743b) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.exec (n := 111) (ρ' := [(0, 107), (1, 109), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107443) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 107), (1, 109), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10744b) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f43 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 113), (1, 109), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107450) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 113), (1, 109), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107458) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f45 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 116), (1, 109), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10745c) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.exec (n := 118) (ρ' := [(0, 116), (1, 109), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107463) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f47 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 116), (1, 109), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (14, 119), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10746b) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f48 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 116), (1, 109), (2, 69), (3, 3), (4, 4), (5, 5), (6, 121), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (14, 119), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107473) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f49 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 116), (1, 109), (2, 69), (3, 3), (4, 4), (5, 5), (6, 121), (7, 123), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (14, 119), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107476) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f50 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 116), (1, 109), (2, 69), (3, 3), (4, 125), (5, 5), (6, 121), (7, 123), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (14, 119), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee80) f50 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 127) (by decide) (by decide) rfl rfl

theorem rest_l10731b_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x10731b bytes_l10731b) [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      31 0x1073a1 bytes_l10731b_1 b_l10731b_1 := by
  have f20 : InstrSpec 0x1073a1 [0x44, 0x0F, 0xB7, 0x94, 0x24, 0xC7, 0x00, 0x00, 0x00] (LoadPre 0x1073a1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc7)) s (0x1073a1 + BitVec.ofNat 64 9)) 2) (movzxR32M16Effect 0x1073a1 9 10 (.sib 4 none 0 (.d32 0xc7)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x1073a1 9 10 (.sib 4 none 0 (.d32 0xc7))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1073a1 0x44 (by decide) 2 (.sib 4 none 0 (.d32 0xc7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x1073aa [0x66, 0x44, 0x89, 0x94, 0x24, 0x98, 0x01, 0x00, 0x00] (StorePre 0x1073aa 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x1073aa + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x1073aa 9 10 (.sib 4 none 0 (.d32 0x198)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1073aa 9 10 (.sib 4 none 0 (.d32 0x198))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1073aa 0x44 (by decide) 2 (.sib 4 none 0 (.d32 0x198)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x1073b3 [0x4C, 0x8B, 0x9C, 0x24, 0xBF, 0x00, 0x00, 0x00] (LoadPre 0x1073b3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbf)) s (0x1073b3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1073b3 11 (.sib 4 none 0 (.d32 0xbf)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1073b3 11 (.sib 4 none 0 (.d32 0xbf))).toInstrSpec (mov_r64_m64_effect_step 0x1073b3 0x4c (by decide) 3 (.sib 4 none 0 (.d32 0xbf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x1073bb [0x4C, 0x89, 0x9C, 0x24, 0x90, 0x01, 0x00, 0x00] (StorePre 0x1073bb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x1073bb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1073bb 11 (.sib 4 none 0 (.d32 0x190)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1073bb 11 (.sib 4 none 0 (.d32 0x190))).toInstrSpec (mov_m64_r64_effect_step 0x1073bb 0x4c (by decide) 3 (.sib 4 none 0 (.d32 0x190)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x1073c3 [0x89, 0x84, 0x24, 0x2B, 0x01, 0x00, 0x00] (StorePre 0x1073c3 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x12b)) s (0x1073c3 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1073c3 0 (.sib 4 none 0 (.d32 0x12b)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1073c3 0 (.sib 4 none 0 (.d32 0x12b))).toInstrSpec (mov_m32_r32_low_effect_step 0x1073c3 0 (.sib 4 none 0 (.d32 0x12b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x1073ca [0x88, 0x8C, 0x24, 0x2F, 0x01, 0x00, 0x00] (StorePre 0x1073ca 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x12f)) s (0x1073ca + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1073ca 7 1 (.sib 4 none 0 (.d32 0x12f)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1073ca 7 1 (.sib 4 none 0 (.d32 0x12f))).toInstrSpec (mov_m8_r8_effect_step 0x1073ca 1 (by decide) (.sib 4 none 0 (.d32 0x12f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x1073d1 [0x89, 0x94, 0x24, 0x57, 0x01, 0x00, 0x00] (StorePre 0x1073d1 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x157)) s (0x1073d1 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1073d1 2 (.sib 4 none 0 (.d32 0x157)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1073d1 2 (.sib 4 none 0 (.d32 0x157))).toInstrSpec (mov_m32_r32_low_effect_step 0x1073d1 2 (.sib 4 none 0 (.d32 0x157)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x1073d8 [0x48, 0x89, 0xB4, 0x24, 0x4F, 0x01, 0x00, 0x00] (StorePre 0x1073d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x14f)) s (0x1073d8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1073d8 6 (.sib 4 none 0 (.d32 0x14f)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1073d8 6 (.sib 4 none 0 (.d32 0x14f))).toInstrSpec (mov_m64_r64_effect_step 0x1073d8 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x14f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x1073e0 [0x48, 0x89, 0xBC, 0x24, 0x47, 0x01, 0x00, 0x00] (StorePre 0x1073e0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x147)) s (0x1073e0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1073e0 7 (.sib 4 none 0 (.d32 0x147)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1073e0 7 (.sib 4 none 0 (.d32 0x147))).toInstrSpec (mov_m64_r64_effect_step 0x1073e0 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x147)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x1073e8 [0x4C, 0x89, 0x84, 0x24, 0x3F, 0x01, 0x00, 0x00] (StorePre 0x1073e8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x13f)) s (0x1073e8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1073e8 8 (.sib 4 none 0 (.d32 0x13f)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1073e8 8 (.sib 4 none 0 (.d32 0x13f))).toInstrSpec (mov_m64_r64_effect_step 0x1073e8 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x13f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x1073f0 [0x4C, 0x89, 0x8C, 0x24, 0x37, 0x01, 0x00, 0x00] (StorePre 0x1073f0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x137)) s (0x1073f0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1073f0 9 (.sib 4 none 0 (.d32 0x137)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1073f0 9 (.sib 4 none 0 (.d32 0x137))).toInstrSpec (mov_m64_r64_effect_step 0x1073f0 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x137)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x1073f8 [0x66, 0x44, 0x89, 0x94, 0x24, 0x63, 0x01, 0x00, 0x00] (StorePre 0x1073f8 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x163)) s (0x1073f8 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x1073f8 9 10 (.sib 4 none 0 (.d32 0x163)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1073f8 9 10 (.sib 4 none 0 (.d32 0x163))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1073f8 0x44 (by decide) 2 (.sib 4 none 0 (.d32 0x163)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x107401 [0x4C, 0x89, 0x9C, 0x24, 0x5B, 0x01, 0x00, 0x00] (StorePre 0x107401 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15b)) s (0x107401 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107401 11 (.sib 4 none 0 (.d32 0x15b)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107401 11 (.sib 4 none 0 (.d32 0x15b))).toInstrSpec (mov_m64_r64_effect_step 0x107401 0x4c (by decide) 3 (.sib 4 none 0 (.d32 0x15b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x107409 [0x40, 0x88, 0xAC, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x107409 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x107409 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x107409 8 5 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107409 8 5 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107409 0x40 (by decide) 5 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x107411 [0x0F, 0xB7, 0x04, 0x24] (LoadPre 0x107411 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x107411 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x107411 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x107411 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x107411 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x107415 [0x66, 0x89, 0x84, 0x24, 0x01, 0x01, 0x00, 0x00] (StorePre 0x107415 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x101)) s (0x107415 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x107415 8 0 (.sib 4 none 0 (.d32 0x101)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x107415 8 0 (.sib 4 none 0 (.d32 0x101))).toInstrSpec (mov_m16_r16_effect_step 0x107415 0 (.sib 4 none 0 (.d32 0x101)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x10741d [0x0F, 0xB6, 0x44, 0x24, 0x02] (LoadPre 0x10741d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x10741d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10741d 5 0 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10741d 5 0 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (movzx_r32_m8_effect_step 0x10741d 0 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x107422 [0x88, 0x84, 0x24, 0x03, 0x01, 0x00, 0x00] (StorePre 0x107422 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x103)) s (0x107422 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x107422 7 0 (.sib 4 none 0 (.d32 0x103)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107422 7 0 (.sib 4 none 0 (.d32 0x103))).toInstrSpec (mov_m8_r8_effect_step 0x107422 0 (by decide) (.sib 4 none 0 (.d32 0x103)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x107429 [0x44, 0x88, 0xA4, 0x24, 0x04, 0x01, 0x00, 0x00] (StorePre 0x107429 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x104)) s (0x107429 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x107429 8 12 (.sib 4 none 0 (.d32 0x104)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107429 8 12 (.sib 4 none 0 (.d32 0x104))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107429 0x44 (by decide) 4 (.sib 4 none 0 (.d32 0x104)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x107431 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x107431 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107431 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107431 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107431 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x107431 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f20 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073aa) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073b3) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f22 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073bb) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073c3) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073ca) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073d1) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073d8) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073e0) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073e8) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073f0) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073f8) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107401) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107409) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107411) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f34 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 100), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107415) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.exec (n := 102) (ρ' := [(0, 100), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10741d) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f36 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 103), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107422) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.exec (n := 105) (ρ' := [(0, 103), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107429) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 103), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107431) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f39 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 107), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107436) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10731b_2 code

theorem rest_l10731b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10731b bytes_l10731b) (entryMap (live .l10731b))
      51 0x10731b bytes_l10731b b_l10731b := by
  have f0 : InstrSpec 0x10731b [0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x10731b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10731b + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x10731b 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x10731b 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r32_m32_low_effect_step 0x10731b 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107322 [0x8B, 0x8C, 0x24, 0x8B, 0x00, 0x00, 0x00] (LoadPre 0x107322 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8b)) s (0x107322 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x107322 1 (.sib 4 none 0 (.d32 0x8b)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x107322 1 (.sib 4 none 0 (.d32 0x8b))).toInstrSpec (mov_r32_m32_low_effect_step 0x107322 1 (.sib 4 none 0 (.d32 0x8b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x107329 [0x89, 0x84, 0x24, 0x24, 0x01, 0x00, 0x00] (StorePre 0x107329 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x124)) s (0x107329 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107329 0 (.sib 4 none 0 (.d32 0x124)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107329 0 (.sib 4 none 0 (.d32 0x124))).toInstrSpec (mov_m32_r32_low_effect_step 0x107329 0 (.sib 4 none 0 (.d32 0x124)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x107330 [0x89, 0x8C, 0x24, 0x27, 0x01, 0x00, 0x00] (StorePre 0x107330 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x127)) s (0x107330 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107330 1 (.sib 4 none 0 (.d32 0x127)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107330 1 (.sib 4 none 0 (.d32 0x127))).toInstrSpec (mov_m32_r32_low_effect_step 0x107330 1 (.sib 4 none 0 (.d32 0x127)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x107337 [0x8B, 0x84, 0x24, 0x8F, 0x00, 0x00, 0x00] (LoadPre 0x107337 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f)) s (0x107337 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x107337 0 (.sib 4 none 0 (.d32 0x8f)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x107337 0 (.sib 4 none 0 (.d32 0x8f))).toInstrSpec (mov_r32_m32_low_effect_step 0x107337 0 (.sib 4 none 0 (.d32 0x8f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10733e [0x0F, 0xB6, 0x8C, 0x24, 0x93, 0x00, 0x00, 0x00] (LoadPre 0x10733e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x93)) s (0x10733e + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10733e 8 1 (.sib 4 none 0 (.d32 0x93)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10733e 8 1 (.sib 4 none 0 (.d32 0x93))).toInstrSpec (movzx_r32_m8_effect_step 0x10733e 1 (.sib 4 none 0 (.d32 0x93)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x107346 [0x8B, 0x94, 0x24, 0x94, 0x00, 0x00, 0x00] (LoadPre 0x107346 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x107346 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x107346 2 (.sib 4 none 0 (.d32 0x94)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x107346 2 (.sib 4 none 0 (.d32 0x94))).toInstrSpec (mov_r32_m32_low_effect_step 0x107346 2 (.sib 4 none 0 (.d32 0x94)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10734d [0x89, 0x94, 0x24, 0x30, 0x01, 0x00, 0x00] (StorePre 0x10734d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10734d + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10734d 2 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10734d 2 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_m32_r32_low_effect_step 0x10734d 2 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x107354 [0x8B, 0x94, 0x24, 0x97, 0x00, 0x00, 0x00] (LoadPre 0x107354 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x97)) s (0x107354 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x107354 2 (.sib 4 none 0 (.d32 0x97)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x107354 2 (.sib 4 none 0 (.d32 0x97))).toInstrSpec (mov_r32_m32_low_effect_step 0x107354 2 (.sib 4 none 0 (.d32 0x97)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10735b [0x89, 0x94, 0x24, 0x33, 0x01, 0x00, 0x00] (StorePre 0x10735b 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x133)) s (0x10735b + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10735b 2 (.sib 4 none 0 (.d32 0x133)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10735b 2 (.sib 4 none 0 (.d32 0x133))).toInstrSpec (mov_m32_r32_low_effect_step 0x10735b 2 (.sib 4 none 0 (.d32 0x133)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x107362 [0x8B, 0x94, 0x24, 0xBB, 0x00, 0x00, 0x00] (LoadPre 0x107362 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbb)) s (0x107362 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x107362 2 (.sib 4 none 0 (.d32 0xbb)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x107362 2 (.sib 4 none 0 (.d32 0xbb))).toInstrSpec (mov_r32_m32_low_effect_step 0x107362 2 (.sib 4 none 0 (.d32 0xbb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x107369 [0x89, 0x54, 0x24, 0x50] (StorePre 0x107369 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x107369 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x107369 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107369 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m32_r32_low_effect_step 0x107369 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10736d [0x48, 0x8B, 0xB4, 0x24, 0xB3, 0x00, 0x00, 0x00] (LoadPre 0x10736d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb3)) s (0x10736d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10736d 6 (.sib 4 none 0 (.d32 0xb3)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10736d 6 (.sib 4 none 0 (.d32 0xb3))).toInstrSpec (mov_r64_m64_effect_step 0x10736d 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xb3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x107375 [0x48, 0x89, 0x74, 0x24, 0x48] (StorePre 0x107375 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x107375 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107375 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107375 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x107375 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x10737a [0x48, 0x8B, 0xBC, 0x24, 0xAB, 0x00, 0x00, 0x00] (LoadPre 0x10737a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xab)) s (0x10737a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10737a 7 (.sib 4 none 0 (.d32 0xab)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10737a 7 (.sib 4 none 0 (.d32 0xab))).toInstrSpec (mov_r64_m64_effect_step 0x10737a 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xab)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x107382 [0x48, 0x89, 0x7C, 0x24, 0x40] (StorePre 0x107382 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107382 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107382 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107382 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x107382 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x107387 [0x4C, 0x8B, 0x84, 0x24, 0xA3, 0x00, 0x00, 0x00] (LoadPre 0x107387 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa3)) s (0x107387 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107387 8 (.sib 4 none 0 (.d32 0xa3)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x107387 8 (.sib 4 none 0 (.d32 0xa3))).toInstrSpec (mov_r64_m64_effect_step 0x107387 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0xa3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10738f [0x4C, 0x89, 0x44, 0x24, 0x38] (StorePre 0x10738f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10738f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10738f 8 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10738f 8 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10738f 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x107394 [0x4C, 0x8B, 0x8C, 0x24, 0x9B, 0x00, 0x00, 0x00] (LoadPre 0x107394 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9b)) s (0x107394 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107394 9 (.sib 4 none 0 (.d32 0x9b)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x107394 9 (.sib 4 none 0 (.d32 0x9b))).toInstrSpec (mov_r64_m64_effect_step 0x107394 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x9b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x10739c [0x4C, 0x89, 0x4C, 0x24, 0x30] (StorePre 0x10739c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10739c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10739c 9 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10739c 9 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10739c 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107322) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107329) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107330) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107337) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10733e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107346) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (2, 63), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10734d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 61), (2, 63), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107354) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 61), (2, 66), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10735b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (2, 66), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107362) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107369) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10736d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107375) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10737a) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107382) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107387) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10738f) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107394) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10739c) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 72), (7, 75), (8, 78), (9, 81), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1073a1) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10731b_1 code

theorem block_l10731b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10731b :=
  Rest.liftedBlock (rest_l10731b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10731b x hx)

theorem rest_l10747b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10747b bytes_l10747b) (entryMap (live .l10747b))
      3 0x10747b bytes_l10747b b_l10747b := by
  have f0 : InstrSpec 0x10747b [0x48, 0x8D, 0x7C, 0x24, 0x30] (fun s => s.RIP = 0x10747b) (leaR64Effect 0x10747b 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10747b 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x10747b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x107480 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x107480) (movR64R64Effect 0x107480 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x107480 6 14).toInstrSpec (mov_r64_r64_effect_step 0x107480 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x107483 [0xE8, 0xC8, 0x89, 0x00, 0x00] (PushPre 0x107483 5) (callEffect (fun _ => 0x10fe50) 0x107488)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107483 0x10fe50 0x107488).toInstrSpec (call_rel32_effect_step 0x107483 0x89c8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107480) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107483) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe50) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l10747b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10747b :=
  Rest.liftedBlock (rest_l10747b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10747b x hx)

theorem rest_l107488 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107488 bytes_l107488) (entryMap (live .l107488))
      4 0x107488 bytes_l107488 b_l107488 := by
  have f0 : InstrSpec 0x107488 [0x44, 0x0F, 0xB6, 0xB4, 0x24, 0x24, 0x01, 0x00, 0x00] (LoadPre 0x107488 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x124)) s (0x107488 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107488 9 14 (.sib 4 none 0 (.d32 0x124)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x107488 9 14 (.sib 4 none 0 (.d32 0x124))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107488 0x44 (by decide) 6 (.sib 4 none 0 (.d32 0x124)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107491 [0x41, 0x8D, 0x46, 0xFE] (fun s => s.RIP = 0x107491) (leaR32Effect 0x107491 4 0 (.base 14 (.d8 0xfe)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (leaR32Effect_footprint 0x107491 4 0 (.base 14 (.d8 0xfe))).toInstrSpec (lea_r32_rex_effect_step 0x107491 0x41 (by decide) 0 (.base 14 (.d8 0xfe)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x107495 [0x83, 0xF8, 0x04] (fun s => s.RIP = 0x107495) (cmpR32Imm8Effect 0x107495 3 0 0x4)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x107495 3 0 0x4).toInstrSpec (cmp_r32_imm8_effect_step 0x107495 0xf8 0x4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107491) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107495) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107498) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x107498 2 0x5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l107488 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107488 :=
  Rest.liftedBlock (rest_l107488 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107488 x hx)

theorem rest_l10749a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10749a bytes_l10749a) (entryMap (live .l10749a))
      2 0x10749a bytes_l10749a b_l10749a := by
  have f0 : InstrSpec 0x10749a [0x45, 0x85, 0xF6] (fun s => s.RIP = 0x10749a) (testR32R32Effect 0x10749a 3 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR32R32Effect_footprint 0x10749a 3 14 14).toInstrSpec (test_r32_r32_rex_effect_step 0x10749a 0x45 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10749d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x10749d 5 0x4a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10749a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10749a :=
  Rest.liftedBlock (rest_l10749a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10749a x hx)

theorem rest_l10749f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10749f bytes_l10749f) (entryMap (live .l10749f))
      8 0x10749f bytes_l10749f b_l10749f := by
  have f0 : InstrSpec 0x10749f [0x44, 0x89, 0xF0] (fun s => s.RIP = 0x10749f) (movR32R32Effect 0x10749f 3 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x10749f 3 0 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x10749f 0x44 0xf0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1074a2 [0x24, 0xFE] (fun s => s.RIP = 0x1074a2) (andAlImm8Effect 0x1074a2 0xfe)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x1074a2 0xfe).toInstrSpec (and_al_imm8_effect_step 0x1074a2 0xfe) pre_rip
  have f2 : InstrSpec 0x1074a4 [0x31, 0xD2] (fun s => s.RIP = 0x1074a4) (xorR32R32Effect 0x1074a4 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1074a4 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x1074a4 0xd2 (by decide)) pre_rip
  have f3 : InstrSpec 0x1074a6 [0x3C, 0x02] (fun s => s.RIP = 0x1074a6) (cmpAlImm8Effect 0x1074a6 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x1074a6 0x2).toInstrSpec (cmp_al_imm8_effect_step 0x1074a6 0x2) pre_rip
  have f4 : InstrSpec 0x1074a8 [0x0F, 0x94, 0xC2] (fun s => s.RIP = 0x1074a8) (atFlags (condHolds 4) (setccR8Effect 0x1074a8 3 2))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (setccR8Effect_footprint 0x1074a8 3 2 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1074a8 4 0xc2 (by decide) (by decide) c)) pre_rip
  have f5 : InstrSpec 0x1074ab [0x48, 0x8D, 0xBC, 0x24, 0x90, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1074ab) (leaR64Effect 0x1074ab 7 (.sib 4 none 0 (.d32 0x190)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1074ab 7 (.sib 4 none 0 (.d32 0x190))).toInstrSpec (lea_r64_effect_step 0x1074ab 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x190)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1074b3 [0x48, 0x8D, 0x74, 0x24, 0x30] (fun s => s.RIP = 0x1074b3) (leaR64Effect 0x1074b3 6 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1074b3 6 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x1074b3 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1074b8 [0xE8, 0x23, 0xA1, 0x01, 0x00] (PushPre 0x1074b8 5) (callEffect (fun _ => 0x1215e0) 0x1074bd)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1074b8 0x1215e0 0x1074bd).toInstrSpec (call_rel32_effect_step 0x1074b8 0x1a123 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074a2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074a4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (2, 57), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074a6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (2, 57), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074a8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074ab) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (7, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074b3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074b8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 67), (5, 5), (6, 65), (7, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215e0) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l10749f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10749f :=
  Rest.liftedBlock (rest_l10749f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10749f x hx)

theorem rest_l1074bd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1074bd bytes_l1074bd) (entryMap (live .l1074bd))
      8 0x1074bd bytes_l1074bd b_l1074bd := by
  have f0 : InstrSpec 0x1074bd [0x41, 0x80, 0xFE, 0x06] (fun s => s.RIP = 0x1074bd) (cmpR8Imm8Effect 0x1074bd 4 14 0x6)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1074bd 4 14 0x6).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x1074bd 0x41 0xfe 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1074c1 [0x0F, 0x92, 0xC2] (fun s => s.RIP = 0x1074c1) (atFlags (condHolds 2) (setccR8Effect 0x1074c1 3 2))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .rip] :=
    (setccR8Effect_footprint 0x1074c1 3 2 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1074c1 2 0xc2 (by decide) (by decide) c)) pre_rip
  have f2 : InstrSpec 0x1074c4 [0xB0, 0x3D] (fun s => s.RIP = 0x1074c4) (movR8Imm8Effect 0x1074c4 2 0 0x3d)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x1074c4 2 0 0x3d).toInstrSpec (mov_r8_imm8_effect_step 0x1074c4 0xb0 (by decide) 0x3d) pre_rip
  have f3 : InstrSpec 0x1074c6 [0x40, 0xB6, 0x3D] (fun s => s.RIP = 0x1074c6) (movR8Imm8Effect 0x1074c6 3 6 0x3d)
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR8Imm8Effect_footprint 0x1074c6 3 6 0x3d).toInstrSpec (mov_r8_imm8_rex_effect_step 0x1074c6 0x40 (by decide) 0xb6 (by decide) 0x3d) pre_rip
  have f4 : InstrSpec 0x1074c9 [0x44, 0x89, 0xF1] (fun s => s.RIP = 0x1074c9) (movR32R32Effect 0x1074c9 3 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1074c9 3 1 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x1074c9 0x44 0xf1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1074cc [0x40, 0xD2, 0xEE] (fun s => s.RIP = 0x1074cc) (shrR8ClEffect 0x1074cc 3 6)
      [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR8ClEffect_footprint 0x1074cc 3 6).toInstrSpec (shr_r8_cl_rex_effect_step 0x1074cc 0x40 0xee (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1074cf [0x40, 0x84, 0xF2] (fun s => s.RIP = 0x1074cf) (testR8R8Effect 0x1074cf 3 2 6)
      [.gpr 2, .gpr 6] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1074cf 3 2 6).toInstrSpec (test_r8_r8_rex_effect_step 0x1074cf 0x40 0xf2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074c4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074c6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074c9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074cc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074cf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074d2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 67) (jcc_rel8_effect_step 0x1074d2 4 0x15) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1074bd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1074bd :=
  Rest.liftedBlock (rest_l1074bd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1074bd x hx)

theorem rest_l1074d4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1074d4 bytes_l1074d4) (entryMap (live .l1074d4))
      6 0x1074d4 bytes_l1074d4 b_l1074d4 := by
  have f0 : InstrSpec 0x1074d4 [0x0F, 0xB6, 0x8C, 0x24, 0x90, 0x01, 0x00, 0x00] (LoadPre 0x1074d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x1074d4 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1074d4 8 1 (.sib 4 none 0 (.d32 0x190)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1074d4 8 1 (.sib 4 none 0 (.d32 0x190))).toInstrSpec (movzx_r32_m8_effect_step 0x1074d4 1 (.sib 4 none 0 (.d32 0x190)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1074dc [0x48, 0x83, 0xF9, 0x06] (fun s => s.RIP = 0x1074dc) (cmpR64Imm8Effect 0x1074dc 1 0x6)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1074dc 1 0x6).toInstrSpec (cmp_r64_imm8_effect_step 0x1074dc 0x48 0xf9 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1074e0 [0x0F, 0x92, 0xC2] (fun s => s.RIP = 0x1074e0) (atFlags (condHolds 2) (setccR8Effect 0x1074e0 3 2))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .rip] :=
    (setccR8Effect_footprint 0x1074e0 3 2 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1074e0 2 0xc2 (by decide) (by decide) c)) pre_rip
  have f3 : InstrSpec 0x1074e3 [0xD2, 0xE8] (fun s => s.RIP = 0x1074e3) (shrR8ClEffect 0x1074e3 2 0)
      [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR8ClEffect_footprint 0x1074e3 2 0).toInstrSpec (shr_r8_cl_effect_step 0x1074e3 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1074e5 [0x84, 0xC2] (fun s => s.RIP = 0x1074e5) (testR8R8Effect 0x1074e5 2 2 0)
      [.gpr 2, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1074e5 2 2 0).toInstrSpec (test_r8_r8_effect_step 0x1074e5 0xc2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074dc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074e0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074e3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074e5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1074e7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x1074e7 5 0x53) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1074d4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1074d4 :=
  Rest.liftedBlock (rest_l1074d4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1074d4 x hx)

theorem rest_l1074e9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1074e9 bytes_l1074e9) (entryMap (live .l1074e9))
      7 0x1074e9 bytes_l1074e9 b_l1074e9 := by
  have f0 : InstrSpec 0x1074e9 [0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00] (StorePre 0x1074e9 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1074e9 + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x1074e9 11 (.sib 4 none 0 (.d32 0x88)) 0x3)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1074e9 11 (.sib 4 none 0 (.d32 0x88)) 0x3).toInstrSpec (mov_m32_imm32_effect_step 0x1074e9 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x3) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1074f4 [0x48, 0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1074f4) (leaR64Effect 0x1074f4 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1074f4 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x1074f4 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1074fc [0xBE, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1074fc) (movR32Imm32Effect 0x1074fc 5 6 0xb)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1074fc 5 6 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x1074fc 0xbe (by decide) 0xb) pre_rip
  have f3 : InstrSpec 0x107501 [0x48, 0xC7, 0xC7, 0x00, 0x28, 0x20, 0x00] (fun s => s.RIP = 0x107501) (movR64Imm32Effect 0x107501 7 0x202800)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x107501 7 0x202800).toInstrSpec (mov_r64_imm32_effect_step 0x107501 0x48 0xc7 (by decide) (by decide) (by decide) 0x202800) pre_rip
  have f4 : InstrSpec 0x107508 [0x48, 0xC7, 0xC1, 0xE0, 0x27, 0x20, 0x00] (fun s => s.RIP = 0x107508) (movR64Imm32Effect 0x107508 1 0x2027e0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x107508 1 0x2027e0).toInstrSpec (mov_r64_imm32_effect_step 0x107508 0x48 0xc1 (by decide) (by decide) (by decide) 0x2027e0) pre_rip
  have f5 : InstrSpec 0x10750f [0x49, 0xC7, 0xC0, 0x10, 0x28, 0x20, 0x00] (fun s => s.RIP = 0x10750f) (movR64Imm32Effect 0x10750f 8 0x202810)
      [] [] [.reg 8, .rip] :=
    (movR64Imm32Effect_footprint 0x10750f 8 0x202810).toInstrSpec (mov_r64_imm32_effect_step 0x10750f 0x49 0xc0 (by decide) (by decide) (by decide) 0x202810) pre_rip
  have f6 : InstrSpec 0x107516 [0xE8, 0x85, 0x20, 0x02, 0x00] (PushPre 0x107516 5) (callEffect (fun _ => 0x1295a0) 0x10751b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107516 0x1295a0 0x10751b).toInstrSpec (call_rel32_effect_step 0x107516 0x22085 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x1074f4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 54), (4, 4), (5, 5)]) (p' := 0x1074fc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56)]) (p' := 0x107501) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x107508) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x10750f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x107516) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 60), (2, 54), (4, 64), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x1295a0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l1074e9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1074e9 :=
  Rest.liftedBlock (rest_l1074e9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1074e9 x hx)

theorem rest_l10751b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10751b bytes_l10751b) (entryMap (live .l10751b))
      3 0x10751b bytes_l10751b b_l10751b := by
  have f0 : InstrSpec 0x10751b [0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (StorePre 0x10751b 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10751b + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10751b (.sib 4 none 0 (.d32 0x88)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10751b (.sib 4 none 0 (.d32 0x88)) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x10751b 0x48 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x107527 [0x80, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00] (LoadPre 0x107527 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107527 + BitVec.ofNat 64 8)) 1) (cmpM8Imm8Effect 0x107527 8 (.sib 4 none 0 (.d32 0x88)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x107527 8 (.sib 4 none 0 (.d32 0x88)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x107527 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107527) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10752f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x10752f 4 0xfffffd18) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10751b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10751b :=
  Rest.liftedBlock (rest_l10751b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10751b x hx)

theorem rest_l107535 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107535 bytes_l107535) (entryMap (live .l107535))
      2 0x107535 bytes_l107535 b_l107535 := by
  have f0 : InstrSpec 0x107535 [0xB0, 0x03] (fun s => s.RIP = 0x107535) (movR8Imm8Effect 0x107535 2 0 0x3)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x107535 2 0 0x3).toInstrSpec (mov_r8_imm8_effect_step 0x107535 0xb0 (by decide) 0x3) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107537) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x107537 0xe7 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l107535 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107535 :=
  Rest.liftedBlock (rest_l107535 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107535 x hx)

theorem rest_l10753c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10753c bytes_l10753c) (entryMap (live .l10753c))
      3 0x10753c bytes_l10753c b_l10753c := by
  have f0 : InstrSpec 0x10753c [0x4A, 0x8B, 0x14, 0xF5, 0xD8, 0x2A, 0x20, 0x00] (LoadPre 0x10753c (fun s => AddrMode.addr (.abs (some 14) 3 0x202ad8) s (0x10753c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10753c 2 (.abs (some 14) 3 0x202ad8))
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10753c 2 (.abs (some 14) 3 0x202ad8)).toInstrSpec (mov_r64_m64_effect_step 0x10753c 0x4a (by decide) 2 (.abs (some 14) 3 0x202ad8) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107544 [0x48, 0x3B, 0x14, 0xCD, 0xD8, 0x2A, 0x20, 0x00] (LoadPre 0x107544 (fun s => AddrMode.addr (.abs (some 1) 3 0x202ad8) s (0x107544 + BitVec.ofNat 64 8)) 8) (cmpR64M64Effect 0x107544 2 (.abs (some 1) 3 0x202ad8))
      [.gpr 2, .gpr 1] [] [.flags, .rip] :=
    (cmpR64M64Effect_footprint 0x107544 2 (.abs (some 1) 3 0x202ad8)).toInstrSpec (cmp_r64_m64_effect_step 0x107544 0x48 (by decide) 2 (.abs (some 1) 3 0x202ad8) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107544) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10754c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x10754c 5 0x1e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10753c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10753c :=
  Rest.liftedBlock (rest_l10753c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10753c x hx)

theorem rest_l10754e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10754e bytes_l10754e) (entryMap (live .l10754e))
      3 0x10754e bytes_l10754e b_l10754e := by
  have f0 : InstrSpec 0x10754e [0x48, 0x8D, 0xBC, 0x24, 0x24, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10754e) (leaR64Effect 0x10754e 7 (.sib 4 none 0 (.d32 0x124)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10754e 7 (.sib 4 none 0 (.d32 0x124))).toInstrSpec (lea_r64_effect_step 0x10754e 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x124)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x107556 [0x48, 0x8D, 0xB4, 0x24, 0x90, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x107556) (leaR64Effect 0x107556 6 (.sib 4 none 0 (.d32 0x190)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x107556 6 (.sib 4 none 0 (.d32 0x190))).toInstrSpec (lea_r64_effect_step 0x107556 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x190)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10755e [0xFF, 0x15, 0x9C, 0xC8, 0x0F, 0x00] (GoesTo (CallMemPre 0x10755e (.rip 0xfc89c)) (callEffect (callMemPtr 0x10755e (.rip 0xfc89c)) (0x10755e + BitVec.ofNat 64 (callMemLen (.rip 0xfc89c)))) 0x12a750) (callEffect (callMemPtr 0x10755e (.rip 0xfc89c)) (0x10755e + BitVec.ofNat 64 (callMemLen (.rip 0xfc89c))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x10755e (.rip 0xfc89c)).toInstrSpec (call_m64_effect_step 0x10755e (.rip 0xfc89c) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a750
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107556) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10755e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a750) f2 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l10754e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10754e :=
  Rest.liftedBlock (rest_l10754e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10754e x hx)

theorem rest_l107564 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107564 bytes_l107564) (entryMap (live .l107564))
      2 0x107564 bytes_l107564 b_l107564 := by
  have f0 : InstrSpec 0x107564 [0x85, 0xC0] (fun s => s.RIP = 0x107564) (testR32R32Effect 0x107564 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR32R32Effect_footprint 0x107564 2 0 0).toInstrSpec (test_r32_r32_effect_step 0x107564 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107566) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x107566 4 0x134) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l107564 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107564 :=
  Rest.liftedBlock (rest_l107564 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107564 x hx)

theorem rest_l10756c_1 [Bindings] (code : CodeMap) :
    Rest (n := 79) code lifted (codeRange 0x10756c bytes_l10756c) [(0, 76), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]
      7 0x1075fa bytes_l10756c_1 b_l10756c_1 := by
  have f20 : InstrSpec 0x1075fa [0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x1075fa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1075fa + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1075fa 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1075fa 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x1075fa 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x107602 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x107602 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107602 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107602 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107602 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x107602 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x107607 [0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x107607 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107607 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107607 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107607 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x107607 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x10760f [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x10760f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10760f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10760f 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10760f 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10760f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x107614 [0x48, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x107614 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107614 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107614 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107614 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x107614 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x10761c [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x10761c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10761c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10761c 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10761c 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10761c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x107621 [0xB0, 0x02] (fun s => s.RIP = 0x107621) (movR8Imm8Effect 0x107621 2 0 0x2)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x107621 2 0 0x2).toInstrSpec (mov_r8_imm8_effect_step 0x107621 0xb0 (by decide) 0x2) pre_rip
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107602) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107607) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10760f) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 82), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107614) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10761c) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 85), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107621) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f26 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 88), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107623) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 90) (by decide) rfl

theorem rest_l10756c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10756c bytes_l10756c) (entryMap (live .l10756c))
      27 0x10756c bytes_l10756c b_l10756c := by
  have f0 : InstrSpec 0x10756c [0xC6, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00, 0x00] (StorePre 0x10756c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x10756c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x10756c (.sib 4 none 0 (.d32 0x190)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x10756c (.sib 4 none 0 (.d32 0x190)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x10756c (.sib 4 none 0 (.d32 0x190)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x107574 [0xC6, 0x44, 0x24, 0x32, 0x00] (StorePre 0x107574 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x107574 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107574 (.sib 4 none 0 (.d8 0x32)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x107574 (.sib 4 none 0 (.d8 0x32)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x107574 (.sib 4 none 0 (.d8 0x32)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x107579 [0x66, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00] (StorePre 0x107579 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107579 + BitVec.ofNat 64 7)) 2) (movM16Imm16Effect 0x107579 (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM16Imm16Effect_footprint 0x107579 (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m16_imm16_effect_step 0x107579 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x107580 [0xC6, 0x84, 0x24, 0x24, 0x01, 0x00, 0x00, 0x00] (StorePre 0x107580 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x124)) s (0x107580 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x107580 (.sib 4 none 0 (.d32 0x124)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x107580 (.sib 4 none 0 (.d32 0x124)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x107580 (.sib 4 none 0 (.d32 0x124)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x107588 [0xC7, 0x84, 0x24, 0x9F, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107588 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x107588 + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x107588 11 (.sib 4 none 0 (.d32 0x9f)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x107588 11 (.sib 4 none 0 (.d32 0x9f)) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x107588 (.sib 4 none 0 (.d32 0x9f)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x107593 [0x48, 0xC7, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107593 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x107593 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x107593 (.sib 4 none 0 (.d32 0x98)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107593 (.sib 4 none 0 (.d32 0x98)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107593 0x48 (by decide) (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10759f [0x48, 0xC7, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10759f 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10759f + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10759f (.sib 4 none 0 (.d32 0x90)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10759f (.sib 4 none 0 (.d32 0x90)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10759f 0x48 (by decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1075ab [0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1075ab 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1075ab + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1075ab (.sib 4 none 0 (.d32 0x88)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1075ab (.sib 4 none 0 (.d32 0x88)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1075ab 0x48 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1075b7 [0x0F, 0xB6, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00] (LoadPre 0x1075b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x1075b7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075b7 8 0 (.sib 4 none 0 (.d32 0x190)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1075b7 8 0 (.sib 4 none 0 (.d32 0x190))).toInstrSpec (movzx_r32_m8_effect_step 0x1075b7 0 (.sib 4 none 0 (.d32 0x190)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1075bf [0x88, 0x44, 0x24, 0x08] (StorePre 0x1075bf 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1075bf + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075bf 4 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1075bf 4 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_effect_step 0x1075bf 0 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1075c3 [0x0F, 0xB6, 0x44, 0x24, 0x32] (LoadPre 0x1075c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x1075c3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1075c3 5 0 (.sib 4 none 0 (.d8 0x32)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1075c3 5 0 (.sib 4 none 0 (.d8 0x32))).toInstrSpec (movzx_r32_m8_effect_step 0x1075c3 0 (.sib 4 none 0 (.d8 0x32)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1075c8 [0x88, 0x44, 0x24, 0x02] (StorePre 0x1075c8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1075c8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075c8 4 0 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1075c8 4 0 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (mov_m8_r8_effect_step 0x1075c8 0 (by decide) (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1075cc [0x0F, 0xB7, 0x44, 0x24, 0x30] (LoadPre 0x1075cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1075cc + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1075cc 5 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1075cc 5 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (movzx_r32_m16_effect_step 0x1075cc 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1075d1 [0x66, 0x89, 0x04, 0x24] (StorePre 0x1075d1 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1075d1 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x1075d1 4 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1075d1 4 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m16_r16_effect_step 0x1075d1 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1075d5 [0x0F, 0xB6, 0x84, 0x24, 0x24, 0x01, 0x00, 0x00] (LoadPre 0x1075d5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x124)) s (0x1075d5 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075d5 8 0 (.sib 4 none 0 (.d32 0x124)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1075d5 8 0 (.sib 4 none 0 (.d32 0x124))).toInstrSpec (movzx_r32_m8_effect_step 0x1075d5 0 (.sib 4 none 0 (.d32 0x124)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1075dd [0x88, 0x44, 0x24, 0x0C] (StorePre 0x1075dd 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1075dd + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075dd 4 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1075dd 4 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m8_r8_effect_step 0x1075dd 0 (by decide) (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1075e1 [0x0F, 0xB6, 0x84, 0x24, 0xA2, 0x00, 0x00, 0x00] (LoadPre 0x1075e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa2)) s (0x1075e1 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075e1 8 0 (.sib 4 none 0 (.d32 0xa2)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1075e1 8 0 (.sib 4 none 0 (.d32 0xa2))).toInstrSpec (movzx_r32_m8_effect_step 0x1075e1 0 (.sib 4 none 0 (.d32 0xa2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x1075e9 [0x88, 0x44, 0x24, 0x2A] (StorePre 0x1075e9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x1075e9 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075e9 4 0 (.sib 4 none 0 (.d8 0x2a)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1075e9 4 0 (.sib 4 none 0 (.d8 0x2a))).toInstrSpec (mov_m8_r8_effect_step 0x1075e9 0 (by decide) (.sib 4 none 0 (.d8 0x2a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1075ed [0x0F, 0xB7, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x1075ed (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1075ed + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1075ed 8 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1075ed 8 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (movzx_r32_m16_effect_step 0x1075ed 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x1075f5 [0x66, 0x89, 0x44, 0x24, 0x28] (StorePre 0x1075f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1075f5 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1075f5 5 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1075f5 5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m16_r16_effect_step 0x1075f5 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107574) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107579) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107580) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107588) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107593) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10759f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075ab) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075b7) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075bf) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075c3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075c8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075cc) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075d1) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075d5) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075dd) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 70), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075e1) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075e9) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 73), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075ed) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075f5) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 76), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1075fa) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10756c_1 code

theorem block_l10756c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10756c :=
  Rest.liftedBlock (rest_l10756c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10756c x hx)

theorem rest_l107623 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107623 bytes_l107623) (entryMap (live .l107623))
      20 0x107623 bytes_l107623 b_l107623 := by
  have f0 : InstrSpec 0x107623 [0x0F, 0xB6, 0x4C, 0x24, 0x06] (LoadPre 0x107623 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x107623 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x107623 5 1 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x107623 5 1 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (movzx_r32_m8_effect_step 0x107623 1 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107628 [0x88, 0x4B, 0x13] (StorePre 0x107628 3 (fun s => AddrMode.addr (.base 3 (.d8 0x13)) s (0x107628 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x107628 3 1 (.base 3 (.d8 0x13)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x107628 3 1 (.base 3 (.d8 0x13))).toInstrSpec (mov_m8_r8_effect_step 0x107628 1 (by decide) (.base 3 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10762b [0x0F, 0xB7, 0x4C, 0x24, 0x04] (LoadPre 0x10762b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x10762b + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10762b 5 1 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x10762b 5 1 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (movzx_r32_m16_effect_step 0x10762b 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x107630 [0x66, 0x89, 0x4B, 0x11] (StorePre 0x107630 4 (fun s => AddrMode.addr (.base 3 (.d8 0x11)) s (0x107630 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x107630 4 1 (.base 3 (.d8 0x11)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x107630 4 1 (.base 3 (.d8 0x11))).toInstrSpec (mov_m16_r16_effect_step 0x107630 1 (.base 3 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x107634 [0x48, 0x8B, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x107634 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107634 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107634 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x107634 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x107634 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10763c [0x48, 0x8B, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x10763c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10763c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10763c 2 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10763c 2 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x10763c 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x107644 [0x48, 0x89, 0x4B, 0x15] (StorePre 0x107644 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x107644 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107644 1 (.base 3 (.d8 0x15)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x107644 1 (.base 3 (.d8 0x15))).toInstrSpec (mov_m64_r64_effect_step 0x107644 0x48 (by decide) 1 (.base 3 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x107648 [0x48, 0x89, 0x53, 0x1D] (StorePre 0x107648 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x107648 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107648 2 (.base 3 (.d8 0x1d)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x107648 2 (.base 3 (.d8 0x1d))).toInstrSpec (mov_m64_r64_effect_step 0x107648 0x48 (by decide) 2 (.base 3 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10764c [0x48, 0x8B, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x10764c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10764c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10764c 1 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10764c 1 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x10764c 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x107654 [0x48, 0x89, 0x4B, 0x25] (StorePre 0x107654 4 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x107654 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107654 1 (.base 3 (.d8 0x25)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x107654 1 (.base 3 (.d8 0x25))).toInstrSpec (mov_m64_r64_effect_step 0x107654 0x48 (by decide) 1 (.base 3 (.d8 0x25)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x107658 [0x48, 0x8B, 0x8C, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x107658 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x107658 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107658 1 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x107658 1 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x107658 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x107660 [0x48, 0x89, 0x4B, 0x2D] (StorePre 0x107660 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x107660 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107660 1 (.base 3 (.d8 0x2d)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x107660 1 (.base 3 (.d8 0x2d))).toInstrSpec (mov_m64_r64_effect_step 0x107660 0x48 (by decide) 1 (.base 3 (.d8 0x2d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x107664 [0x48, 0x8B, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x107664 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x107664 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107664 1 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x107664 1 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x107664 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10766c [0x48, 0x89, 0x4B, 0x35] (StorePre 0x10766c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x35)) s (0x10766c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10766c 1 (.base 3 (.d8 0x35)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10766c 1 (.base 3 (.d8 0x35))).toInstrSpec (mov_m64_r64_effect_step 0x10766c 0x48 (by decide) 1 (.base 3 (.d8 0x35)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x107670 [0x8B, 0x8C, 0x24, 0xAF, 0x00, 0x00, 0x00] (LoadPre 0x107670 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaf)) s (0x107670 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x107670 1 (.sib 4 none 0 (.d32 0xaf)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x107670 1 (.sib 4 none 0 (.d32 0xaf))).toInstrSpec (mov_r32_m32_low_effect_step 0x107670 1 (.sib 4 none 0 (.d32 0xaf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x107677 [0x89, 0x4B, 0x3C] (StorePre 0x107677 3 (fun s => AddrMode.addr (.base 3 (.d8 0x3c)) s (0x107677 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x107677 1 (.base 3 (.d8 0x3c)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107677 1 (.base 3 (.d8 0x3c))).toInstrSpec (mov_m32_r32_low_effect_step 0x107677 1 (.base 3 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10767a [0xC6, 0x03, 0xFF] (StorePre 0x10767a 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10767a + BitVec.ofNat 64 3)) 1) (movM8Imm8Effect 0x10767a (.base 3 .none) 0xff)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x10767a (.base 3 .none) 0xff).toInstrSpec (mov_m8_imm8_effect_step 0x10767a (.base 3 .none) (by decide) (by decide) (by decide) 0xff) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x10767d [0xC7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10767d 7 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10767d + BitVec.ofNat 64 7)) 4) (movM32Imm32Effect 0x10767d 7 (.base 3 (.d8 0x8)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x10767d 7 (.base 3 (.d8 0x8)) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x10767d (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x107684 [0xC6, 0x43, 0x10, 0x15] (StorePre 0x107684 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x107684 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x107684 (.base 3 (.d8 0x10)) 0x15)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x107684 (.base 3 (.d8 0x10)) 0x15).toInstrSpec (mov_m8_imm8_effect_step 0x107684 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide) 0x15) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x107688 [0x88, 0x43, 0x14] (StorePre 0x107688 3 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x107688 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x107688 3 0 (.base 3 (.d8 0x14)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x107688 3 0 (.base 3 (.d8 0x14))).toInstrSpec (mov_m8_r8_effect_step 0x107688 0 (by decide) (.base 3 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107628) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10762b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107630) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107634) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10763c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107644) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 59), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107648) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 59), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10764c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107654) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 65), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107658) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 68), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107660) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 68), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107664) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 71), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10766c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 71), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107670) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 74), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107677) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 74), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10767a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 74), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10767d) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 74), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107684) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 74), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107688) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 74), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10768b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 81) (by decide) rfl

theorem block_l107623 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107623 :=
  Rest.liftedBlock (rest_l107623 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107623 x hx)

theorem rest_l10768b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10768b bytes_l10768b) (entryMap (live .l10768b))
      9 0x10768b bytes_l10768b b_l10768b := by
  have f0 : InstrSpec 0x10768b [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10768b) (movR64R64Effect 0x10768b 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10768b 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10768b 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10768e [0x48, 0x81, 0xC4, 0xD8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10768e) (addR64Imm32Effect 0x10768e 4 0x1d8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x10768e 4 0x1d8).toInstrSpec (add_r64_imm32_effect_step 0x10768e 0x48 0xc4 0x1d8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x107695 [0x5B] (PopPre 0x107695) (popR64Effect 0x107695 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x107695 1 3).toInstrSpec (pop_r64_effect_step 0x107695 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x107696 [0x41, 0x5C] (PopPre 0x107696) (popR64Effect 0x107696 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x107696 2 12).toInstrSpec (pop_r64_rex_effect_step 0x107696 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x107698 [0x41, 0x5D] (PopPre 0x107698) (popR64Effect 0x107698 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x107698 2 13).toInstrSpec (pop_r64_rex_effect_step 0x107698 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10769a [0x41, 0x5E] (PopPre 0x10769a) (popR64Effect 0x10769a 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10769a 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10769a 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10769c [0x41, 0x5F] (PopPre 0x10769c) (popR64Effect 0x10769c 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10769c 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10769c 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x10769e [0x5D] (PopPre 0x10769e) (popR64Effect 0x10769e 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10769e 1 5).toInstrSpec (pop_r64_effect_step 0x10769e 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x10769f [0xC3] (RetPre 0x10769f) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10769f).toInstrSpec (ret_effect_step 0x10769f) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10768e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107695) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107696) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107698) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10769a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10769c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10769e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10769f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l10768b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10768b :=
  Rest.liftedBlock (rest_l10768b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10768b x hx)

theorem rest_l1076a0_1 [Bindings] (code : CodeMap) :
    Rest (n := 82) code lifted (codeRange 0x1076a0 bytes_l1076a0) [(0, 80), (1, 67), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x10770b bytes_l1076a0_1 b_l1076a0_1 := by
  have f20 : InstrSpec 0x10770b [0x66, 0x89, 0x43, 0x09] (StorePre 0x10770b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x9)) s (0x10770b + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10770b 4 0 (.base 3 (.d8 0x9)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x10770b 4 0 (.base 3 (.d8 0x9))).toInstrSpec (mov_m16_r16_effect_step 0x10770b 0 (.base 3 (.d8 0x9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x10770f [0x0F, 0xB6, 0x44, 0x24, 0x06] (LoadPre 0x10770f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x10770f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10770f 5 0 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10770f 5 0 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (movzx_r32_m8_effect_step 0x10770f 0 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x107714 [0x88, 0x43, 0x0B] (StorePre 0x107714 3 (fun s => AddrMode.addr (.base 3 (.d8 0xb)) s (0x107714 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x107714 3 0 (.base 3 (.d8 0xb)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x107714 3 0 (.base 3 (.d8 0xb))).toInstrSpec (mov_m8_r8_effect_step 0x107714 0 (by decide) (.base 3 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x107717 [0x44, 0x88, 0x63, 0x0C] (StorePre 0x107717 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x107717 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107717 4 12 (.base 3 (.d8 0xc)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x107717 4 12 (.base 3 (.d8 0xc))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107717 0x44 (by decide) 4 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x10771b [0xC6, 0x03, 0xFE] (StorePre 0x10771b 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10771b + BitVec.ofNat 64 3)) 1) (movM8Imm8Effect 0x10771b (.base 3 .none) 0xfe)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x10771b (.base 3 .none) 0xfe).toInstrSpec (mov_m8_imm8_effect_step 0x10771b (.base 3 .none) (by decide) (by decide) (by decide) 0xfe) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 67), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10770f) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 67), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107714) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 83), (1, 67), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107717) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 83), (1, 67), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10771b) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 83), (1, 67), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10771e) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 88) (jmp_rel32_effect_step 0x10771e 0xffffff68 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l1076a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1076a0 bytes_l1076a0) (entryMap (live .l1076a0))
      26 0x1076a0 bytes_l1076a0 b_l1076a0 := by
  have f0 : InstrSpec 0x1076a0 [0x0F, 0xB6, 0x44, 0x24, 0x02] (LoadPre 0x1076a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1076a0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1076a0 5 0 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1076a0 5 0 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (movzx_r32_m8_effect_step 0x1076a0 0 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1076a5 [0x88, 0x44, 0x24, 0x06] (StorePre 0x1076a5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1076a5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1076a5 4 0 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1076a5 4 0 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (mov_m8_r8_effect_step 0x1076a5 0 (by decide) (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1076a9 [0x0F, 0xB7, 0x04, 0x24] (LoadPre 0x1076a9 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1076a9 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x1076a9 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1076a9 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x1076a9 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1076ad [0x66, 0x89, 0x44, 0x24, 0x04] (StorePre 0x1076ad 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1076ad + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1076ad 5 0 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1076ad 5 0 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m16_r16_effect_step 0x1076ad 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1076b2 [0x8B, 0x44, 0x24, 0x27] (LoadPre 0x1076b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x1076b2 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1076b2 0 (.sib 4 none 0 (.d8 0x27)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1076b2 0 (.sib 4 none 0 (.d8 0x27))).toInstrSpec (mov_r32_m32_low_effect_step 0x1076b2 0 (.sib 4 none 0 (.d8 0x27)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1076b6 [0x89, 0x84, 0x24, 0x9F, 0x00, 0x00, 0x00] (StorePre 0x1076b6 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x1076b6 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1076b6 0 (.sib 4 none 0 (.d32 0x9f)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1076b6 0 (.sib 4 none 0 (.d32 0x9f))).toInstrSpec (mov_m32_r32_low_effect_step 0x1076b6 0 (.sib 4 none 0 (.d32 0x9f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1076bd [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x1076bd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1076bd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1076bd 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1076bd 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1076bd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1076c2 [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x1076c2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1076c2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1076c2 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1076c2 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x1076c2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1076ca [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1076ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1076ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1076ca 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1076ca 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1076ca 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1076cf [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x1076cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1076cf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1076cf 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1076cf 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1076cf 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1076d4 [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1076d4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1076d4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1076d4 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1076d4 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x1076d4 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1076dc [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x1076dc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1076dc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1076dc 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1076dc 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x1076dc 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1076e4 [0x8B, 0x94, 0x24, 0x9F, 0x00, 0x00, 0x00] (LoadPre 0x1076e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x1076e4 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1076e4 2 (.sib 4 none 0 (.d32 0x9f)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1076e4 2 (.sib 4 none 0 (.d32 0x9f))).toInstrSpec (mov_r32_m32_low_effect_step 0x1076e4 2 (.sib 4 none 0 (.d32 0x9f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1076eb [0x89, 0x53, 0x24] (StorePre 0x1076eb 3 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x1076eb + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1076eb 2 (.base 3 (.d8 0x24)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1076eb 2 (.base 3 (.d8 0x24))).toInstrSpec (mov_m32_r32_low_effect_step 0x1076eb 2 (.base 3 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1076ee [0x48, 0x8B, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x1076ee (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1076ee + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1076ee 2 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1076ee 2 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x1076ee 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1076f6 [0x48, 0x89, 0x53, 0x1D] (StorePre 0x1076f6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x1076f6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1076f6 2 (.base 3 (.d8 0x1d)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1076f6 2 (.base 3 (.d8 0x1d))).toInstrSpec (mov_m64_r64_effect_step 0x1076f6 0x48 (by decide) 2 (.base 3 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1076fa [0x48, 0x89, 0x4B, 0x15] (StorePre 0x1076fa 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x1076fa + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1076fa 1 (.base 3 (.d8 0x15)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1076fa 1 (.base 3 (.d8 0x15))).toInstrSpec (mov_m64_r64_effect_step 0x1076fa 0x48 (by decide) 1 (.base 3 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1076fe [0x48, 0x89, 0x43, 0x0D] (StorePre 0x1076fe 4 (fun s => AddrMode.addr (.base 3 (.d8 0xd)) s (0x1076fe + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1076fe 0 (.base 3 (.d8 0xd)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1076fe 0 (.base 3 (.d8 0xd))).toInstrSpec (mov_m64_r64_effect_step 0x1076fe 0x48 (by decide) 0 (.base 3 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x107702 [0x40, 0x88, 0x6B, 0x08] (StorePre 0x107702 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x107702 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107702 4 5 (.base 3 (.d8 0x8)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x107702 4 5 (.base 3 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107702 0x40 (by decide) 5 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x107706 [0x0F, 0xB7, 0x44, 0x24, 0x04] (LoadPre 0x107706 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x107706 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x107706 5 0 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x107706 5 0 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (movzx_r32_m16_effect_step 0x107706 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076a5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076a9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076ad) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076b2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076b6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076bd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076c2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076ca) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076cf) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 67), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076d4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 65), (1, 67), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076dc) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 67), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076e4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (1, 67), (2, 71), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076eb) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 65), (1, 67), (2, 71), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076ee) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 65), (1, 67), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076f6) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 65), (1, 67), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076fa) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 65), (1, 67), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1076fe) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 65), (1, 67), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107702) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 65), (1, 67), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107706) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 67), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10770b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1076a0_1 code

theorem block_l1076a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1076a0 :=
  Rest.liftedBlock (rest_l1076a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1076a0 x hx)

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

theorem_by block_l106dd0_eval :
    program.runBlock (dialect code) ⟨.l106dd0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106e2d_eval :
    program.runBlock (dialect code) ⟨.l106e2d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106e35_eval :
    program.runBlock (dialect code) ⟨.l106e35, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106ee4_eval :
    program.runBlock (dialect code) ⟨.l106ee4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106eed_eval :
    program.runBlock (dialect code) ⟨.l106eed, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106f3b_eval :
    program.runBlock (dialect code) ⟨.l106f3b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106f45_eval :
    program.runBlock (dialect code) ⟨.l106f45, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106f49_eval :
    program.runBlock (dialect code) ⟨.l106f49, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106f5b_eval :
    program.runBlock (dialect code) ⟨.l106f5b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106f70_eval :
    program.runBlock (dialect code) ⟨.l106f70, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106faa_eval :
    program.runBlock (dialect code) ⟨.l106faa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106fd4_eval :
    program.runBlock (dialect code) ⟨.l106fd4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107006_eval :
    program.runBlock (dialect code) ⟨.l107006, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107052_eval :
    program.runBlock (dialect code) ⟨.l107052, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107097_eval :
    program.runBlock (dialect code) ⟨.l107097, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1070eb_eval :
    program.runBlock (dialect code) ⟨.l1070eb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107105_eval :
    program.runBlock (dialect code) ⟨.l107105, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107109_eval :
    program.runBlock (dialect code) ⟨.l107109, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107110_eval :
    program.runBlock (dialect code) ⟨.l107110, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107116_eval :
    program.runBlock (dialect code) ⟨.l107116, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107126_eval :
    program.runBlock (dialect code) ⟨.l107126, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107134_eval :
    program.runBlock (dialect code) ⟨.l107134, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107139_eval :
    program.runBlock (dialect code) ⟨.l107139, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107150_eval :
    program.runBlock (dialect code) ⟨.l107150, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10718f_eval :
    program.runBlock (dialect code) ⟨.l10718f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10719f_eval :
    program.runBlock (dialect code) ⟨.l10719f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10724d_eval :
    program.runBlock (dialect code) ⟨.l10724d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1072b1_eval :
    program.runBlock (dialect code) ⟨.l1072b1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1072ba_eval :
    program.runBlock (dialect code) ⟨.l1072ba, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1072d4_eval :
    program.runBlock (dialect code) ⟨.l1072d4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1072e2_eval :
    program.runBlock (dialect code) ⟨.l1072e2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107307_eval :
    program.runBlock (dialect code) ⟨.l107307, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10731b_eval :
    program.runBlock (dialect code) ⟨.l10731b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10747b_eval :
    program.runBlock (dialect code) ⟨.l10747b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107488_eval :
    program.runBlock (dialect code) ⟨.l107488, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10749a_eval :
    program.runBlock (dialect code) ⟨.l10749a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10749f_eval :
    program.runBlock (dialect code) ⟨.l10749f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1074bd_eval :
    program.runBlock (dialect code) ⟨.l1074bd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1074d4_eval :
    program.runBlock (dialect code) ⟨.l1074d4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1074e9_eval :
    program.runBlock (dialect code) ⟨.l1074e9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10751b_eval :
    program.runBlock (dialect code) ⟨.l10751b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107535_eval :
    program.runBlock (dialect code) ⟨.l107535, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10753c_eval :
    program.runBlock (dialect code) ⟨.l10753c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10754e_eval :
    program.runBlock (dialect code) ⟨.l10754e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107564_eval :
    program.runBlock (dialect code) ⟨.l107564, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10756c_eval :
    program.runBlock (dialect code) ⟨.l10756c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107623_eval :
    program.runBlock (dialect code) ⟨.l107623, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10768b_eval :
    program.runBlock (dialect code) ⟨.l10768b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1076a0_eval :
    program.runBlock (dialect code) ⟨.l1076a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
