import K256.Proofs.Generate.LIR.CallPre
import K256.Proofs.Signing.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Signing.LIR.Generated.Values

namespace K256.Proofs.Signing.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR K256.Proofs.Verify.LIR

theorem rest_l107a50_1 [Bindings] (code : CodeMap) :
    Rest (n := 87) code lifted (codeRange 0x107a50 bytes_l107a50) [(0, 82), (1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x107acb bytes_l107a50_1 b_l107a50_1 := by
  have f20 : InstrSpec 0x107acb [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107acb) (movR32Imm32Effect 0x107acb 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x107acb 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x107acb 0xba (by decide) 0x1) pre_rip
  have f21 : InstrSpec 0x107ad0 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x107ad0) (movR64R64Effect 0x107ad0 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107ad0 7 14).toInstrSpec (mov_r64_r64_effect_step 0x107ad0 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x107ad3 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x107ad3) (movR64R64Effect 0x107ad3 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x107ad3 6 15).toInstrSpec (mov_r64_r64_effect_step 0x107ad3 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x107ad6 [0xE8, 0x05, 0x9E, 0x01, 0x00] (PushPre 0x107ad6 5) (callEffect (fun _ => 0x1218e0) 0x107adb)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107ad6 0x1218e0 0x107adb).toInstrSpec (call_rel32_effect_step 0x107ad6 0x19e05 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 82), (1, 1), (2, 87), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ad0) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f21 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 82), (1, 1), (2, 87), (3, 67), (4, 65), (5, 5), (6, 6), (7, 89), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ad3) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f22 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 82), (1, 1), (2, 87), (3, 67), (4, 65), (5, 5), (6, 91), (7, 89), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ad6) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f23 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 82), (1, 1), (2, 87), (3, 67), (4, 93), (5, 5), (6, 91), (7, 89), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f23 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 95) (by decide) (by decide) rfl rfl

theorem rest_l107a50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107a50 bytes_l107a50) (entryMap (live .l107a50))
      24 0x107a50 bytes_l107a50 b_l107a50 := by
  have f0 : InstrSpec 0x107a50 [0x55] (PushPre 0x107a50 1) (pushR64Effect 0x107a50 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107a50 1 5).toInstrSpec (push_r64_effect_step 0x107a50 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x107a51 [0x41, 0x57] (PushPre 0x107a51 2) (pushR64Effect 0x107a51 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107a51 2 15).toInstrSpec (push_r64_rex_effect_step 0x107a51 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x107a53 [0x41, 0x56] (PushPre 0x107a53 2) (pushR64Effect 0x107a53 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107a53 2 14).toInstrSpec (push_r64_rex_effect_step 0x107a53 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x107a55 [0x41, 0x55] (PushPre 0x107a55 2) (pushR64Effect 0x107a55 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107a55 2 13).toInstrSpec (push_r64_rex_effect_step 0x107a55 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x107a57 [0x41, 0x54] (PushPre 0x107a57 2) (pushR64Effect 0x107a57 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107a57 2 12).toInstrSpec (push_r64_rex_effect_step 0x107a57 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x107a59 [0x53] (PushPre 0x107a59 1) (pushR64Effect 0x107a59 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x107a59 1 3).toInstrSpec (push_r64_effect_step 0x107a59 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x107a5a [0x48, 0x81, 0xEC, 0x38, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x107a5a) (subR64Imm32Effect 0x107a5a 4 0x138)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x107a5a 4 0x138).toInstrSpec (sub_r64_imm32_effect_step 0x107a5a 0x48 0xec 0x138 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x107a61 [0x48, 0x89, 0xF3] (fun s => s.RIP = 0x107a61) (movR64R64Effect 0x107a61 3 6)
      [.gpr 6] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x107a61 3 6).toInstrSpec (mov_r64_r64_effect_step 0x107a61 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x107a64 [0x49, 0x89, 0xFF] (fun s => s.RIP = 0x107a64) (movR64R64Effect 0x107a64 15 7)
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x107a64 15 7).toInstrSpec (mov_r64_r64_effect_step 0x107a64 0x49 0xff (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x107a67 [0x4C, 0x8D, 0xB4, 0x24, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x107a67) (leaR64Effect 0x107a67 14 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x107a67 14 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (lea_r64_effect_step 0x107a67 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x107a6f [0x48, 0xB8, 0xAB, 0xD9, 0x83, 0x1F, 0x19, 0xCD, 0xE0, 0x5B] (fun s => s.RIP = 0x107a6f) (movR64Imm64Effect 0x107a6f 0 0x5be0cd191f83d9ab)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x107a6f 0 0x5be0cd191f83d9ab).toInstrSpec (mov_r64_imm64_effect_step 0x107a6f 0x48 0xb8 (by decide) (by decide) 0x5be0cd191f83d9ab) pre_rip
  have f11 : InstrSpec 0x107a79 [0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00] (StorePre 0x107a79 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x107a79 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107a79 0 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107a79 0 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_m64_r64_effect_step 0x107a79 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x107a81 [0x48, 0xB8, 0x7F, 0x52, 0x0E, 0x51, 0x8C, 0x68, 0x05, 0x9B] (fun s => s.RIP = 0x107a81) (movR64Imm64Effect 0x107a81 0 0x9b05688c510e527f)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x107a81 0 0x9b05688c510e527f).toInstrSpec (mov_r64_imm64_effect_step 0x107a81 0x48 0xb8 (by decide) (by decide) 0x9b05688c510e527f) pre_rip
  have f13 : InstrSpec 0x107a8b [0x48, 0x89, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00] (StorePre 0x107a8b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x107a8b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107a8b 0 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107a8b 0 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_m64_r64_effect_step 0x107a8b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x107a93 [0x48, 0xB8, 0x72, 0xF3, 0x6E, 0x3C, 0x3A, 0xF5, 0x4F, 0xA5] (fun s => s.RIP = 0x107a93) (movR64Imm64Effect 0x107a93 0 0xa54ff53a3c6ef372)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x107a93 0 0xa54ff53a3c6ef372).toInstrSpec (mov_r64_imm64_effect_step 0x107a93 0x48 0xb8 (by decide) (by decide) 0xa54ff53a3c6ef372) pre_rip
  have f15 : InstrSpec 0x107a9d [0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x107a9d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x107a9d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107a9d 0 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107a9d 0 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m64_r64_effect_step 0x107a9d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x107aa5 [0x48, 0xB8, 0x67, 0xE6, 0x09, 0x6A, 0x85, 0xAE, 0x67, 0xBB] (fun s => s.RIP = 0x107aa5) (movR64Imm64Effect 0x107aa5 0 0xbb67ae856a09e667)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x107aa5 0 0xbb67ae856a09e667).toInstrSpec (mov_r64_imm64_effect_step 0x107aa5 0x48 0xb8 (by decide) (by decide) 0xbb67ae856a09e667) pre_rip
  have f17 : InstrSpec 0x107aaf [0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x107aaf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x107aaf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107aaf 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107aaf 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m64_r64_effect_step 0x107aaf 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x107ab7 [0xC6, 0x84, 0x24, 0x0F, 0x01, 0x00, 0x00, 0x00] (StorePre 0x107ab7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10f)) s (0x107ab7 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x107ab7 (.sib 4 none 0 (.d32 0x10f)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x107ab7 (.sib 4 none 0 (.d32 0x10f)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x107ab7 (.sib 4 none 0 (.d32 0x10f)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x107abf [0x48, 0xC7, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (StorePre 0x107abf 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x107abf + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x107abf (.sib 4 none 0 (.d32 0x130)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107abf (.sib 4 none 0 (.d32 0x130)) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x107abf 0x48 (by decide) (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a51) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a53) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a55) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a57) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a59) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a5a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a61) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a64) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a67) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a6f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a79) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 73), (1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a81) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a8b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 76), (1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a93) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a9d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107aa5) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107aaf) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 82), (1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ab7) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 82), (1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107abf) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 82), (1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107acb) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107a50_1 code

theorem block_l107a50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107a50 :=
  Rest.liftedBlock (rest_l107a50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107a50 x hx)

theorem rest_l107adb [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107adb bytes_l107adb) (entryMap (live .l107adb))
      17 0x107adb bytes_l107adb b_l107adb := by
  have f0 : InstrSpec 0x107adb [0xC6, 0x84, 0x24, 0x0F, 0x01, 0x00, 0x00, 0x00] (StorePre 0x107adb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10f)) s (0x107adb + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x107adb (.sib 4 none 0 (.d32 0x10f)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x107adb (.sib 4 none 0 (.d32 0x10f)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x107adb (.sib 4 none 0 (.d32 0x10f)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x107ae3 [0x49, 0x83, 0xC7, 0x40] (fun s => s.RIP = 0x107ae3) (addR64Imm8Effect 0x107ae3 15 0x40)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x107ae3 15 0x40).toInstrSpec (add_r64_imm8_effect_step 0x107ae3 0x49 0xc7 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x107ae7 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x107ae7) (leaR64Effect 0x107ae7 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x107ae7 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x107ae7 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x107aec [0xB9, 0x0D, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107aec) (movR32Imm32Effect 0x107aec 5 1 0xd)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x107aec 5 1 0xd).toInstrSpec (mov_r32_imm32_effect_step 0x107aec 0xb9 (by decide) 0xd) pre_rip
  have f4 : InstrSpec 0x107af1 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x107af1) (movR64R64Effect 0x107af1 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x107af1 6 15).toInstrSpec (mov_r64_r64_effect_step 0x107af1 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x107af4 [0xF3, 0x48, 0xA5] (RepPre 0x107af4 (RepMovsqPre 0x107af4)) (repMovsqEffect 0x107af4)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x107af4).toInstrSpecOfRuns (rep_movsq_runs hstride 0x107af4 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f6 : InstrSpec 0x107af7 [0x4C, 0x8D, 0x7C, 0x24, 0x48] (fun s => s.RIP = 0x107af7) (leaR64Effect 0x107af7 15 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x107af7 15 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x107af7 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x107afc [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x47] (LoadPre 0x107afc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x107afc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107afc 6 13 (.sib 4 none 0 (.d8 0x47)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x107afc 6 13 (.sib 4 none 0 (.d8 0x47))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107afc 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x47)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x107b02 [0x48, 0x8B, 0x6C, 0x24, 0x68] (LoadPre 0x107b02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x107b02 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b02 5 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x107b02 5 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x107b02 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x107b07 [0x4D, 0x89, 0xEC] (fun s => s.RIP = 0x107b07) (movR64R64Effect 0x107b07 12 13)
      [.gpr 13] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x107b07 12 13).toInstrSpec (mov_r64_r64_effect_step 0x107b07 0x4d 0xec (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x107b0a [0x49, 0x83, 0xF4, 0x3F] (fun s => s.RIP = 0x107b0a) (xorR64Imm8Effect 0x107b0a 12 0x3f)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR64Imm8Effect_footprint 0x107b0a 12 0x3f).toInstrSpec (xor_r64_imm8_effect_step 0x107b0a 0x49 0xf4 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x107b0e [0x42, 0xC6, 0x44, 0x2C, 0x08, 0x80] (StorePre 0x107b0e 6 (fun s => AddrMode.addr (.sib 4 (some 13) 0 (.d8 0x8)) s (0x107b0e + BitVec.ofNat 64 6)) 1) (movM8Imm8RexEffect 0x107b0e (.sib 4 (some 13) 0 (.d8 0x8)) 0x80)
      [.gpr 4, .gpr 13] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x107b0e (.sib 4 (some 13) 0 (.d8 0x8)) 0x80).toInstrSpec (mov_m8_imm8_rex_effect_step 0x107b0e 0x42 (by decide) (.sib 4 (some 13) 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x80) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x107b14 [0x4A, 0x8D, 0x3C, 0x2C] (fun s => s.RIP = 0x107b14) (leaR64Effect 0x107b14 7 (.sib 4 (some 13) 0 .none))
      [.gpr 4, .gpr 13] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x107b14 7 (.sib 4 (some 13) 0 .none)).toInstrSpec (lea_r64_effect_step 0x107b14 0x4a (by decide) 7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x107b18 [0x48, 0x83, 0xC7, 0x09] (fun s => s.RIP = 0x107b18) (addR64Imm8Effect 0x107b18 7 0x9)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x107b18 7 0x9).toInstrSpec (add_r64_imm8_effect_step 0x107b18 0x48 0xc7 0x9 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x107b1c [0x31, 0xF6] (fun s => s.RIP = 0x107b1c) (xorR32R32Effect 0x107b1c 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x107b1c 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x107b1c 0xf6 (by decide)) pre_rip
  have f15 : InstrSpec 0x107b1e [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x107b1e) (movR64R64Effect 0x107b1e 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x107b1e 2 12).toInstrSpec (mov_r64_r64_effect_step 0x107b1e 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x107b21 [0xFF, 0x15, 0xE9, 0xC2, 0x0F, 0x00] (GoesTo (CallMemPre 0x107b21 (.rip 0xfc2e9)) (callEffect (callMemPtr 0x107b21 (.rip 0xfc2e9)) (0x107b21 + BitVec.ofNat 64 (callMemLen (.rip 0xfc2e9)))) 0x12a700) (callEffect (callMemPtr 0x107b21 (.rip 0xfc2e9)) (0x107b21 + BitVec.ofNat 64 (callMemLen (.rip 0xfc2e9))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x107b21 (.rip 0xfc2e9)).toInstrSpec (call_m64_effect_step 0x107b21 (.rip 0xfc2e9) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a700
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ae3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (14, 14), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ae7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (7, 56), (9, 9), (10, 10), (11, 11), (14, 14), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107aec) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 58), (3, 3), (4, 4), (7, 56), (9, 9), (10, 10), (11, 11), (14, 14), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107af1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 58), (3, 3), (4, 4), (6, 60), (7, 56), (9, 9), (10, 10), (11, 11), (14, 14), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107af4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 4), (6, 62), (9, 9), (10, 10), (11, 11), (14, 14), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107af7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(3, 3), (4, 4), (6, 62), (9, 9), (10, 10), (11, 11), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107afc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(3, 3), (4, 4), (6, 62), (9, 9), (10, 10), (11, 11), (13, 66), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b02) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(3, 3), (4, 4), (5, 68), (6, 62), (9, 9), (10, 10), (11, 11), (13, 66), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b07) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(3, 3), (4, 4), (5, 68), (6, 62), (9, 9), (10, 10), (11, 11), (12, 70), (13, 66), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b0a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(3, 3), (4, 4), (5, 68), (6, 62), (9, 9), (10, 10), (11, 11), (12, 72), (13, 66), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b0e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(3, 3), (4, 4), (5, 68), (6, 62), (9, 9), (10, 10), (11, 11), (12, 72), (13, 66), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b14) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(3, 3), (4, 4), (5, 68), (6, 62), (7, 75), (9, 9), (10, 10), (11, 11), (12, 72), (13, 66), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b18) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(3, 3), (4, 4), (5, 68), (6, 62), (7, 77), (9, 9), (10, 10), (11, 11), (12, 72), (13, 66), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b1c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(3, 3), (4, 4), (5, 68), (6, 79), (7, 77), (9, 9), (10, 10), (11, 11), (12, 72), (13, 66), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b1e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(2, 81), (3, 3), (4, 4), (5, 68), (6, 79), (7, 77), (9, 9), (10, 10), (11, 11), (12, 72), (13, 66), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b21) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(2, 81), (3, 3), (4, 83), (5, 68), (6, 79), (7, 77), (9, 9), (10, 10), (11, 11), (12, 72), (13, 66), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a700) f16 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l107adb [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107adb :=
  Rest.liftedBlock (rest_l107adb hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107adb x hx)

theorem rest_l107b27 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107b27 bytes_l107b27) (entryMap (live .l107b27))
      2 0x107b27 bytes_l107b27 b_l107b27 := by
  have f0 : InstrSpec 0x107b27 [0x49, 0x83, 0xFC, 0x07] (fun s => s.RIP = 0x107b27) (cmpR64Imm8Effect 0x107b27 12 0x7)
      [.gpr 12] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x107b27 12 0x7).toInstrSpec (cmp_r64_imm8_effect_step 0x107b27 0x49 0xfc 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b2b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x107b2b 7 0xb3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l107b27 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107b27 :=
  Rest.liftedBlock (rest_l107b27 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107b27 x hx)

theorem rest_l107b31 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107b31 bytes_l107b31) (entryMap (live .l107b31))
      20 0x107b31 bytes_l107b31 b_l107b31 := by
  have f0 : InstrSpec 0x107b31 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x107b31 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107b31 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b31 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107b31 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x107b31 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107b36 [0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x107b36 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x107b36 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107b36 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107b36 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x107b36 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x107b3e [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x107b3e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107b3e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b3e 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107b3e 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x107b3e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x107b43 [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x107b43 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x107b43 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107b43 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107b43 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x107b43 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x107b4b [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x107b4b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107b4b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b4b 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107b4b 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x107b4b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x107b50 [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x107b50 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x107b50 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107b50 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107b50 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x107b50 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x107b58 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x107b58 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107b58 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b58 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107b58 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x107b58 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x107b5d [0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x107b5d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107b5d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107b5d 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107b5d 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x107b5d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x107b65 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x107b65 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107b65 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b65 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107b65 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x107b65 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x107b6a [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x107b6a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107b6a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107b6a 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107b6a 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x107b6a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x107b72 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x107b72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107b72 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b72 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107b72 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x107b72 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x107b77 [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x107b77 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107b77 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107b77 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107b77 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x107b77 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x107b7f [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x107b7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107b7f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b7f 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107b7f 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x107b7f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x107b84 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x107b84 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107b84 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b84 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x107b84 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x107b84 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x107b89 [0x48, 0x89, 0x4C, 0x24, 0x78] (StorePre 0x107b89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107b89 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107b89 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107b89 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x107b89 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x107b8e [0x48, 0x89, 0x44, 0x24, 0x70] (StorePre 0x107b8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x107b8e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107b8e 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107b8e 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x107b8e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x107b93 [0x48, 0x8D, 0x74, 0x24, 0x70] (fun s => s.RIP = 0x107b93) (leaR64Effect 0x107b93 6 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x107b93 6 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (lea_r64_effect_step 0x107b93 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x107b98 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107b98) (movR32Imm32Effect 0x107b98 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x107b98 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x107b98 0xba (by decide) 0x1) pre_rip
  have f18 : InstrSpec 0x107b9d [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x107b9d) (movR64R64Effect 0x107b9d 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107b9d 7 15).toInstrSpec (mov_r64_r64_effect_step 0x107b9d 0x4c 0xff (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x107ba0 [0xE8, 0x3B, 0x9D, 0x01, 0x00] (PushPre 0x107ba0 5) (callEffect (fun _ => 0x1218e0) 0x107ba5)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107ba0 0x1218e0 0x107ba5).toInstrSpec (call_rel32_effect_step 0x107ba0 0x19d3b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b36) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b3e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b43) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b4b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b50) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b58) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b5d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b65) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b6a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b72) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b77) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b7f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b84) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b89) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b8e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b93) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (6, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b98) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 71), (1, 73), (2, 79), (3, 3), (4, 4), (5, 5), (6, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107b9d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 71), (1, 73), (2, 79), (3, 3), (4, 4), (5, 5), (6, 77), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ba0) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 71), (1, 73), (2, 79), (3, 3), (4, 83), (5, 5), (6, 77), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l107b31 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107b31 :=
  Rest.liftedBlock (rest_l107b31 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107b31 x hx)

theorem rest_l107ba5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107ba5 bytes_l107ba5) (entryMap (live .l107ba5))
      7 0x107ba5 bytes_l107ba5 b_l107ba5 := by
  have f0 : InstrSpec 0x107ba5 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107ba5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107ba5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ba5 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107ba5 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107ba5 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x107bae [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107bae 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107bae + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107bae (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107bae (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107bae 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x107bb7 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107bb7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107bb7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107bb7 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107bb7 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107bb7 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x107bc0 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107bc0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107bc0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107bc0 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107bc0 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107bc0 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x107bc9 [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107bc9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107bc9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107bc9 (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107bc9 (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107bc9 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x107bd2 [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107bd2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107bd2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107bd2 (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107bd2 (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107bd2 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x107bdb [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107bdb 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107bdb + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107bdb (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107bdb (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107bdb 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bae) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bb7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bc0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bc9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bd2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bdb) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107be4) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l107ba5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107ba5 :=
  Rest.liftedBlock (rest_l107ba5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107ba5 x hx)

theorem rest_l107be4_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x107be4 bytes_l107be4) [(0, 78), (1, 80), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x107c54 bytes_l107be4_1 b_l107be4_1 := by
  have f20 : InstrSpec 0x107c54 [0x48, 0x8D, 0x74, 0x24, 0x70] (fun s => s.RIP = 0x107c54) (leaR64Effect 0x107c54 6 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x107c54 6 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (lea_r64_effect_step 0x107c54 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x107c59 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107c59) (movR32Imm32Effect 0x107c59 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x107c59 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x107c59 0xba (by decide) 0x1) pre_rip
  have f22 : InstrSpec 0x107c5e [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x107c5e) (movR64R64Effect 0x107c5e 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107c5e 7 15).toInstrSpec (mov_r64_r64_effect_step 0x107c5e 0x4c 0xff (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x107c61 [0xE8, 0x7A, 0x9C, 0x01, 0x00] (PushPre 0x107c61 5) (callEffect (fun _ => 0x1218e0) 0x107c66)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107c61 0x1218e0 0x107c66).toInstrSpec (call_rel32_effect_step 0x107c61 0x19c7a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 53), (6, 84), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c59) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f21 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 78), (1, 80), (2, 86), (3, 3), (4, 4), (5, 53), (6, 84), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c5e) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f22 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 78), (1, 80), (2, 86), (3, 3), (4, 4), (5, 53), (6, 84), (7, 88), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c61) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f23 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 78), (1, 80), (2, 86), (3, 3), (4, 90), (5, 53), (6, 84), (7, 88), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f23 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 92) (by decide) (by decide) rfl rfl

theorem rest_l107be4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107be4 bytes_l107be4) (entryMap (live .l107be4))
      24 0x107be4 bytes_l107be4 b_l107be4 := by
  have f0 : InstrSpec 0x107be4 [0x48, 0xC1, 0xE5, 0x09] (fun s => s.RIP = 0x107be4) (shlR64Effect 0x107be4 4 5 9)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shlR64Effect_footprint 0x107be4 4 5 9).toInstrSpec (shl_r64_imm8_effect_step 0x107be4 0x48 0xe5 0x9 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x107be8 [0x41, 0xC1, 0xE5, 0x03] (fun s => s.RIP = 0x107be8) (shlR32Effect 0x107be8 4 13 3)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shlR32Effect_footprint 0x107be8 4 13 3).toInstrSpec (shl_r32_imm8_rex_effect_step 0x107be8 0x41 0xe5 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x107bec [0x49, 0x09, 0xED] (fun s => s.RIP = 0x107bec) (orR64R64Effect 0x107bec 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (orR64R64Effect_footprint 0x107bec 13 5).toInstrSpec (or_r64_r64_effect_step 0x107bec 0x49 0xed (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x107bef [0x49, 0x0F, 0xCD] (fun s => s.RIP = 0x107bef) (bswapR64Effect 0x107bef 3 13)
      [.gpr 13] [] [.reg 13, .rip] :=
    (bswapR64Effect_footprint 0x107bef 3 13).toInstrSpec (bswap_r64_effect_step 0x107bef 0x49 (by decide) 0xcd (by decide)) pre_rip
  have f4 : InstrSpec 0x107bf2 [0x4C, 0x89, 0x6C, 0x24, 0x40] (StorePre 0x107bf2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107bf2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107bf2 13 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107bf2 13 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x107bf2 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x107bf7 [0x4C, 0x89, 0xAC, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x107bf7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x107bf7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107bf7 13 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107bf7 13 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x107bf7 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x107bff [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x107bff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107bff + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107bff 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107bff 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x107bff 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x107c04 [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x107c04 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x107c04 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107c04 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107c04 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x107c04 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x107c0c [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x107c0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107c0c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c0c 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107c0c 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x107c0c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x107c11 [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x107c11 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x107c11 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107c11 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107c11 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x107c11 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x107c19 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x107c19 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107c19 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c19 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107c19 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x107c19 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x107c1e [0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x107c1e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107c1e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107c1e 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107c1e 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x107c1e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x107c26 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x107c26 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107c26 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c26 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107c26 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x107c26 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x107c2b [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x107c2b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107c2b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107c2b 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107c2b 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x107c2b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x107c33 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x107c33 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107c33 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c33 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107c33 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x107c33 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x107c38 [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x107c38 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107c38 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107c38 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107c38 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x107c38 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x107c40 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x107c40 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107c40 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c40 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107c40 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x107c40 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x107c45 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x107c45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107c45 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c45 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x107c45 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x107c45 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x107c4a [0x48, 0x89, 0x4C, 0x24, 0x78] (StorePre 0x107c4a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107c4a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107c4a 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107c4a 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x107c4a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x107c4f [0x48, 0x89, 0x44, 0x24, 0x70] (StorePre 0x107c4f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x107c4f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107c4f 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107c4f 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x107c4f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107be8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bec) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bef) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bf2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bf7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107bff) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c04) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c0c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c11) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c19) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c1e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c26) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c2b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c33) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c38) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c40) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c45) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c4a) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c4f) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c54) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107be4_1 code

theorem block_l107be4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107be4 :=
  Rest.liftedBlock (rest_l107be4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107be4 x hx)

theorem rest_l107c66_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x107c66 bytes_l107c66) [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]
      7 0x107cb8 bytes_l107c66_1 b_l107c66_1 := by
  have f20 : InstrSpec 0x107cb8 [0x89, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x107cb8 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x107cb8 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107cb8 7 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107cb8 7 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m32_r32_low_effect_step 0x107cb8 7 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x107cbf [0x44, 0x89, 0x84, 0x24, 0xC4, 0x00, 0x00, 0x00] (StorePre 0x107cbf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc4)) s (0x107cbf + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x107cbf 8 (.sib 4 none 0 (.d32 0xc4)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x107cbf 8 (.sib 4 none 0 (.d32 0xc4))).toInstrSpec (mov_m32_r32_effect_step 0x107cbf 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0xc4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x107cc7 [0x44, 0x89, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x107cc7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x107cc7 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x107cc7 9 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x107cc7 9 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m32_r32_effect_step 0x107cc7 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x107ccf [0x44, 0x89, 0x94, 0x24, 0xCC, 0x00, 0x00, 0x00] (StorePre 0x107ccf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc)) s (0x107ccf + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x107ccf 10 (.sib 4 none 0 (.d32 0xcc)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x107ccf 10 (.sib 4 none 0 (.d32 0xcc))).toInstrSpec (mov_m32_r32_effect_step 0x107ccf 0x44 (by decide) 2 (.sib 4 none 0 (.d32 0xcc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x107cd7 [0x44, 0x0F, 0xB6, 0xBC, 0x24, 0x0F, 0x01, 0x00, 0x00] (LoadPre 0x107cd7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10f)) s (0x107cd7 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107cd7 9 15 (.sib 4 none 0 (.d32 0x10f)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x107cd7 9 15 (.sib 4 none 0 (.d32 0x10f))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107cd7 0x44 (by decide) 7 (.sib 4 none 0 (.d32 0x10f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x107ce0 [0x49, 0x83, 0xFF, 0x1F] (fun s => s.RIP = 0x107ce0) (cmpR64Imm8Effect 0x107ce0 15 0x1f)
      [.gpr 15] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x107ce0 15 0x1f).toInstrSpec (cmp_r64_imm8_effect_step 0x107ce0 0x49 0xff 0x1f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cbf) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cc7) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ccf) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cd7) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f24 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (14, 14), (15, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ce0) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f25 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 96) f25 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 97) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (14, 14), (15, 93), (16, 95), (19, 96), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ce4) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 98) (jcc_rel8_effect_step 0x107ce4 7 0x4e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l107c66 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107c66 bytes_l107c66) (entryMap (live .l107c66))
      27 0x107c66 bytes_l107c66 b_l107c66 := by
  have f0 : InstrSpec 0x107c66 [0x8B, 0x44, 0x24, 0x48] (LoadPre 0x107c66 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x107c66 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107c66 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x107c66 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r32_m32_low_effect_step 0x107c66 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107c6a [0x8B, 0x4C, 0x24, 0x4C] (LoadPre 0x107c6a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x107c6a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107c6a 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x107c6a 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_r32_m32_low_effect_step 0x107c6a 1 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x107c6e [0x0F, 0xC8] (fun s => s.RIP = 0x107c6e) (bswapR32Effect 0x107c6e 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR32Effect_footprint 0x107c6e 2 0).toInstrSpec (bswap_r32_effect_step 0x107c6e 0xc8 (by decide)) pre_rip
  have f3 : InstrSpec 0x107c70 [0x0F, 0xC9] (fun s => s.RIP = 0x107c70) (bswapR32Effect 0x107c70 2 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR32Effect_footprint 0x107c70 2 1).toInstrSpec (bswap_r32_effect_step 0x107c70 0xc9 (by decide)) pre_rip
  have f4 : InstrSpec 0x107c72 [0x8B, 0x54, 0x24, 0x50] (LoadPre 0x107c72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x107c72 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107c72 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x107c72 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r32_m32_low_effect_step 0x107c72 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x107c76 [0x0F, 0xCA] (fun s => s.RIP = 0x107c76) (bswapR32Effect 0x107c76 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR32Effect_footprint 0x107c76 2 2).toInstrSpec (bswap_r32_effect_step 0x107c76 0xca (by decide)) pre_rip
  have f6 : InstrSpec 0x107c78 [0x8B, 0x74, 0x24, 0x54] (LoadPre 0x107c78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x107c78 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107c78 6 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x107c78 6 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_r32_m32_low_effect_step 0x107c78 6 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x107c7c [0x0F, 0xCE] (fun s => s.RIP = 0x107c7c) (bswapR32Effect 0x107c7c 2 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR32Effect_footprint 0x107c7c 2 6).toInstrSpec (bswap_r32_effect_step 0x107c7c 0xce (by decide)) pre_rip
  have f8 : InstrSpec 0x107c7e [0x8B, 0x7C, 0x24, 0x58] (LoadPre 0x107c7e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x107c7e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107c7e 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x107c7e 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r32_m32_low_effect_step 0x107c7e 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x107c82 [0x0F, 0xCF] (fun s => s.RIP = 0x107c82) (bswapR32Effect 0x107c82 2 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (bswapR32Effect_footprint 0x107c82 2 7).toInstrSpec (bswap_r32_effect_step 0x107c82 0xcf (by decide)) pre_rip
  have f10 : InstrSpec 0x107c84 [0x44, 0x8B, 0x44, 0x24, 0x5C] (LoadPre 0x107c84 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x107c84 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x107c84 8 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x107c84 8 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_r32_m32_effect_step 0x107c84 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x107c89 [0x41, 0x0F, 0xC8] (fun s => s.RIP = 0x107c89) (bswapR32Effect 0x107c89 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (bswapR32Effect_footprint 0x107c89 3 8).toInstrSpec (bswap_r32_rex_effect_step 0x107c89 0x41 (by decide) 0xc8 (by decide)) pre_rip
  have f12 : InstrSpec 0x107c8c [0x44, 0x8B, 0x4C, 0x24, 0x60] (LoadPre 0x107c8c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x107c8c + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x107c8c 9 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x107c8c 9 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r32_m32_effect_step 0x107c8c 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x107c91 [0x41, 0x0F, 0xC9] (fun s => s.RIP = 0x107c91) (bswapR32Effect 0x107c91 3 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (bswapR32Effect_footprint 0x107c91 3 9).toInstrSpec (bswap_r32_rex_effect_step 0x107c91 0x41 (by decide) 0xc9 (by decide)) pre_rip
  have f14 : InstrSpec 0x107c94 [0x44, 0x8B, 0x54, 0x24, 0x64] (LoadPre 0x107c94 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x107c94 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x107c94 10 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x107c94 10 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_r32_m32_effect_step 0x107c94 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x107c99 [0x41, 0x0F, 0xCA] (fun s => s.RIP = 0x107c99) (bswapR32Effect 0x107c99 3 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (bswapR32Effect_footprint 0x107c99 3 10).toInstrSpec (bswap_r32_rex_effect_step 0x107c99 0x41 (by decide) 0xca (by decide)) pre_rip
  have f16 : InstrSpec 0x107c9c [0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x107c9c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x107c9c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107c9c 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107c9c 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m32_r32_low_effect_step 0x107c9c 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x107ca3 [0x89, 0x8C, 0x24, 0xB4, 0x00, 0x00, 0x00] (StorePre 0x107ca3 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x107ca3 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107ca3 1 (.sib 4 none 0 (.d32 0xb4)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107ca3 1 (.sib 4 none 0 (.d32 0xb4))).toInstrSpec (mov_m32_r32_low_effect_step 0x107ca3 1 (.sib 4 none 0 (.d32 0xb4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x107caa [0x89, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x107caa 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x107caa + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107caa 2 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107caa 2 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m32_r32_low_effect_step 0x107caa 2 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x107cb1 [0x89, 0xB4, 0x24, 0xBC, 0x00, 0x00, 0x00] (StorePre 0x107cb1 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x107cb1 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107cb1 6 (.sib 4 none 0 (.d32 0xbc)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107cb1 6 (.sib 4 none 0 (.d32 0xbc))).toInstrSpec (mov_m32_r32_low_effect_step 0x107cb1 6 (.sib 4 none 0 (.d32 0xbc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c6a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c6e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c70) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c72) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c76) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c78) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 65), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c7c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c7e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 69), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c82) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c84) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 73), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c89) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c8c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 77), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c91) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c94) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 81), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c99) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107c9c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ca3) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107caa) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cb1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cb8) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107c66_1 code

theorem block_l107c66 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107c66 :=
  Rest.liftedBlock (rest_l107c66 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107c66 x hx)

theorem rest_l107ce6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107ce6 bytes_l107ce6) (entryMap (live .l107ce6))
      11 0x107ce6 bytes_l107ce6 b_l107ce6 := by
  have f0 : InstrSpec 0x107ce6 [0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x107ce6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x107ce6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107ce6 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107ce6 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x107ce6 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107cee [0x4A, 0x89, 0x84, 0x3C, 0xE8, 0x00, 0x00, 0x00] (StorePre 0x107cee 8 (fun s => AddrMode.addr (.sib 4 (some 15) 0 (.d32 0xe8)) s (0x107cee + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107cee 0 (.sib 4 (some 15) 0 (.d32 0xe8)))
      [.gpr 0, .gpr 4, .gpr 15] [] [.rip] :=
    (movM64R64Effect_footprint 0x107cee 0 (.sib 4 (some 15) 0 (.d32 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x107cee 0x4a (by decide) 0 (.sib 4 (some 15) 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x107cf6 [0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x107cf6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x107cf6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107cf6 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107cf6 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x107cf6 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x107cfe [0x4A, 0x89, 0x84, 0x3C, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x107cfe 8 (fun s => AddrMode.addr (.sib 4 (some 15) 0 (.d32 0xe0)) s (0x107cfe + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107cfe 0 (.sib 4 (some 15) 0 (.d32 0xe0)))
      [.gpr 0, .gpr 4, .gpr 15] [] [.rip] :=
    (movM64R64Effect_footprint 0x107cfe 0 (.sib 4 (some 15) 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x107cfe 0x4a (by decide) 0 (.sib 4 (some 15) 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x107d06 [0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x107d06 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x107d06 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107d06 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107d06 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x107d06 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x107d0e [0x48, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x107d0e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x107d0e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107d0e 1 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x107d0e 1 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x107d0e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x107d16 [0x4A, 0x89, 0x8C, 0x3C, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x107d16 8 (fun s => AddrMode.addr (.sib 4 (some 15) 0 (.d32 0xd8)) s (0x107d16 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107d16 1 (.sib 4 (some 15) 0 (.d32 0xd8)))
      [.gpr 1, .gpr 4, .gpr 15] [] [.rip] :=
    (movM64R64Effect_footprint 0x107d16 1 (.sib 4 (some 15) 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x107d16 0x4a (by decide) 1 (.sib 4 (some 15) 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x107d1e [0x4A, 0x89, 0x84, 0x3C, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x107d1e 8 (fun s => AddrMode.addr (.sib 4 (some 15) 0 (.d32 0xd0)) s (0x107d1e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107d1e 0 (.sib 4 (some 15) 0 (.d32 0xd0)))
      [.gpr 0, .gpr 4, .gpr 15] [] [.rip] :=
    (movM64R64Effect_footprint 0x107d1e 0 (.sib 4 (some 15) 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x107d1e 0x4a (by decide) 0 (.sib 4 (some 15) 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x107d26 [0x41, 0x80, 0xCF, 0x20] (fun s => s.RIP = 0x107d26) (orR8Imm8Effect 0x107d26 4 15 0x20)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (orR8Imm8Effect_footprint 0x107d26 4 15 0x20).toInstrSpec (or_r8_imm8_rex_effect_step 0x107d26 0x41 0xcf 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x107d2a [0x44, 0x88, 0xBC, 0x24, 0x0F, 0x01, 0x00, 0x00] (StorePre 0x107d2a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10f)) s (0x107d2a + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x107d2a 8 15 (.sib 4 none 0 (.d32 0x10f)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107d2a 8 15 (.sib 4 none 0 (.d32 0x10f))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107d2a 0x44 (by decide) 7 (.sib 4 none 0 (.d32 0x10f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cee) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cf6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107cfe) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d06) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d0e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d16) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d1e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d26) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d2a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d32) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 68) (jmp_rel8_effect_step 0x107d32 0x73 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l107ce6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107ce6 :=
  Rest.liftedBlock (rest_l107ce6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107ce6 x hx)

theorem rest_l107d34 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107d34 bytes_l107d34) (entryMap (live .l107d34))
      10 0x107d34 bytes_l107d34 b_l107d34 := by
  have f0 : InstrSpec 0x107d34 [0xBA, 0x40, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107d34) (movR32Imm32Effect 0x107d34 5 2 0x40)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x107d34 5 2 0x40).toInstrSpec (mov_r32_imm32_effect_step 0x107d34 0xba (by decide) 0x40) pre_rip
  have f1 : InstrSpec 0x107d39 [0x4C, 0x29, 0xFA] (fun s => s.RIP = 0x107d39) (subR64R64Effect 0x107d39 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x107d39 2 15).toInstrSpec (sub_r64_r64_effect_step 0x107d39 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x107d3c [0x4C, 0x8D, 0x2C, 0x14] (fun s => s.RIP = 0x107d3c) (leaR64Effect 0x107d3c 13 (.sib 4 (some 2) 0 .none))
      [.gpr 4, .gpr 2] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x107d3c 13 (.sib 4 (some 2) 0 .none)).toInstrSpec (lea_r64_effect_step 0x107d3c 0x4c (by decide) 5 (.sib 4 (some 2) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x107d40 [0x49, 0x81, 0xC5, 0xB0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107d40) (addR64Imm32Effect 0x107d40 13 0xb0)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x107d40 13 0xb0).toInstrSpec (add_r64_imm32_effect_step 0x107d40 0x49 0xc5 0xb0 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x107d47 [0x4A, 0x8D, 0x3C, 0x3C] (fun s => s.RIP = 0x107d47) (leaR64Effect 0x107d47 7 (.sib 4 (some 15) 0 .none))
      [.gpr 4, .gpr 15] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x107d47 7 (.sib 4 (some 15) 0 .none)).toInstrSpec (lea_r64_effect_step 0x107d47 0x4a (by decide) 7 (.sib 4 (some 15) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x107d4b [0x48, 0x81, 0xC7, 0xD0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107d4b) (addR64Imm32Effect 0x107d4b 7 0xd0)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x107d4b 7 0xd0).toInstrSpec (add_r64_imm32_effect_step 0x107d4b 0x48 0xc7 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x107d52 [0x49, 0x83, 0xC7, 0xE0] (fun s => s.RIP = 0x107d52) (addR64Imm8Effect 0x107d52 15 0xe0)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x107d52 15 0xe0).toInstrSpec (add_r64_imm8_effect_step 0x107d52 0x49 0xc7 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x107d56 [0x48, 0x8D, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107d56) (leaR64Effect 0x107d56 6 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x107d56 6 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (lea_r64_effect_step 0x107d56 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x107d5e [0x48, 0x8D, 0x2D, 0xBB, 0x2A, 0x02, 0x00] (fun s => s.RIP = 0x107d5e) (leaR64Effect 0x107d5e 5 (.rip 0x22abb))
      [] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x107d5e 5 (.rip 0x22abb)).toInstrSpec (lea_r64_effect_step 0x107d5e 0x48 (by decide) 5 (.rip 0x22abb) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x107d65 [0xFF, 0xD5] (GoesTo (CallPre 0x107d65 2 (fun s => (Operand.reg 5 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x107d67) 0x12a820) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x107d67)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x107d65 5 0x107d67).toInstrSpec (call_r64_effect_step 0x107d65 0xd5 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 5 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d39) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d3c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d40) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d47) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 55), (3, 3), (4, 4), (7, 61), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d4b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 55), (3, 3), (4, 4), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d52) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 55), (3, 3), (4, 4), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d56) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 55), (3, 3), (4, 4), (6, 67), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d5e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 69), (6, 67), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d65) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 55), (3, 3), (4, 71), (5, 69), (6, 67), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f9 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l107d34 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107d34 :=
  Rest.liftedBlock (rest_l107d34 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107d34 x hx)

theorem rest_l107d67 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107d67 bytes_l107d67) (entryMap (live .l107d67))
      6 0x107d67 bytes_l107d67 b_l107d67 := by
  have f0 : InstrSpec 0x107d67 [0x48, 0xFF, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00] (StorePre 0x107d67 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x107d67 + BitVec.ofNat 64 8)) 8) (incMEffect 0x107d67 8 64 (.sib 4 none 0 (.d32 0x130)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (incMEffect64_footprint 0x107d67 8 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (inc_m64_effect_step 0x107d67 0x48 (by decide) (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x107d6f [0x4C, 0x8D, 0xA4, 0x24, 0xD0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107d6f) (leaR64Effect 0x107d6f 12 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x107d6f 12 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (lea_r64_effect_step 0x107d6f 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x107d77 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107d77) (movR32Imm32Effect 0x107d77 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x107d77 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x107d77 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x107d7c [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x107d7c) (movR64R64Effect 0x107d7c 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107d7c 7 14).toInstrSpec (mov_r64_r64_effect_step 0x107d7c 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x107d7f [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x107d7f) (movR64R64Effect 0x107d7f 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x107d7f 6 12).toInstrSpec (mov_r64_r64_effect_step 0x107d7f 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x107d82 [0xE8, 0x59, 0x9B, 0x01, 0x00] (PushPre 0x107d82 5) (callEffect (fun _ => 0x1218e0) 0x107d87)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107d82 0x1218e0 0x107d87).toInstrSpec (call_rel32_effect_step 0x107d82 0x19b59 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d6f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 54), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d77) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 54), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d7c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (5, 5), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 54), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d7f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (5, 5), (6, 60), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 54), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d82) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 62), (5, 5), (6, 60), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 54), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 64) (by decide) (by decide) rfl rfl

theorem block_l107d67 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107d67 :=
  Rest.liftedBlock (rest_l107d67 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107d67 x hx)

theorem rest_l107d87 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107d87 bytes_l107d87) (entryMap (live .l107d87))
      7 0x107d87 bytes_l107d87 b_l107d87 := by
  have f0 : InstrSpec 0x107d87 [0x48, 0xBE, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x107d87) (movR64Imm64Effect 0x107d87 6 0x7fffffffffffffc0)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x107d87 6 0x7fffffffffffffc0).toInstrSpec (mov_r64_imm64_effect_step 0x107d87 0x48 0xbe (by decide) (by decide) 0x7fffffffffffffc0) pre_rip
  have f1 : InstrSpec 0x107d91 [0x4C, 0x21, 0xFE] (fun s => s.RIP = 0x107d91) (andR64R64Effect 0x107d91 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x107d91 6 15).toInstrSpec (and_r64_r64_effect_step 0x107d91 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x107d94 [0x4C, 0x01, 0xEE] (fun s => s.RIP = 0x107d94) (addR64R64Effect 0x107d94 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x107d94 6 13).toInstrSpec (add_r64_r64_effect_step 0x107d94 0x4c 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x107d97 [0x44, 0x88, 0xBC, 0x24, 0x0F, 0x01, 0x00, 0x00] (StorePre 0x107d97 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10f)) s (0x107d97 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x107d97 8 15 (.sib 4 none 0 (.d32 0x10f)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x107d97 8 15 (.sib 4 none 0 (.d32 0x10f))).toInstrSpec (mov_m8_r8_rex_effect_step 0x107d97 0x44 (by decide) 7 (.sib 4 none 0 (.d32 0x10f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x107d9f [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x107d9f) (movR64R64Effect 0x107d9f 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107d9f 7 12).toInstrSpec (mov_r64_r64_effect_step 0x107d9f 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x107da2 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x107da2) (movR64R64Effect 0x107da2 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x107da2 2 15).toInstrSpec (mov_r64_r64_effect_step 0x107da2 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x107da5 [0xFF, 0xD5] (GoesTo (CallPre 0x107da5 2 (fun s => (Operand.reg 5 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x107da7) 0x12a820) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x107da7)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x107da5 5 0x107da7).toInstrSpec (call_r64_effect_step 0x107da5 0xd5 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 5 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d91) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d94) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d97) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107d9f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107da2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 62), (3, 3), (4, 4), (5, 5), (6, 57), (7, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107da5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 62), (3, 3), (4, 64), (5, 5), (6, 57), (7, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f6 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l107d87 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107d87 :=
  Rest.liftedBlock (rest_l107d87 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107d87 x hx)

theorem rest_l107da7 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107da7 bytes_l107da7) (entryMap (live .l107da7))
      15 0x107da7 bytes_l107da7 b_l107da7 := by
  have f0 : InstrSpec 0x107da7 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x107da7) (leaR64Effect 0x107da7 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x107da7 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x107da7 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x107dac [0x48, 0x8D, 0xB4, 0x24, 0xD0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107dac) (leaR64Effect 0x107dac 6 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x107dac 6 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (lea_r64_effect_step 0x107dac 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x107db4 [0xB9, 0x0D, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107db4) (movR32Imm32Effect 0x107db4 5 1 0xd)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x107db4 5 1 0xd).toInstrSpec (mov_r32_imm32_effect_step 0x107db4 0xb9 (by decide) 0xd) pre_rip
  have f3 : InstrSpec 0x107db9 [0xF3, 0x48, 0xA5] (RepPre 0x107db9 (RepMovsqPre 0x107db9)) (repMovsqEffect 0x107db9)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x107db9).toInstrSpecOfRuns (rep_movsq_runs hstride 0x107db9 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x107dbc [0x4C, 0x8D, 0x74, 0x24, 0x48] (fun s => s.RIP = 0x107dbc) (leaR64Effect 0x107dbc 14 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x107dbc 14 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x107dbc 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x107dc1 [0x44, 0x0F, 0xB6, 0x64, 0x24, 0x47] (LoadPre 0x107dc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x107dc1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107dc1 6 12 (.sib 4 none 0 (.d8 0x47)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x107dc1 6 12 (.sib 4 none 0 (.d8 0x47))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x107dc1 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x47)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x107dc7 [0x4C, 0x8B, 0x6C, 0x24, 0x68] (LoadPre 0x107dc7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x107dc7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107dc7 13 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x107dc7 13 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x107dc7 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x107dcc [0x4D, 0x89, 0xE7] (fun s => s.RIP = 0x107dcc) (movR64R64Effect 0x107dcc 15 12)
      [.gpr 12] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x107dcc 15 12).toInstrSpec (mov_r64_r64_effect_step 0x107dcc 0x4d 0xe7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x107dcf [0x49, 0x83, 0xF7, 0x3F] (fun s => s.RIP = 0x107dcf) (xorR64Imm8Effect 0x107dcf 15 0x3f)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR64Imm8Effect_footprint 0x107dcf 15 0x3f).toInstrSpec (xor_r64_imm8_effect_step 0x107dcf 0x49 0xf7 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x107dd3 [0x42, 0xC6, 0x44, 0x24, 0x08, 0x80] (StorePre 0x107dd3 6 (fun s => AddrMode.addr (.sib 4 (some 12) 0 (.d8 0x8)) s (0x107dd3 + BitVec.ofNat 64 6)) 1) (movM8Imm8RexEffect 0x107dd3 (.sib 4 (some 12) 0 (.d8 0x8)) 0x80)
      [.gpr 4, .gpr 12] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x107dd3 (.sib 4 (some 12) 0 (.d8 0x8)) 0x80).toInstrSpec (mov_m8_imm8_rex_effect_step 0x107dd3 0x42 (by decide) (.sib 4 (some 12) 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x80) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x107dd9 [0x4A, 0x8D, 0x3C, 0x24] (fun s => s.RIP = 0x107dd9) (leaR64Effect 0x107dd9 7 (.sib 4 (some 12) 0 .none))
      [.gpr 4, .gpr 12] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x107dd9 7 (.sib 4 (some 12) 0 .none)).toInstrSpec (lea_r64_effect_step 0x107dd9 0x4a (by decide) 7 (.sib 4 (some 12) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x107ddd [0x48, 0x83, 0xC7, 0x09] (fun s => s.RIP = 0x107ddd) (addR64Imm8Effect 0x107ddd 7 0x9)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x107ddd 7 0x9).toInstrSpec (add_r64_imm8_effect_step 0x107ddd 0x48 0xc7 0x9 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x107de1 [0x31, 0xF6] (fun s => s.RIP = 0x107de1) (xorR32R32Effect 0x107de1 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x107de1 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x107de1 0xf6 (by decide)) pre_rip
  have f13 : InstrSpec 0x107de3 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x107de3) (movR64R64Effect 0x107de3 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x107de3 2 15).toInstrSpec (mov_r64_r64_effect_step 0x107de3 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x107de6 [0xFF, 0x15, 0x24, 0xC0, 0x0F, 0x00] (GoesTo (CallMemPre 0x107de6 (.rip 0xfc024)) (callEffect (callMemPtr 0x107de6 (.rip 0xfc024)) (0x107de6 + BitVec.ofNat 64 (callMemLen (.rip 0xfc024)))) 0x12a700) (callEffect (callMemPtr 0x107de6 (.rip 0xfc024)) (0x107de6 + BitVec.ofNat 64 (callMemLen (.rip 0xfc024))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x107de6 (.rip 0xfc024)).toInstrSpec (call_m64_effect_step 0x107de6 (.rip 0xfc024) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a700
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107db4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107db9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dbc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dc1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 63), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dc7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 63), (13, 65), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dcc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 63), (13, 65), (14, 61), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dcf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 63), (13, 65), (14, 61), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dd3) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 63), (13, 65), (14, 61), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dd9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 63), (13, 65), (14, 61), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ddd) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 59), (7, 74), (9, 9), (10, 10), (11, 11), (12, 63), (13, 65), (14, 61), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107de1) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 76), (7, 74), (9, 9), (10, 10), (11, 11), (12, 63), (13, 65), (14, 61), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107de3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(2, 78), (3, 3), (4, 4), (5, 5), (6, 76), (7, 74), (9, 9), (10, 10), (11, 11), (12, 63), (13, 65), (14, 61), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107de6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(2, 78), (3, 3), (4, 80), (5, 5), (6, 76), (7, 74), (9, 9), (10, 10), (11, 11), (12, 63), (13, 65), (14, 61), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a700) f14 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 82) (by decide) (by decide) rfl rfl

theorem block_l107da7 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107da7 :=
  Rest.liftedBlock (rest_l107da7 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107da7 x hx)

theorem rest_l107dec [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107dec bytes_l107dec) (entryMap (live .l107dec))
      2 0x107dec bytes_l107dec b_l107dec := by
  have f0 : InstrSpec 0x107dec [0x49, 0x83, 0xFF, 0x07] (fun s => s.RIP = 0x107dec) (cmpR64Imm8Effect 0x107dec 15 0x7)
      [.gpr 15] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x107dec 15 0x7).toInstrSpec (cmp_r64_imm8_effect_step 0x107dec 0x49 0xff 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107df0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x107df0 7 0xb3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l107dec [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107dec :=
  Rest.liftedBlock (rest_l107dec code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107dec x hx)

theorem rest_l107df6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107df6 bytes_l107df6) (entryMap (live .l107df6))
      20 0x107df6 bytes_l107df6 b_l107df6 := by
  have f0 : InstrSpec 0x107df6 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x107df6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107df6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107df6 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107df6 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x107df6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107dfb [0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x107dfb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x107dfb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107dfb 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107dfb 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x107dfb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x107e03 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x107e03 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107e03 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107e03 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107e03 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x107e03 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x107e08 [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x107e08 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x107e08 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107e08 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107e08 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x107e08 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x107e10 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x107e10 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107e10 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107e10 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107e10 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x107e10 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x107e15 [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x107e15 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x107e15 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107e15 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107e15 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x107e15 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x107e1d [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x107e1d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107e1d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107e1d 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107e1d 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x107e1d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x107e22 [0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x107e22 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107e22 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107e22 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107e22 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x107e22 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x107e2a [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x107e2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107e2a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107e2a 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107e2a 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x107e2a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x107e2f [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x107e2f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107e2f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107e2f 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107e2f 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x107e2f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x107e37 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x107e37 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107e37 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107e37 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107e37 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x107e37 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x107e3c [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x107e3c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107e3c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107e3c 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107e3c 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x107e3c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x107e44 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x107e44 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107e44 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107e44 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107e44 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x107e44 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x107e49 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x107e49 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107e49 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107e49 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x107e49 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x107e49 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x107e4e [0x48, 0x89, 0x4C, 0x24, 0x78] (StorePre 0x107e4e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107e4e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107e4e 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107e4e 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x107e4e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x107e53 [0x48, 0x89, 0x44, 0x24, 0x70] (StorePre 0x107e53 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x107e53 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107e53 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107e53 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x107e53 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x107e58 [0x48, 0x8D, 0x74, 0x24, 0x70] (fun s => s.RIP = 0x107e58) (leaR64Effect 0x107e58 6 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x107e58 6 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (lea_r64_effect_step 0x107e58 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x107e5d [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107e5d) (movR32Imm32Effect 0x107e5d 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x107e5d 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x107e5d 0xba (by decide) 0x1) pre_rip
  have f18 : InstrSpec 0x107e62 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x107e62) (movR64R64Effect 0x107e62 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107e62 7 14).toInstrSpec (mov_r64_r64_effect_step 0x107e62 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x107e65 [0xE8, 0x76, 0x9A, 0x01, 0x00] (PushPre 0x107e65 5) (callEffect (fun _ => 0x1218e0) 0x107e6a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107e65 0x1218e0 0x107e6a).toInstrSpec (call_rel32_effect_step 0x107e65 0x19a76 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107dfb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e03) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e08) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e10) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e15) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e1d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e22) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e2a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e2f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e37) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e3c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e44) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e49) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e4e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e53) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e58) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (6, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e5d) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 71), (1, 73), (2, 79), (3, 3), (4, 4), (5, 5), (6, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e62) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 71), (1, 73), (2, 79), (3, 3), (4, 4), (5, 5), (6, 77), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e65) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 71), (1, 73), (2, 79), (3, 3), (4, 83), (5, 5), (6, 77), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l107df6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107df6 :=
  Rest.liftedBlock (rest_l107df6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107df6 x hx)

theorem rest_l107e6a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107e6a bytes_l107e6a) (entryMap (live .l107e6a))
      7 0x107e6a bytes_l107e6a b_l107e6a := by
  have f0 : InstrSpec 0x107e6a [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107e6a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107e6a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107e6a (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107e6a (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107e6a 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x107e73 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107e73 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107e73 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107e73 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107e73 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107e73 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x107e7c [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107e7c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107e7c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107e7c (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107e7c (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107e7c 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x107e85 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107e85 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107e85 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107e85 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107e85 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107e85 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x107e8e [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107e8e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107e8e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107e8e (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107e8e (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107e8e 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x107e97 [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107e97 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107e97 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107e97 (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107e97 (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107e97 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x107ea0 [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x107ea0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107ea0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ea0 (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x107ea0 (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x107ea0 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e73) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e7c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e85) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e8e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107e97) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ea0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ea9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l107e6a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107e6a :=
  Rest.liftedBlock (rest_l107e6a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107e6a x hx)

theorem rest_l107ea9_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x107ea9 bytes_l107ea9) [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x107f19 bytes_l107ea9_1 b_l107ea9_1 := by
  have f20 : InstrSpec 0x107f19 [0x48, 0x8D, 0x74, 0x24, 0x70] (fun s => s.RIP = 0x107f19) (leaR64Effect 0x107f19 6 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x107f19 6 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (lea_r64_effect_step 0x107f19 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x107f1e [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107f1e) (movR32Imm32Effect 0x107f1e 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x107f1e 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x107f1e 0xba (by decide) 0x1) pre_rip
  have f22 : InstrSpec 0x107f23 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x107f23) (movR64R64Effect 0x107f23 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x107f23 7 14).toInstrSpec (mov_r64_r64_effect_step 0x107f23 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x107f26 [0xE8, 0xB5, 0x99, 0x01, 0x00] (PushPre 0x107f26 5) (callEffect (fun _ => 0x1218e0) 0x107f2b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107f26 0x1218e0 0x107f2b).toInstrSpec (call_rel32_effect_step 0x107f26 0x199b5 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (6, 84), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f1e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f21 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 78), (1, 80), (2, 86), (3, 3), (4, 4), (5, 5), (6, 84), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f23) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f22 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 78), (1, 80), (2, 86), (3, 3), (4, 4), (5, 5), (6, 84), (7, 88), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f26) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f23 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 78), (1, 80), (2, 86), (3, 3), (4, 90), (5, 5), (6, 84), (7, 88), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f23 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 92) (by decide) (by decide) rfl rfl

theorem rest_l107ea9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107ea9 bytes_l107ea9) (entryMap (live .l107ea9))
      24 0x107ea9 bytes_l107ea9 b_l107ea9 := by
  have f0 : InstrSpec 0x107ea9 [0x49, 0xC1, 0xE5, 0x09] (fun s => s.RIP = 0x107ea9) (shlR64Effect 0x107ea9 4 13 9)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shlR64Effect_footprint 0x107ea9 4 13 9).toInstrSpec (shl_r64_imm8_effect_step 0x107ea9 0x49 0xe5 0x9 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x107ead [0x41, 0xC1, 0xE4, 0x03] (fun s => s.RIP = 0x107ead) (shlR32Effect 0x107ead 4 12 3)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x107ead 4 12 3).toInstrSpec (shl_r32_imm8_rex_effect_step 0x107ead 0x41 0xe4 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x107eb1 [0x4D, 0x09, 0xEC] (fun s => s.RIP = 0x107eb1) (orR64R64Effect 0x107eb1 12 13)
      [.gpr 12, .gpr 13] [] [.reg 12, .flags, .rip] :=
    (orR64R64Effect_footprint 0x107eb1 12 13).toInstrSpec (or_r64_r64_effect_step 0x107eb1 0x4d 0xec (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x107eb4 [0x49, 0x0F, 0xCC] (fun s => s.RIP = 0x107eb4) (bswapR64Effect 0x107eb4 3 12)
      [.gpr 12] [] [.reg 12, .rip] :=
    (bswapR64Effect_footprint 0x107eb4 3 12).toInstrSpec (bswap_r64_effect_step 0x107eb4 0x49 (by decide) 0xcc (by decide)) pre_rip
  have f4 : InstrSpec 0x107eb7 [0x4C, 0x89, 0x64, 0x24, 0x40] (StorePre 0x107eb7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107eb7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107eb7 12 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107eb7 12 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x107eb7 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x107ebc [0x4C, 0x89, 0xA4, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x107ebc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x107ebc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107ebc 12 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107ebc 12 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x107ebc 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x107ec4 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x107ec4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107ec4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107ec4 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107ec4 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x107ec4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x107ec9 [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x107ec9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x107ec9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107ec9 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107ec9 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x107ec9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x107ed1 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x107ed1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107ed1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107ed1 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107ed1 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x107ed1 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x107ed6 [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x107ed6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x107ed6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107ed6 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107ed6 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x107ed6 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x107ede [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x107ede (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107ede + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107ede 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107ede 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x107ede 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x107ee3 [0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x107ee3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107ee3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107ee3 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107ee3 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x107ee3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x107eeb [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x107eeb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107eeb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107eeb 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107eeb 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x107eeb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x107ef0 [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x107ef0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107ef0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107ef0 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107ef0 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x107ef0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x107ef8 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x107ef8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107ef8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107ef8 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107ef8 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x107ef8 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x107efd [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x107efd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107efd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107efd 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107efd 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x107efd 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x107f05 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x107f05 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107f05 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f05 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x107f05 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x107f05 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x107f0a [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x107f0a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107f0a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f0a 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x107f0a 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x107f0a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x107f0f [0x48, 0x89, 0x4C, 0x24, 0x78] (StorePre 0x107f0f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107f0f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107f0f 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107f0f 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x107f0f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x107f14 [0x48, 0x89, 0x44, 0x24, 0x70] (StorePre 0x107f14 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x107f14 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107f14 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x107f14 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x107f14 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ead) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107eb1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107eb4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107eb7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ebc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ec4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ec9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ed1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ed6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ede) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ee3) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107eeb) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ef0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107ef8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107efd) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f05) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f0a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f0f) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f14) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f19) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107ea9_1 code

theorem block_l107ea9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107ea9 :=
  Rest.liftedBlock (rest_l107ea9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107ea9 x hx)

theorem rest_l107f2b_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x107f2b bytes_l107f2b) [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]
      12 0x107f6c bytes_l107f2b_1 b_l107f2b_1 := by
  have f20 : InstrSpec 0x107f6c [0x89, 0x7B, 0x10] (StorePre 0x107f6c 3 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x107f6c + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x107f6c 7 (.base 3 (.d8 0x10)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107f6c 7 (.base 3 (.d8 0x10))).toInstrSpec (mov_m32_r32_low_effect_step 0x107f6c 7 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x107f6f [0x44, 0x89, 0x43, 0x14] (StorePre 0x107f6f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x107f6f + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x107f6f 8 (.base 3 (.d8 0x14)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x107f6f 8 (.base 3 (.d8 0x14))).toInstrSpec (mov_m32_r32_effect_step 0x107f6f 0x44 (by decide) 0 (.base 3 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x107f73 [0x44, 0x89, 0x4B, 0x18] (StorePre 0x107f73 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x107f73 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x107f73 9 (.base 3 (.d8 0x18)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x107f73 9 (.base 3 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x107f73 0x44 (by decide) 1 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x107f77 [0x44, 0x89, 0x53, 0x1C] (StorePre 0x107f77 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x107f77 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x107f77 10 (.base 3 (.d8 0x1c)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x107f77 10 (.base 3 (.d8 0x1c))).toInstrSpec (mov_m32_r32_effect_step 0x107f77 0x44 (by decide) 2 (.base 3 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x107f7b [0x48, 0x81, 0xC4, 0x38, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x107f7b) (addR64Imm32Effect 0x107f7b 4 0x138)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x107f7b 4 0x138).toInstrSpec (add_r64_imm32_effect_step 0x107f7b 0x48 0xc4 0x138 (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x107f82 [0x5B] (PopPre 0x107f82) (popR64Effect 0x107f82 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x107f82 1 3).toInstrSpec (pop_r64_effect_step 0x107f82 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f26 : InstrSpec 0x107f83 [0x41, 0x5C] (PopPre 0x107f83) (popR64Effect 0x107f83 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x107f83 2 12).toInstrSpec (pop_r64_rex_effect_step 0x107f83 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f27 : InstrSpec 0x107f85 [0x41, 0x5D] (PopPre 0x107f85) (popR64Effect 0x107f85 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x107f85 2 13).toInstrSpec (pop_r64_rex_effect_step 0x107f85 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f28 : InstrSpec 0x107f87 [0x41, 0x5E] (PopPre 0x107f87) (popR64Effect 0x107f87 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x107f87 2 14).toInstrSpec (pop_r64_rex_effect_step 0x107f87 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f29 : InstrSpec 0x107f89 [0x41, 0x5F] (PopPre 0x107f89) (popR64Effect 0x107f89 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x107f89 2 15).toInstrSpec (pop_r64_rex_effect_step 0x107f89 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f30 : InstrSpec 0x107f8b [0x5D] (PopPre 0x107f8b) (popR64Effect 0x107f8b 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x107f8b 1 5).toInstrSpec (pop_r64_effect_step 0x107f8b 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f31 : InstrSpec 0x107f8c [0xC3] (RetPre 0x107f8c) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x107f8c).toInstrSpec (ret_effect_step 0x107f8c) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f6f) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f73) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f77) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f7b) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f24 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 93), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f82) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f25 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 96) f25 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 97) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 95), (4, 96), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f83) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f26 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 99) f26 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 100) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 95), (4, 99), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f85) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f27 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 102) f27 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 103) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 95), (4, 102), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 98), (13, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f87) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f28 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 105) f28 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 106) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 95), (4, 105), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 98), (13, 101), (14, 104), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f89) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f29 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 108) f29 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 109) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 95), (4, 108), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 98), (13, 101), (14, 104), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f8b) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f30 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 111) f30 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 112) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 95), (4, 111), (5, 110), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 98), (13, 101), (14, 104), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f8c) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f31 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 114) f31 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 115) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 95), (4, 114), (5, 110), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 98), (13, 101), (14, 104), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) f31 (by decide) rfl rfl rfl (by decide)

theorem rest_l107f2b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107f2b bytes_l107f2b) (entryMap (live .l107f2b))
      32 0x107f2b bytes_l107f2b b_l107f2b := by
  have f0 : InstrSpec 0x107f2b [0x8B, 0x44, 0x24, 0x48] (LoadPre 0x107f2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x107f2b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107f2b 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x107f2b 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r32_m32_low_effect_step 0x107f2b 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x107f2f [0x8B, 0x4C, 0x24, 0x4C] (LoadPre 0x107f2f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x107f2f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107f2f 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x107f2f 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_r32_m32_low_effect_step 0x107f2f 1 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x107f33 [0x0F, 0xC8] (fun s => s.RIP = 0x107f33) (bswapR32Effect 0x107f33 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR32Effect_footprint 0x107f33 2 0).toInstrSpec (bswap_r32_effect_step 0x107f33 0xc8 (by decide)) pre_rip
  have f3 : InstrSpec 0x107f35 [0x0F, 0xC9] (fun s => s.RIP = 0x107f35) (bswapR32Effect 0x107f35 2 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR32Effect_footprint 0x107f35 2 1).toInstrSpec (bswap_r32_effect_step 0x107f35 0xc9 (by decide)) pre_rip
  have f4 : InstrSpec 0x107f37 [0x8B, 0x54, 0x24, 0x50] (LoadPre 0x107f37 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x107f37 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107f37 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x107f37 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r32_m32_low_effect_step 0x107f37 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x107f3b [0x0F, 0xCA] (fun s => s.RIP = 0x107f3b) (bswapR32Effect 0x107f3b 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR32Effect_footprint 0x107f3b 2 2).toInstrSpec (bswap_r32_effect_step 0x107f3b 0xca (by decide)) pre_rip
  have f6 : InstrSpec 0x107f3d [0x8B, 0x74, 0x24, 0x54] (LoadPre 0x107f3d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x107f3d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107f3d 6 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x107f3d 6 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_r32_m32_low_effect_step 0x107f3d 6 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x107f41 [0x0F, 0xCE] (fun s => s.RIP = 0x107f41) (bswapR32Effect 0x107f41 2 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR32Effect_footprint 0x107f41 2 6).toInstrSpec (bswap_r32_effect_step 0x107f41 0xce (by decide)) pre_rip
  have f8 : InstrSpec 0x107f43 [0x8B, 0x7C, 0x24, 0x58] (LoadPre 0x107f43 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x107f43 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107f43 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x107f43 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r32_m32_low_effect_step 0x107f43 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x107f47 [0x0F, 0xCF] (fun s => s.RIP = 0x107f47) (bswapR32Effect 0x107f47 2 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (bswapR32Effect_footprint 0x107f47 2 7).toInstrSpec (bswap_r32_effect_step 0x107f47 0xcf (by decide)) pre_rip
  have f10 : InstrSpec 0x107f49 [0x44, 0x8B, 0x44, 0x24, 0x5C] (LoadPre 0x107f49 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x107f49 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x107f49 8 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x107f49 8 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_r32_m32_effect_step 0x107f49 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x107f4e [0x41, 0x0F, 0xC8] (fun s => s.RIP = 0x107f4e) (bswapR32Effect 0x107f4e 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (bswapR32Effect_footprint 0x107f4e 3 8).toInstrSpec (bswap_r32_rex_effect_step 0x107f4e 0x41 (by decide) 0xc8 (by decide)) pre_rip
  have f12 : InstrSpec 0x107f51 [0x44, 0x8B, 0x4C, 0x24, 0x60] (LoadPre 0x107f51 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x107f51 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x107f51 9 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x107f51 9 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r32_m32_effect_step 0x107f51 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x107f56 [0x41, 0x0F, 0xC9] (fun s => s.RIP = 0x107f56) (bswapR32Effect 0x107f56 3 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (bswapR32Effect_footprint 0x107f56 3 9).toInstrSpec (bswap_r32_rex_effect_step 0x107f56 0x41 (by decide) 0xc9 (by decide)) pre_rip
  have f14 : InstrSpec 0x107f59 [0x44, 0x8B, 0x54, 0x24, 0x64] (LoadPre 0x107f59 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x107f59 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x107f59 10 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x107f59 10 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_r32_m32_effect_step 0x107f59 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x107f5e [0x41, 0x0F, 0xCA] (fun s => s.RIP = 0x107f5e) (bswapR32Effect 0x107f5e 3 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (bswapR32Effect_footprint 0x107f5e 3 10).toInstrSpec (bswap_r32_rex_effect_step 0x107f5e 0x41 (by decide) 0xca (by decide)) pre_rip
  have f16 : InstrSpec 0x107f61 [0x89, 0x03] (StorePre 0x107f61 2 (fun s => AddrMode.addr (.base 3 .none) s (0x107f61 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x107f61 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107f61 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x107f61 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x107f63 [0x89, 0x4B, 0x04] (StorePre 0x107f63 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x107f63 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x107f63 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107f63 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x107f63 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x107f66 [0x89, 0x53, 0x08] (StorePre 0x107f66 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x107f66 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x107f66 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107f66 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x107f66 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x107f69 [0x89, 0x73, 0x0C] (StorePre 0x107f69 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x107f69 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x107f69 6 (.base 3 (.d8 0xc)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x107f69 6 (.base 3 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x107f69 6 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f2f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f33) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (3, 3), (4, 4), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f35) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f37) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f3b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f3d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f41) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f43) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 69), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f47) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f49) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (8, 73), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f4e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (8, 75), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f51) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (8, 75), (9, 77), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f56) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (8, 75), (9, 79), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f59) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (8, 75), (9, 79), (10, 81), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f5e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f61) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f63) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f66) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f69) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107f6c) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l107f2b_1 code

theorem block_l107f2b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107f2b :=
  Rest.liftedBlock (rest_l107f2b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107f2b x hx)

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

theorem_by block_l107a50_eval :
    program.runBlock (dialect code) ⟨.l107a50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107adb_eval :
    program.runBlock (dialect code) ⟨.l107adb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107b27_eval :
    program.runBlock (dialect code) ⟨.l107b27, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107b31_eval :
    program.runBlock (dialect code) ⟨.l107b31, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107ba5_eval :
    program.runBlock (dialect code) ⟨.l107ba5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107be4_eval :
    program.runBlock (dialect code) ⟨.l107be4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107c66_eval :
    program.runBlock (dialect code) ⟨.l107c66, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107ce6_eval :
    program.runBlock (dialect code) ⟨.l107ce6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107d34_eval :
    program.runBlock (dialect code) ⟨.l107d34, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107d67_eval :
    program.runBlock (dialect code) ⟨.l107d67, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107d87_eval :
    program.runBlock (dialect code) ⟨.l107d87, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107da7_eval :
    program.runBlock (dialect code) ⟨.l107da7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107dec_eval :
    program.runBlock (dialect code) ⟨.l107dec, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107df6_eval :
    program.runBlock (dialect code) ⟨.l107df6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107e6a_eval :
    program.runBlock (dialect code) ⟨.l107e6a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107ea9_eval :
    program.runBlock (dialect code) ⟨.l107ea9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107f2b_eval :
    program.runBlock (dialect code) ⟨.l107f2b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
