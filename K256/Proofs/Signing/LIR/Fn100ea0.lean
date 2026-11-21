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

theorem rest_l100ea0_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x100ea0 bytes_l100ea0) [(0, 67), (1, 80), (2, 84), (3, 3), (4, 65), (5, 5), (6, 6), (7, 72), (8, 8), (9, 9), (10, 90), (11, 69), (12, 12), (13, 86), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]
      9 0x100ee4 bytes_l100ea0_1 b_l100ea0_1 := by
  have f20 : InstrSpec 0x100ee4 [0x48, 0x8B, 0x6F, 0x18] (LoadPre 0x100ee4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x100ee4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100ee4 5 (.base 7 (.d8 0x18)))
      [.gpr 7] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x100ee4 5 (.base 7 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x100ee4 0x48 (by decide) 5 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x100ee8 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x100ee8) (movR64R64Effect 0x100ee8 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x100ee8 7 5).toInstrSpec (mov_r64_r64_effect_step 0x100ee8 0x48 0xef (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x100eeb [0x48, 0x0F, 0xCF] (fun s => s.RIP = 0x100eeb) (bswapR64Effect 0x100eeb 3 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (bswapR64Effect_footprint 0x100eeb 3 7).toInstrSpec (bswap_r64_effect_step 0x100eeb 0x48 (by decide) 0xcf (by decide)) pre_rip
  have f23 : InstrSpec 0x100eee [0x48, 0x89, 0xBC, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x100eee 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x100eee + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100eee 7 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100eee 7 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x100eee 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x100ef6 [0x4C, 0x89, 0x94, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x100ef6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x100ef6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100ef6 10 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100ef6 10 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x100ef6 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x100efe [0x48, 0x89, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x100efe 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x100efe + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100efe 2 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100efe 2 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x100efe 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x100f06 [0x48, 0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x100f06 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x100f06 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f06 1 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f06 1 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x100f06 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x100f0e [0x49, 0x83, 0xFB, 0x20] (fun s => s.RIP = 0x100f0e) (cmpR64Imm8Effect 0x100f0e 11 0x20)
      [.gpr 11] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100f0e 11 0x20).toInstrSpec (cmp_r64_imm8_effect_step 0x100f0e 0x49 0xfb 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 67), (1, 80), (2, 84), (3, 3), (4, 65), (5, 92), (6, 6), (7, 72), (8, 8), (9, 9), (10, 90), (11, 69), (12, 12), (13, 86), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ee8) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f21 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 67), (1, 80), (2, 84), (3, 3), (4, 65), (5, 92), (6, 6), (7, 94), (8, 8), (9, 9), (10, 90), (11, 69), (12, 12), (13, 86), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100eeb) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f22 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 67), (1, 80), (2, 84), (3, 3), (4, 65), (5, 92), (6, 6), (7, 96), (8, 8), (9, 9), (10, 90), (11, 69), (12, 12), (13, 86), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100eee) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 67), (1, 80), (2, 84), (3, 3), (4, 65), (5, 92), (6, 6), (7, 96), (8, 8), (9, 9), (10, 90), (11, 69), (12, 12), (13, 86), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ef6) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 67), (1, 80), (2, 84), (3, 3), (4, 65), (5, 92), (6, 6), (7, 96), (8, 8), (9, 9), (10, 90), (11, 69), (12, 12), (13, 86), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100efe) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 67), (1, 80), (2, 84), (3, 3), (4, 65), (5, 92), (6, 6), (7, 96), (8, 8), (9, 9), (10, 90), (11, 69), (12, 12), (13, 86), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f06) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 67), (1, 80), (2, 84), (3, 3), (4, 65), (5, 92), (6, 6), (7, 96), (8, 8), (9, 9), (10, 90), (11, 69), (12, 12), (13, 86), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f0e) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f27 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 103) f27 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 104) (ρ' := [(0, 67), (1, 80), (2, 84), (3, 3), (4, 65), (5, 92), (6, 6), (7, 96), (8, 8), (9, 9), (10, 90), (11, 69), (12, 12), (13, 86), (14, 76), (15, 74), (16, 102), (19, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f12) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 105) (jcc_rel32_effect_step 0x100f12 7 0x472) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l100ea0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100ea0 bytes_l100ea0) (entryMap (live .l100ea0))
      29 0x100ea0 bytes_l100ea0 b_l100ea0 := by
  have f0 : InstrSpec 0x100ea0 [0x55] (PushPre 0x100ea0 1) (pushR64Effect 0x100ea0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100ea0 1 5).toInstrSpec (push_r64_effect_step 0x100ea0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x100ea1 [0x41, 0x57] (PushPre 0x100ea1 2) (pushR64Effect 0x100ea1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100ea1 2 15).toInstrSpec (push_r64_rex_effect_step 0x100ea1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x100ea3 [0x41, 0x56] (PushPre 0x100ea3 2) (pushR64Effect 0x100ea3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100ea3 2 14).toInstrSpec (push_r64_rex_effect_step 0x100ea3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x100ea5 [0x41, 0x55] (PushPre 0x100ea5 2) (pushR64Effect 0x100ea5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100ea5 2 13).toInstrSpec (push_r64_rex_effect_step 0x100ea5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x100ea7 [0x41, 0x54] (PushPre 0x100ea7 2) (pushR64Effect 0x100ea7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100ea7 2 12).toInstrSpec (push_r64_rex_effect_step 0x100ea7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x100ea9 [0x53] (PushPre 0x100ea9 1) (pushR64Effect 0x100ea9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100ea9 1 3).toInstrSpec (push_r64_effect_step 0x100ea9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x100eaa [0x48, 0x81, 0xEC, 0xE8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100eaa) (subR64Imm32Effect 0x100eaa 4 0xe8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x100eaa 4 0xe8).toInstrSpec (sub_r64_imm32_effect_step 0x100eaa 0x48 0xec 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100eb1 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x100eb1) (movR64R64Effect 0x100eb1 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100eb1 0 1).toInstrSpec (mov_r64_r64_effect_step 0x100eb1 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100eb4 [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x100eb4) (movR64R64Effect 0x100eb4 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x100eb4 11 2).toInstrSpec (mov_r64_r64_effect_step 0x100eb4 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100eb7 [0x48, 0x89, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x100eb7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x100eb7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100eb7 7 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100eb7 7 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x100eb7 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x100ebf [0x48, 0x8B, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00] (LoadPre 0x100ebf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x100ebf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100ebf 7 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x100ebf 7 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_r64_m64_effect_step 0x100ebf 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x100ec7 [0x4C, 0x8B, 0x3F] (LoadPre 0x100ec7 (fun s => AddrMode.addr (.base 7 .none) s (0x100ec7 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100ec7 15 (.base 7 .none))
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x100ec7 15 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x100ec7 0x4c (by decide) 7 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x100eca [0x4C, 0x8B, 0x77, 0x08] (LoadPre 0x100eca (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x100eca + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100eca 14 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x100eca 14 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x100eca 0x4c (by decide) 6 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x100ece [0x4C, 0x89, 0xF9] (fun s => s.RIP = 0x100ece) (movR64R64Effect 0x100ece 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x100ece 1 15).toInstrSpec (mov_r64_r64_effect_step 0x100ece 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x100ed1 [0x48, 0x0F, 0xC9] (fun s => s.RIP = 0x100ed1) (bswapR64Effect 0x100ed1 3 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR64Effect_footprint 0x100ed1 3 1).toInstrSpec (bswap_r64_effect_step 0x100ed1 0x48 (by decide) 0xc9 (by decide)) pre_rip
  have f15 : InstrSpec 0x100ed4 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x100ed4) (movR64R64Effect 0x100ed4 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x100ed4 2 14).toInstrSpec (mov_r64_r64_effect_step 0x100ed4 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x100ed7 [0x48, 0x0F, 0xCA] (fun s => s.RIP = 0x100ed7) (bswapR64Effect 0x100ed7 3 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR64Effect_footprint 0x100ed7 3 2).toInstrSpec (bswap_r64_effect_step 0x100ed7 0x48 (by decide) 0xca (by decide)) pre_rip
  have f17 : InstrSpec 0x100eda [0x4C, 0x8B, 0x6F, 0x10] (LoadPre 0x100eda (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x100eda + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100eda 13 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x100eda 13 (.base 7 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x100eda 0x4c (by decide) 5 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x100ede [0x4D, 0x89, 0xEA] (fun s => s.RIP = 0x100ede) (movR64R64Effect 0x100ede 10 13)
      [.gpr 13] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x100ede 10 13).toInstrSpec (mov_r64_r64_effect_step 0x100ede 0x4d 0xea (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x100ee1 [0x49, 0x0F, 0xCA] (fun s => s.RIP = 0x100ee1) (bswapR64Effect 0x100ee1 3 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (bswapR64Effect_footprint 0x100ee1 3 10).toInstrSpec (bswap_r64_effect_step 0x100ee1 0x49 (by decide) 0xca (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ea1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ea3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ea5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ea7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ea9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100eaa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100eb1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100eb4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 69), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100eb7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 69), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ebf) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 72), (8, 8), (9, 9), (11, 69), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ec7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 72), (8, 8), (9, 9), (11, 69), (12, 12), (13, 13), (14, 14), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100eca) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 72), (8, 8), (9, 9), (11, 69), (12, 12), (13, 13), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ece) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 67), (1, 78), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 72), (8, 8), (9, 9), (11, 69), (12, 12), (13, 13), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ed1) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 67), (1, 80), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 72), (8, 8), (9, 9), (11, 69), (12, 12), (13, 13), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ed4) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 67), (1, 80), (2, 82), (3, 3), (4, 65), (5, 5), (6, 6), (7, 72), (8, 8), (9, 9), (11, 69), (12, 12), (13, 13), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ed7) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 67), (1, 80), (2, 84), (3, 3), (4, 65), (5, 5), (6, 6), (7, 72), (8, 8), (9, 9), (11, 69), (12, 12), (13, 13), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100eda) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 67), (1, 80), (2, 84), (3, 3), (4, 65), (5, 5), (6, 6), (7, 72), (8, 8), (9, 9), (11, 69), (12, 12), (13, 86), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ede) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 67), (1, 80), (2, 84), (3, 3), (4, 65), (5, 5), (6, 6), (7, 72), (8, 8), (9, 9), (10, 88), (11, 69), (12, 12), (13, 86), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ee1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 67), (1, 80), (2, 84), (3, 3), (4, 65), (5, 5), (6, 6), (7, 72), (8, 8), (9, 9), (10, 90), (11, 69), (12, 12), (13, 86), (14, 76), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ee4) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100ea0_1 code

theorem block_l100ea0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100ea0 :=
  Rest.liftedBlock (rest_l100ea0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100ea0 x hx)

theorem rest_l100f18_1 [Bindings] (code : CodeMap) :
    Rest (n := 87) code lifted (codeRange 0x100f18 bytes_l100f18) [(0, 0), (1, 69), (2, 78), (3, 62), (4, 4), (5, 82), (6, 56), (7, 85), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x100f6b bytes_l100f18_1 b_l100f18_1 := by
  have f20 : InstrSpec 0x100f6b [0x48, 0xC1, 0xEF, 0x20] (fun s => s.RIP = 0x100f6b) (shrR64Effect 0x100f6b 4 7 32)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x100f6b 4 7 32).toInstrSpec (shr_r64_imm8_effect_step 0x100f6b 0x48 0xef 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 87) (RestInside.fresh (n := 87) f20 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x100f6b 4 7 32 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 69), (2, 78), (3, 62), (4, 4), (5, 82), (6, 56), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f6f) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 89) (jcc_rel32_effect_step 0x100f6f 5 0x42b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l100f18 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100f18 bytes_l100f18) (entryMap (live .l100f18))
      22 0x100f18 bytes_l100f18 b_l100f18 := by
  have f0 : InstrSpec 0x100f18 [0x48, 0x89, 0xB4, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x100f18 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x100f18 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f18 6 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f18 6 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x100f18 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x100f20 [0xC6, 0x44, 0x24, 0x08, 0x01] (StorePre 0x100f20 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f20 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x100f20 (.sib 4 none 0 (.d8 0x8)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x100f20 (.sib 4 none 0 (.d8 0x8)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x100f20 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x100f25 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x100f25) (leaR64Effect 0x100f25 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x100f25 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x100f25 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100f2a [0x0F, 0xB6, 0x74, 0x24, 0x08] (LoadPre 0x100f2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f2a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100f2a 5 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x100f2a 5 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x100f2a 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x100f2f [0x48, 0x89, 0xE9] (fun s => s.RIP = 0x100f2f) (movR64R64Effect 0x100f2f 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x100f2f 1 5).toInstrSpec (mov_r64_r64_effect_step 0x100f2f 0x48 0xe9 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x100f32 [0x31, 0xED] (fun s => s.RIP = 0x100f32) (xorR32R32Effect 0x100f32 2 5 5)
      [.gpr 5, .gpr 5] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100f32 2 5 5).toInstrSpec (xor_r32_r32_effect_step 0x100f32 0xed (by decide)) pre_rip
  have f6 : InstrSpec 0x100f34 [0x48, 0x89, 0xCB] (fun s => s.RIP = 0x100f34) (movR64R64Effect 0x100f34 3 1)
      [.gpr 1] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x100f34 3 1).toInstrSpec (mov_r64_r64_effect_step 0x100f34 0x48 0xcb (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100f37 [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x100f37) (testR64R64Effect 0x100f37 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100f37 1 1).toInstrSpec (test_r64_r64_effect_step 0x100f37 0x48 0xc9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100f3a [0x40, 0x0F, 0x94, 0xC5] (fun s => s.RIP = 0x100f3a) (atFlags (condHolds 4) (setccR8Effect 0x100f3a 4 5))
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 5, .rip] :=
    (setccR8Effect_footprint 0x100f3a 4 5 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x100f3a 4 0x40 (by decide) 0xc5 (by decide) c)) pre_rip
  have f9 : InstrSpec 0x100f3e [0x0F, 0x94, 0x44, 0x24, 0x08] (StorePre 0x100f3e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f3e + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x100f3e 5 (.sib 4 none 0 (.d8 0x8))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x100f3e 5 (.sib 4 none 0 (.d8 0x8)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x100f3e 4 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x100f43 [0x0F, 0xB6, 0x4C, 0x24, 0x08] (LoadPre 0x100f43 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f43 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100f43 5 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x100f43 5 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x100f43 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x100f48 [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x100f48) (xorR32R32Effect 0x100f48 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100f48 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x100f48 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x100f4b [0x4D, 0x85, 0xED] (fun s => s.RIP = 0x100f4b) (testR64R64Effect 0x100f4b 13 13)
      [.gpr 13, .gpr 13] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100f4b 13 13).toInstrSpec (test_r64_r64_effect_step 0x100f4b 0x4d 0xed (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x100f4e [0x41, 0x0F, 0x45, 0xEA] (fun s => s.RIP = 0x100f4e) (atFlags (condHolds 5) (cmovR32R32Effect 0x100f4e 4 5 10))
      [.gpr 5, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 5, .rip] :=
    (cmovR32R32Effect_footprint 0x100f4e 4 5 10 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_rex_effect_step 0x100f4e 5 0x41 (by decide) 0xea (by decide) c)) pre_rip
  have f14 : InstrSpec 0x100f52 [0x40, 0x88, 0x6C, 0x24, 0x08] (StorePre 0x100f52 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f52 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x100f52 5 5 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x100f52 5 5 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x100f52 0x40 (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x100f57 [0x0F, 0xB6, 0x54, 0x24, 0x08] (LoadPre 0x100f57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f57 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100f57 5 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x100f57 5 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x100f57 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x100f5c [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x100f5c) (testR64R64Effect 0x100f5c 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100f5c 14 14).toInstrSpec (test_r64_r64_effect_step 0x100f5c 0x4d 0xf6 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x100f5f [0x41, 0x0F, 0x45, 0xEA] (fun s => s.RIP = 0x100f5f) (atFlags (condHolds 5) (cmovR32R32Effect 0x100f5f 4 5 10))
      [.gpr 5, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 5, .rip] :=
    (cmovR32R32Effect_footprint 0x100f5f 4 5 10 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_rex_effect_step 0x100f5f 5 0x41 (by decide) 0xea (by decide) c)) pre_rip
  have f18 : InstrSpec 0x100f63 [0x40, 0x88, 0x6C, 0x24, 0x08] (StorePre 0x100f63 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f63 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x100f63 5 5 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x100f63 5 5 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x100f63 0x40 (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x100f68 [0x4C, 0x89, 0xC7] (fun s => s.RIP = 0x100f68) (movR64R64Effect 0x100f68 7 8)
      [.gpr 8] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x100f68 7 8).toInstrSpec (mov_r64_r64_effect_step 0x100f68 0x4c 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f20) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f25) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f2a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (4, 4), (5, 5), (6, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f2f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 58), (4, 4), (5, 5), (6, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f32) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 58), (4, 4), (5, 60), (6, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f34) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 58), (3, 62), (4, 4), (5, 60), (6, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f37) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 58), (3, 62), (4, 4), (5, 60), (6, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f3a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 58), (3, 62), (4, 4), (5, 66), (6, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f3e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 58), (3, 62), (4, 4), (5, 66), (6, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f43) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (3, 62), (4, 4), (5, 66), (6, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f48) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 69), (3, 62), (4, 4), (5, 66), (6, 56), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f4b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 69), (3, 62), (4, 4), (5, 66), (6, 56), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f4e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 69), (3, 62), (4, 4), (5, 75), (6, 56), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f52) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 69), (3, 62), (4, 4), (5, 75), (6, 56), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f57) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 69), (2, 78), (3, 62), (4, 4), (5, 75), (6, 56), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f5c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 69), (2, 78), (3, 62), (4, 4), (5, 75), (6, 56), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f5f) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f17 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 69), (2, 78), (3, 62), (4, 4), (5, 82), (6, 56), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f63) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 69), (2, 78), (3, 62), (4, 4), (5, 82), (6, 56), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f68) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f19 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 69), (2, 78), (3, 62), (4, 4), (5, 82), (6, 56), (7, 85), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f6b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100f18_1 code

theorem block_l100f18 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100f18 :=
  Rest.liftedBlock (rest_l100f18 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100f18 x hx)

theorem rest_l100f75 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100f75 bytes_l100f75) (entryMap (live .l100f75))
      2 0x100f75 bytes_l100f75 b_l100f75 := by
  have f0 : InstrSpec 0x100f75 [0x49, 0x81, 0xF8, 0xFF, 0xFF, 0xFF, 0x1F] (fun s => s.RIP = 0x100f75) (cmpR64Imm32Effect 0x100f75 8 0x1fffffff)
      [.gpr 8] [] [.flags, .rip] :=
    (cmpR64Imm32Effect_footprint 0x100f75 8 0x1fffffff).toInstrSpec (cmp_r64_imm32_effect_step 0x100f75 0x49 0xf8 0x1fffffff (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f7c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x100f7c 7 0x41e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100f75 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100f75 :=
  Rest.liftedBlock (rest_l100f75 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100f75 x hx)

theorem rest_l100f82_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x100f82 bytes_l100f82) [(0, 0), (1, 76), (2, 86), (3, 3), (4, 4), (6, 82), (7, 90), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      16 0x100fce bytes_l100f82_1 b_l100f82_1 := by
  have f20 : InstrSpec 0x100fce [0x0F, 0xB6, 0x74, 0x24, 0x08] (LoadPre 0x100fce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100fce + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100fce 5 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x100fce 5 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x100fce 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x100fd3 [0xF7, 0xDE] (fun s => s.RIP = 0x100fd3) (negR32Effect 0x100fd3 2 6)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (negR32Effect_footprint 0x100fd3 2 6).toInstrSpec (neg_r32_effect_step 0x100fd3 0xde (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x100fd5 [0x21, 0xFE] (fun s => s.RIP = 0x100fd5) (andR32R32Effect 0x100fd5 2 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100fd5 2 6 7).toInstrSpec (and_r32_r32_effect_step 0x100fd5 0xfe (by decide)) pre_rip
  have f23 : InstrSpec 0x100fd7 [0x01, 0xD6] (fun s => s.RIP = 0x100fd7) (addR32R32Effect 0x100fd7 2 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100fd7 2 6 2).toInstrSpec (add_r32_r32_effect_step 0x100fd7 0xd6 (by decide)) pre_rip
  have f24 : InstrSpec 0x100fd9 [0x01, 0xCE] (fun s => s.RIP = 0x100fd9) (addR32R32Effect 0x100fd9 2 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100fd9 2 6 1).toInstrSpec (add_r32_r32_effect_step 0x100fd9 0xce (by decide)) pre_rip
  have f25 : InstrSpec 0x100fdb [0xB9, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x100fdb) (movR32Imm32Effect 0x100fdb 5 1 0x100)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x100fdb 5 1 0x100).toInstrSpec (mov_r32_imm32_effect_step 0x100fdb 0xb9 (by decide) 0x100) pre_rip
  have f26 : InstrSpec 0x100fe0 [0x29, 0xF1] (fun s => s.RIP = 0x100fe0) (subR32R32Effect 0x100fe0 2 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (subR32R32Effect_footprint 0x100fe0 2 1 6).toInstrSpec (sub_r32_r32_effect_step 0x100fe0 0xf1 (by decide)) pre_rip
  have f27 : InstrSpec 0x100fe2 [0x46, 0x8D, 0x0C, 0xC5, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100fe2) (leaR32Effect 0x100fe2 8 9 (.abs (some 8) 3 0x0))
      [.gpr 8] [] [.reg 9, .rip] :=
    (leaR32Effect_footprint 0x100fe2 8 9 (.abs (some 8) 3 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x100fe2 0x46 (by decide) 1 (.abs (some 8) 3 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x100fea [0x31, 0xD2] (fun s => s.RIP = 0x100fea) (xorR32R32Effect 0x100fea 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100fea 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x100fea 0xd2 (by decide)) pre_rip
  have f29 : InstrSpec 0x100fec [0x44, 0x89, 0xCD] (fun s => s.RIP = 0x100fec) (movR32R32Effect 0x100fec 3 5 9)
      [.gpr 9] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x100fec 3 5 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x100fec 0x44 0xcd (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x100fef [0x29, 0xCD] (fun s => s.RIP = 0x100fef) (subR32R32Effect 0x100fef 2 5 1)
      [.gpr 5, .gpr 1] [] [.reg 5, .flags, .rip] :=
    (subR32R32Effect_footprint 0x100fef 2 5 1).toInstrSpec (sub_r32_r32_effect_step 0x100fef 0xcd (by decide)) pre_rip
  have f31 : InstrSpec 0x100ff1 [0x0F, 0x42, 0xEA] (fun s => s.RIP = 0x100ff1) (atFlags (condHolds 2) (cmovR32R32Effect 0x100ff1 3 5 2))
      [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .rip] :=
    (cmovR32R32Effect_footprint 0x100ff1 3 5 2 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x100ff1 2 0xea (by decide) c)) pre_rip
  have f32 : InstrSpec 0x100ff4 [0x89, 0xEA] (fun s => s.RIP = 0x100ff4) (movR32R32Effect 0x100ff4 2 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x100ff4 2 2 5).toInstrSpec (mov_r32_r32_effect_step 0x100ff4 0xea (by decide)) pre_rip
  have f33 : InstrSpec 0x100ff6 [0xC1, 0xEA, 0x03] (fun s => s.RIP = 0x100ff6) (shrR32Effect 0x100ff6 3 2 3)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x100ff6 3 2 3).toInstrSpec (shr_r32_imm8_effect_step 0x100ff6 0xea 0x3 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x100ff9 [0x4C, 0x89, 0x9C, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x100ff9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x100ff9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100ff9 11 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100ff9 11 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x100ff9 0x4c (by decide) 3 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 0), (1, 76), (2, 86), (3, 3), (4, 4), (6, 92), (7, 90), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fd3) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 0), (1, 76), (2, 86), (3, 3), (4, 4), (6, 94), (7, 90), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fd5) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f22 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 0), (1, 76), (2, 86), (3, 3), (4, 4), (6, 96), (7, 90), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fd7) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 0), (1, 76), (2, 86), (3, 3), (4, 4), (6, 98), (7, 90), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fd9) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f24 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 0), (1, 76), (2, 86), (3, 3), (4, 4), (6, 100), (7, 90), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fdb) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f25 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 0), (1, 102), (2, 86), (3, 3), (4, 4), (6, 100), (7, 90), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fe0) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 0), (1, 104), (2, 86), (3, 3), (4, 4), (6, 100), (7, 90), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fe2) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f27 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 0), (1, 104), (2, 86), (3, 3), (4, 4), (6, 100), (7, 90), (8, 8), (9, 106), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fea) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 0), (1, 104), (2, 108), (3, 3), (4, 4), (6, 100), (7, 90), (8, 8), (9, 106), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fec) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f29 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 0), (1, 104), (2, 108), (3, 3), (4, 4), (5, 110), (6, 100), (7, 90), (8, 8), (9, 106), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fef) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f30 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 113) f30 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 114) (ρ' := [(0, 0), (1, 104), (2, 108), (3, 3), (4, 4), (5, 112), (6, 100), (7, 90), (8, 8), (9, 106), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ff1) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 0), (1, 104), (2, 108), (3, 3), (4, 4), (5, 115), (6, 100), (7, 90), (8, 8), (9, 106), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ff4) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 0), (1, 104), (2, 117), (3, 3), (4, 4), (5, 115), (6, 100), (7, 90), (8, 8), (9, 106), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ff6) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 120) f33 .ZF (fun _ => rfl) (shrR32Effect_fresh 0x100ff6 3 2 3 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 121) (ρ' := [(0, 0), (1, 104), (2, 119), (3, 3), (4, 4), (5, 115), (6, 100), (7, 90), (8, 8), (9, 106), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 120), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ff9) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.exec (n := 122) (ρ' := [(0, 0), (1, 104), (2, 119), (3, 3), (4, 4), (5, 115), (6, 100), (7, 90), (8, 8), (9, 106), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 120), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101001) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 123) (jcc_rel8_effect_step 0x101001 4 0x20) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l100f82 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100f82 bytes_l100f82) (entryMap (live .l100f82))
      36 0x100f82 bytes_l100f82 b_l100f82 := by
  have f0 : InstrSpec 0x100f82 [0x4C, 0x89, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x100f82 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x100f82 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f82 9 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f82 9 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x100f82 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x100f8a [0xBF, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100f8a) (movR32Imm32Effect 0x100f8a 5 7 0x7f)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x100f8a 5 7 0x7f).toInstrSpec (mov_r32_imm32_effect_step 0x100f8a 0xbf (by decide) 0x7f) pre_rip
  have f2 : InstrSpec 0x100f8f [0x41, 0xB9, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100f8f) (movR32Imm32Effect 0x100f8f 6 9 0x7f)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x100f8f 6 9 0x7f).toInstrSpec (mov_r32_imm32_rex_effect_step 0x100f8f 0x41 0xb9 (by decide) (by decide) 0x7f) pre_rip
  have f3 : InstrSpec 0x100f95 [0x4C, 0x0F, 0xBD, 0xCB] (fun s => s.RIP = 0x100f95) (bsrR64R64Effect 0x100f95 4 9 3)
      [.gpr 9, .gpr 3] [] [.reg 9, .flags, .rip] :=
    (bsrR64R64Effect_footprint 0x100f95 4 9 3).toInstrSpec (bsr_r64_r64_effect_step 0x100f95 0x4c (by decide) 0xcb (by decide)) pre_rip
  have f4 : InstrSpec 0x100f99 [0x41, 0x83, 0xF1, 0x3F] (fun s => s.RIP = 0x100f99) (xorR32Imm8Effect 0x100f99 4 9 0x3f)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x100f99 4 9 0x3f).toInstrSpec (xor_r32_imm8_rex_effect_step 0x100f99 0x41 0xf1 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x100f9d [0xF7, 0xDE] (fun s => s.RIP = 0x100f9d) (negR32Effect 0x100f9d 2 6)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (negR32Effect_footprint 0x100f9d 2 6).toInstrSpec (neg_r32_effect_step 0x100f9d 0xde (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100f9f [0x44, 0x21, 0xCE] (fun s => s.RIP = 0x100f9f) (andR32R32Effect 0x100f9f 3 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100f9f 3 6 9).toInstrSpec (and_r32_r32_rex_effect_step 0x100f9f 0x44 0xce (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100fa2 [0x41, 0xB9, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100fa2) (movR32Imm32Effect 0x100fa2 6 9 0x7f)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x100fa2 6 9 0x7f).toInstrSpec (mov_r32_imm32_rex_effect_step 0x100fa2 0x41 0xb9 (by decide) (by decide) 0x7f) pre_rip
  have f8 : InstrSpec 0x100fa8 [0x4D, 0x0F, 0xBD, 0xCD] (fun s => s.RIP = 0x100fa8) (bsrR64R64Effect 0x100fa8 4 9 13)
      [.gpr 9, .gpr 13] [] [.reg 9, .flags, .rip] :=
    (bsrR64R64Effect_footprint 0x100fa8 4 9 13).toInstrSpec (bsr_r64_r64_effect_step 0x100fa8 0x4d (by decide) 0xcd (by decide)) pre_rip
  have f9 : InstrSpec 0x100fac [0x41, 0x83, 0xF1, 0x3F] (fun s => s.RIP = 0x100fac) (xorR32Imm8Effect 0x100fac 4 9 0x3f)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x100fac 4 9 0x3f).toInstrSpec (xor_r32_imm8_rex_effect_step 0x100fac 0x41 0xf1 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x100fb0 [0xF7, 0xD9] (fun s => s.RIP = 0x100fb0) (negR32Effect 0x100fb0 2 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR32Effect_footprint 0x100fb0 2 1).toInstrSpec (neg_r32_effect_step 0x100fb0 0xd9 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x100fb2 [0x44, 0x21, 0xC9] (fun s => s.RIP = 0x100fb2) (andR32R32Effect 0x100fb2 3 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100fb2 3 1 9).toInstrSpec (and_r32_r32_rex_effect_step 0x100fb2 0x44 0xc9 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x100fb5 [0x01, 0xF1] (fun s => s.RIP = 0x100fb5) (addR32R32Effect 0x100fb5 2 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100fb5 2 1 6).toInstrSpec (add_r32_r32_effect_step 0x100fb5 0xf1 (by decide)) pre_rip
  have f13 : InstrSpec 0x100fb7 [0xBE, 0x7F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100fb7) (movR32Imm32Effect 0x100fb7 5 6 0x7f)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x100fb7 5 6 0x7f).toInstrSpec (mov_r32_imm32_effect_step 0x100fb7 0xbe (by decide) 0x7f) pre_rip
  have f14 : InstrSpec 0x100fbc [0x49, 0x0F, 0xBD, 0xF6] (fun s => s.RIP = 0x100fbc) (bsrR64R64Effect 0x100fbc 4 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (bsrR64R64Effect_footprint 0x100fbc 4 6 14).toInstrSpec (bsr_r64_r64_effect_step 0x100fbc 0x49 (by decide) 0xf6 (by decide)) pre_rip
  have f15 : InstrSpec 0x100fc0 [0x83, 0xF6, 0x3F] (fun s => s.RIP = 0x100fc0) (xorR32Imm8Effect 0x100fc0 3 6 0x3f)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x100fc0 3 6 0x3f).toInstrSpec (xor_r32_imm8_effect_step 0x100fc0 0xf6 0x3f (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x100fc3 [0xF7, 0xDA] (fun s => s.RIP = 0x100fc3) (negR32Effect 0x100fc3 2 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR32Effect_footprint 0x100fc3 2 2).toInstrSpec (neg_r32_effect_step 0x100fc3 0xda (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x100fc5 [0x21, 0xF2] (fun s => s.RIP = 0x100fc5) (andR32R32Effect 0x100fc5 2 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100fc5 2 2 6).toInstrSpec (and_r32_r32_effect_step 0x100fc5 0xf2 (by decide)) pre_rip
  have f18 : InstrSpec 0x100fc7 [0x49, 0x0F, 0xBD, 0xFF] (fun s => s.RIP = 0x100fc7) (bsrR64R64Effect 0x100fc7 4 7 15)
      [.gpr 7, .gpr 15] [] [.reg 7, .flags, .rip] :=
    (bsrR64R64Effect_footprint 0x100fc7 4 7 15).toInstrSpec (bsr_r64_r64_effect_step 0x100fc7 0x49 (by decide) 0xff (by decide)) pre_rip
  have f19 : InstrSpec 0x100fcb [0x83, 0xF7, 0x3F] (fun s => s.RIP = 0x100fcb) (xorR32Imm8Effect 0x100fcb 3 7 0x3f)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x100fcb 3 7 0x3f).toInstrSpec (xor_r32_imm8_effect_step 0x100fcb 0xf7 0x3f (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f8a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f8f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 54), (8, 8), (9, 56), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f95) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 54), (8, 8), (9, 58), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f99) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 54), (8, 8), (9, 60), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f9d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 62), (7, 54), (8, 8), (9, 60), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f9f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 64), (7, 54), (8, 8), (9, 60), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fa2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 64), (7, 54), (8, 8), (9, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fa8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 64), (7, 54), (8, 8), (9, 68), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fac) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 64), (7, 54), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fb0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 72), (2, 2), (3, 3), (4, 4), (6, 64), (7, 54), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fb2) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 74), (2, 2), (3, 3), (4, 4), (6, 64), (7, 54), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fb5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 76), (2, 2), (3, 3), (4, 4), (6, 64), (7, 54), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fb7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 76), (2, 2), (3, 3), (4, 4), (6, 78), (7, 54), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fbc) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 76), (2, 2), (3, 3), (4, 4), (6, 80), (7, 54), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fc0) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 76), (2, 2), (3, 3), (4, 4), (6, 82), (7, 54), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fc3) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 76), (2, 84), (3, 3), (4, 4), (6, 82), (7, 54), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fc5) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 76), (2, 86), (3, 3), (4, 4), (6, 82), (7, 54), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fc7) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 76), (2, 86), (3, 3), (4, 4), (6, 82), (7, 88), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fcb) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 76), (2, 86), (3, 3), (4, 4), (6, 82), (7, 90), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fce) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100f82_1 code

theorem block_l100f82 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100f82 :=
  Rest.liftedBlock (rest_l100f82 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100f82 x hx)

theorem rest_l101003 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101003 bytes_l101003) (entryMap (live .l101003))
      4 0x101003 bytes_l101003 b_l101003 := by
  have f0 : InstrSpec 0x101003 [0x89, 0xD2] (fun s => s.RIP = 0x101003) (movR32R32Effect 0x101003 2 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x101003 2 2 2).toInstrSpec (mov_r32_r32_effect_step 0x101003 0xd2 (by decide)) pre_rip
  have f1 : InstrSpec 0x101005 [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x101005) (movR64R64Effect 0x101005 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101005 6 8).toInstrSpec (mov_r64_r64_effect_step 0x101005 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101008 [0x48, 0x29, 0xD6] (fun s => s.RIP = 0x101008) (subR64R64Effect 0x101008 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (subR64R64Effect_footprint 0x101008 6 2).toInstrSpec (sub_r64_r64_effect_step 0x101008 0x48 0xd6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101005) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101008) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10100b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel32_effect_step 0x10100b 2 0x3a7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101003 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101003 :=
  Rest.liftedBlock (rest_l101003 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101003 x hx)

theorem rest_l101011 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101011 bytes_l101011) (entryMap (live .l101011))
      7 0x101011 bytes_l101011 b_l101011 := by
  have f0 : InstrSpec 0x101011 [0x83, 0xE5, 0xF8] (fun s => s.RIP = 0x101011) (andR32Imm8Effect 0x101011 3 5 0xf8)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x101011 3 5 0xf8).toInstrSpec (and_r32_imm8_effect_step 0x101011 0xe5 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101014 [0x41, 0x29, 0xE9] (fun s => s.RIP = 0x101014) (subR32R32Effect 0x101014 3 9 5)
      [.gpr 9, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (subR32R32Effect_footprint 0x101014 3 9 5).toInstrSpec (sub_r32_r32_rex_effect_step 0x101014 0x41 0xe9 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101017 [0x31, 0xD2] (fun s => s.RIP = 0x101017) (xorR32R32Effect 0x101017 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101017 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x101017 0xd2 (by decide)) pre_rip
  have f3 : InstrSpec 0x101019 [0x44, 0x89, 0xCD] (fun s => s.RIP = 0x101019) (movR32R32Effect 0x101019 3 5 9)
      [.gpr 9] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x101019 3 5 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x101019 0x44 0xcd (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10101c [0x29, 0xCD] (fun s => s.RIP = 0x10101c) (subR32R32Effect 0x10101c 2 5 1)
      [.gpr 5, .gpr 1] [] [.reg 5, .flags, .rip] :=
    (subR32R32Effect_footprint 0x10101c 2 5 1).toInstrSpec (sub_r32_r32_effect_step 0x10101c 0xcd (by decide)) pre_rip
  have f5 : InstrSpec 0x10101e [0x0F, 0x42, 0xEA] (fun s => s.RIP = 0x10101e) (atFlags (condHolds 2) (cmovR32R32Effect 0x10101e 3 5 2))
      [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .rip] :=
    (cmovR32R32Effect_footprint 0x10101e 3 5 2 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x10101e 2 0xea (by decide) c)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101014) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101017) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 53), (6, 6), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101019) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 59), (6, 6), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10101c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 61), (6, 6), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10101e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 64), (6, 6), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101021) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 66) (jmp_rel8_effect_step 0x101021 0x3 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l101011 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101011 :=
  Rest.liftedBlock (rest_l101011 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101011 x hx)

theorem rest_l101023 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101023 bytes_l101023) (entryMap (live .l101023))
      1 0x101023 bytes_l101023 b_l101023 := by
  have f0 : InstrSpec 0x101023 [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x101023) (movR64R64Effect 0x101023 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101023 6 8).toInstrSpec (mov_r64_r64_effect_step 0x101023 0x4c 0xc6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101026) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l101023 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101023 :=
  Rest.liftedBlock (rest_l101023 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101023 x hx)

theorem rest_l101026 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101026 bytes_l101026) (entryMap (live .l101026))
      10 0x101026 bytes_l101026 b_l101026 := by
  have f0 : InstrSpec 0x101026 [0x44, 0x89, 0x8C, 0x24, 0x9C, 0x00, 0x00, 0x00] (StorePre 0x101026 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x101026 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x101026 9 (.sib 4 none 0 (.d32 0x9c)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x101026 9 (.sib 4 none 0 (.d32 0x9c))).toInstrSpec (mov_m32_r32_effect_step 0x101026 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0x9c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10102e [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10102e 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10102e + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10102e (.sib 4 none 0 (.d32 0x80)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10102e (.sib 4 none 0 (.d32 0x80)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10102e 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10103a [0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10103a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10103a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10103a (.sib 4 none 0 (.d8 0x78)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10103a (.sib 4 none 0 (.d8 0x78)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10103a 0x48 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101043 [0x48, 0xC7, 0x44, 0x24, 0x70, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101043 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x101043 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x101043 (.sib 4 none 0 (.d8 0x70)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101043 (.sib 4 none 0 (.d8 0x70)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101043 0x48 (by decide) (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10104c [0x48, 0xC7, 0x44, 0x24, 0x68, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10104c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10104c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10104c (.sib 4 none 0 (.d8 0x68)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10104c (.sib 4 none 0 (.d8 0x68)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10104c 0x48 (by decide) (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x101055 [0x48, 0x8D, 0x54, 0x24, 0x68] (fun s => s.RIP = 0x101055) (leaR64Effect 0x101055 2 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x101055 2 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (lea_r64_effect_step 0x101055 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10105a [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10105a) (movR32Imm32Effect 0x10105a 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10105a 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10105a 0xb9 (by decide) 0x4) pre_rip
  have f7 : InstrSpec 0x10105f [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x10105f) (movR64R64Effect 0x10105f 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10105f 7 0).toInstrSpec (mov_r64_r64_effect_step 0x10105f 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101062 [0x45, 0x89, 0xC8] (fun s => s.RIP = 0x101062) (movR32R32Effect 0x101062 3 8 9)
      [.gpr 9] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x101062 3 8 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x101062 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101065 [0xE8, 0x06, 0x6D, 0x02, 0x00] (PushPre 0x101065 5) (callEffect (fun _ => 0x127d70) 0x10106a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101065 0x127d70 0x10106a).toInstrSpec (call_rel32_effect_step 0x101065 0x26d06 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10102e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10103a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101043) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10104c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101055) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10105a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 60), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10105f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 60), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101062) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 60), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 62), (8, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101065) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 60), (2, 58), (3, 3), (4, 66), (5, 5), (6, 6), (7, 62), (8, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d70) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l101026 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101026 :=
  Rest.liftedBlock (rest_l101026 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101026 x hx)

theorem rest_l10106a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10106a bytes_l10106a) (entryMap (live .l10106a))
      2 0x10106a bytes_l10106a b_l10106a := by
  have f0 : InstrSpec 0x10106a [0x3C, 0xFF] (fun s => s.RIP = 0x10106a) (cmpAlImm8Effect 0x10106a 0xff)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x10106a 0xff).toInstrSpec (cmp_al_imm8_effect_step 0x10106a 0xff) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10106c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10106c 5 0x357) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10106a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10106a :=
  Rest.liftedBlock (rest_l10106a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10106a x hx)

theorem rest_l101072 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101072 bytes_l101072) (entryMap (live .l101072))
      12 0x101072 bytes_l101072 b_l101072 := by
  have f0 : InstrSpec 0x101072 [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x101072 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101072 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101072 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101072 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x101072 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10107a [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x10107a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10107a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10107a 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10107a 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x10107a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10107f [0x48, 0x8B, 0x44, 0x24, 0x78] (LoadPre 0x10107f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10107f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10107f 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10107f 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x10107f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x101084 [0x48, 0x89, 0x44, 0x24, 0x58] (StorePre 0x101084 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x101084 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101084 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101084 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x101084 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101089 [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x101089 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101089 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101089 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101089 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x101089 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10108e [0x48, 0x8B, 0x4C, 0x24, 0x70] (LoadPre 0x10108e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10108e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10108e 1 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10108e 1 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x10108e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x101093 [0x48, 0x89, 0x4C, 0x24, 0x50] (StorePre 0x101093 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101093 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101093 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101093 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x101093 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x101098 [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x101098 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101098 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101098 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101098 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x101098 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10109d [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x10109d) (leaR64Effect 0x10109d 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10109d 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10109d 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1010a2 [0x48, 0x8D, 0x74, 0x24, 0x48] (fun s => s.RIP = 0x1010a2) (leaR64Effect 0x1010a2 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1010a2 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x1010a2 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1010a7 [0x89, 0xEA] (fun s => s.RIP = 0x1010a7) (movR32R32Effect 0x1010a7 2 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x1010a7 2 2 5).toInstrSpec (mov_r32_r32_effect_step 0x1010a7 0xea (by decide)) pre_rip
  have f11 : InstrSpec 0x1010a9 [0xE8, 0x02, 0x55, 0x00, 0x00] (PushPre 0x1010a9 5) (callEffect (fun _ => 0x1065b0) 0x1010ae)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1010a9 0x1065b0 0x1010ae).toInstrSpec (call_rel32_effect_step 0x1010a9 0x5502 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10107a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10107f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101084) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101089) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10108e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101093) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101098) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10109d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010a2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010a7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010a9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 61), (2, 69), (3, 3), (4, 71), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1065b0) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l101072 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101072 :=
  Rest.liftedBlock (rest_l101072 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101072 x hx)

theorem rest_l1010ae_5 [Bindings] (code : CodeMap) :
    Rest (n := 233) code lifted (codeRange 0x1010ae bytes_l1010ae) [(1, 231), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]
      12 0x101239 bytes_l1010ae_5 b_l1010ae_5 := by
  have f100 : InstrSpec 0x101239 [0x48, 0x09, 0xE9] (fun s => s.RIP = 0x101239) (orR64R64Effect 0x101239 1 5)
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x101239 1 5).toInstrSpec (or_r64_r64_effect_step 0x101239 0x48 0xe9 (by decide) (by decide)) pre_rip
  have f101 : InstrSpec 0x10123c [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x10123c) (shrR64Effect 0x10123c 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10123c 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x10123c 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x101240 [0x48, 0x89, 0x4C, 0x24, 0x48] (StorePre 0x101240 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101240 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101240 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101240 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x101240 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f103 : InstrSpec 0x101245 [0x0F, 0xB6, 0x44, 0x24, 0x48] (LoadPre 0x101245 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101245 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101245 5 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101245 5 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (movzx_r32_m8_effect_step 0x101245 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f104 : InstrSpec 0x10124a [0x24, 0x01] (fun s => s.RIP = 0x10124a) (andAlImm8Effect 0x10124a 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x10124a 0x1).toInstrSpec (and_al_imm8_effect_step 0x10124a 0x1) pre_rip
  have f105 : InstrSpec 0x10124c [0x44, 0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x10124c) (movzxR32R8Effect 0x10124c 4 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movzxR32R8Effect_footprint 0x10124c 4 8 0).toInstrSpec (movzx_r32_r8_rex_effect_step 0x10124c 0x44 (by decide) 0xc0 (by decide)) pre_rip
  have f106 : InstrSpec 0x101250 [0x48, 0x8D, 0x6C, 0x24, 0x08] (fun s => s.RIP = 0x101250) (leaR64Effect 0x101250 5 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x101250 5 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x101250 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x101255 [0x48, 0x8D, 0x54, 0x24, 0x68] (fun s => s.RIP = 0x101255) (leaR64Effect 0x101255 2 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x101255 2 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (lea_r64_effect_step 0x101255 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x10125a [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10125a) (movR32Imm32Effect 0x10125a 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10125a 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10125a 0xbe (by decide) 0x4) pre_rip
  have f109 : InstrSpec 0x10125f [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10125f) (movR32Imm32Effect 0x10125f 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10125f 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10125f 0xb9 (by decide) 0x4) pre_rip
  have f110 : InstrSpec 0x101264 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x101264) (movR64R64Effect 0x101264 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101264 7 5).toInstrSpec (mov_r64_r64_effect_step 0x101264 0x48 0xef (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x101267 [0xE8, 0x34, 0x6C, 0x02, 0x00] (PushPre 0x101267 5) (callEffect (fun _ => 0x127ea0) 0x10126c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101267 0x127ea0 0x10126c).toInstrSpec (call_rel32_effect_step 0x101267 0x26c34 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 233) (RestInside.out (n := 233) f100 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 234) (ρ' := [(1, 233), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10123c) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 235) (RestInside.out (n := 235) f101 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 236) (ρ' := [(1, 235), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101240) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 237) (RestInside.exec (n := 237) (ρ' := [(1, 235), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101245) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f103 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 238), (1, 235), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10124a) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f104 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 241) (ρ' := [(0, 240), (1, 235), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10124c) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f105 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 243) (ρ' := [(0, 240), (1, 235), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 242), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101250) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f106 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 245) (ρ' := [(0, 240), (1, 235), (2, 109), (3, 185), (4, 4), (5, 244), (6, 138), (7, 107), (8, 242), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101255) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 246) (RestInside.out (n := 246) f107 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 247) (ρ' := [(0, 240), (1, 235), (2, 246), (3, 185), (4, 4), (5, 244), (6, 138), (7, 107), (8, 242), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10125a) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 248) (RestInside.out (n := 248) f108 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 249) (ρ' := [(0, 240), (1, 235), (2, 246), (3, 185), (4, 4), (5, 244), (6, 248), (7, 107), (8, 242), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10125f) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 250) (RestInside.out (n := 250) f109 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 251) (ρ' := [(0, 240), (1, 250), (2, 246), (3, 185), (4, 4), (5, 244), (6, 248), (7, 107), (8, 242), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101264) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 252) (RestInside.out (n := 252) f110 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 253) (ρ' := [(0, 240), (1, 250), (2, 246), (3, 185), (4, 4), (5, 244), (6, 248), (7, 252), (8, 242), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101267) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 254) (RestInside.out (n := 254) f111 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 255) (ρ' := [(0, 240), (1, 250), (2, 246), (3, 185), (4, 254), (5, 244), (6, 248), (7, 252), (8, 242), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127ea0) f111 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 256) (by decide) (by decide) rfl rfl

theorem rest_l1010ae_4 [Bindings] (code : CodeMap) :
    Rest (n := 195) code lifted (codeRange 0x1010ae bytes_l1010ae) [(1, 193), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]
      32 0x1011f0 bytes_l1010ae_4 b_l1010ae_4 := by
  have f80 : InstrSpec 0x1011f0 [0x48, 0x2B, 0x4C, 0x24, 0x48] (LoadPre 0x1011f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1011f0 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1011f0 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x1011f0 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (sub_r64_m64_effect_step 0x1011f0 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f81 : InstrSpec 0x1011f5 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x1011f5) (sarR64Effect 0x1011f5 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x1011f5 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x1011f5 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x1011f9 [0x4C, 0x01, 0xC1] (fun s => s.RIP = 0x1011f9) (addR64R64Effect 0x1011f9 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1011f9 1 8).toInstrSpec (add_r64_r64_effect_step 0x1011f9 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x1011fc [0x48, 0x21, 0xD1] (fun s => s.RIP = 0x1011fc) (andR64R64Effect 0x1011fc 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1011fc 1 2).toInstrSpec (and_r64_r64_effect_step 0x1011fc 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x1011ff [0x48, 0x09, 0xF9] (fun s => s.RIP = 0x1011ff) (orR64R64Effect 0x1011ff 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1011ff 1 7).toInstrSpec (or_r64_r64_effect_step 0x1011ff 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x101202 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x101202) (shrR64Effect 0x101202 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x101202 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x101202 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x101206 [0x48, 0x89, 0x4C, 0x24, 0x48] (StorePre 0x101206 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101206 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101206 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101206 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x101206 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f87 : InstrSpec 0x10120b [0x31, 0xC9] (fun s => s.RIP = 0x10120b) (xorR32R32Effect 0x10120b 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10120b 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x10120b 0xc9 (by decide)) pre_rip
  have f88 : InstrSpec 0x10120d [0x48, 0x2B, 0x4C, 0x24, 0x48] (LoadPre 0x10120d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10120d + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10120d 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10120d 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (sub_r64_m64_effect_step 0x10120d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f89 : InstrSpec 0x101212 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x101212) (sarR64Effect 0x101212 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x101212 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x101212 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x101216 [0x4C, 0x01, 0xD9] (fun s => s.RIP = 0x101216) (addR64R64Effect 0x101216 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101216 1 11).toInstrSpec (add_r64_r64_effect_step 0x101216 0x4c 0xd9 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x101219 [0x4C, 0x21, 0xC9] (fun s => s.RIP = 0x101219) (andR64R64Effect 0x101219 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x101219 1 9).toInstrSpec (and_r64_r64_effect_step 0x101219 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x10121c [0x48, 0x09, 0xF1] (fun s => s.RIP = 0x10121c) (orR64R64Effect 0x10121c 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10121c 1 6).toInstrSpec (or_r64_r64_effect_step 0x10121c 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f93 : InstrSpec 0x10121f [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x10121f) (shrR64Effect 0x10121f 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10121f 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x10121f 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x101223 [0x48, 0x89, 0x4C, 0x24, 0x48] (StorePre 0x101223 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101223 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101223 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101223 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x101223 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f95 : InstrSpec 0x101228 [0x31, 0xC9] (fun s => s.RIP = 0x101228) (xorR32R32Effect 0x101228 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101228 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x101228 0xc9 (by decide)) pre_rip
  have f96 : InstrSpec 0x10122a [0x48, 0x2B, 0x4C, 0x24, 0x48] (LoadPre 0x10122a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10122a + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10122a 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10122a 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (sub_r64_m64_effect_step 0x10122a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f97 : InstrSpec 0x10122f [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x10122f) (sarR64Effect 0x10122f 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x10122f 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x10122f 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x101233 [0x4C, 0x01, 0xE9] (fun s => s.RIP = 0x101233) (addR64R64Effect 0x101233 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101233 1 13).toInstrSpec (add_r64_r64_effect_step 0x101233 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x101236 [0x4C, 0x21, 0xF9] (fun s => s.RIP = 0x101236) (andR64R64Effect 0x101236 1 15)
      [.gpr 1, .gpr 15] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x101236 1 15).toInstrSpec (and_r64_r64_effect_step 0x101236 0x4c 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f80 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(1, 195), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011f5) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f81 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(1, 197), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011f9) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f82 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(1, 199), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011fc) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f83 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(1, 201), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011ff) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f84 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 204) (ρ' := [(1, 203), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101202) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 205) (RestInside.out (n := 205) f85 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 206) (ρ' := [(1, 205), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101206) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 207) (RestInside.exec (n := 207) (ρ' := [(1, 205), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10120b) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f87 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(1, 208), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10120d) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f88 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(1, 210), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101212) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f89 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(1, 212), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101216) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f90 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(1, 214), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101219) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f91 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(1, 216), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10121c) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.out (n := 218) f92 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 219) (ρ' := [(1, 218), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10121f) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 220) (RestInside.out (n := 220) f93 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 221) (ρ' := [(1, 220), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101223) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 222) (RestInside.exec (n := 222) (ρ' := [(1, 220), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101228) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f95 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(1, 223), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10122a) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f96 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(1, 225), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10122f) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f97 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(1, 227), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101233) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f98 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(1, 229), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101236) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.out (n := 231) f99 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 232) (ρ' := [(1, 231), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101239) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1010ae_5 code

theorem rest_l1010ae_3 [Bindings] (code : CodeMap) :
    Rest (n := 163) code lifted (codeRange 0x1010ae bytes_l1010ae) [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 14), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]
      52 0x101198 bytes_l1010ae_3 b_l1010ae_3 := by
  have f60 : InstrSpec 0x101198 [0x49, 0x09, 0xDF] (fun s => s.RIP = 0x101198) (orR64R64Effect 0x101198 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x101198 15 3).toInstrSpec (or_r64_r64_effect_step 0x101198 0x49 0xdf (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x10119b [0x31, 0xC0] (fun s => s.RIP = 0x10119b) (xorR32R32Effect 0x10119b 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10119b 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x10119b 0xc0 (by decide)) pre_rip
  have f62 : InstrSpec 0x10119d [0x48, 0x2B, 0x44, 0x24, 0x08] (LoadPre 0x10119d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10119d + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10119d 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10119d 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x10119d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f63 : InstrSpec 0x1011a2 [0x48, 0xC1, 0xF8, 0x3F] (fun s => s.RIP = 0x1011a2) (sarR64Effect 0x1011a2 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (sarR64Effect_footprint 0x1011a2 4 0 63).toInstrSpec (sar_r64_imm8_effect_step 0x1011a2 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x1011a6 [0x4C, 0x01, 0xE8] (fun s => s.RIP = 0x1011a6) (addR64R64Effect 0x1011a6 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1011a6 0 13).toInstrSpec (add_r64_r64_effect_step 0x1011a6 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x1011a9 [0x4C, 0x8B, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x1011a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1011a9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1011a9 14 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1011a9 14 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x1011a9 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f66 : InstrSpec 0x1011b1 [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x1011b1) (movR64R64Effect 0x1011b1 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1011b1 3 0).toInstrSpec (mov_r64_r64_effect_step 0x1011b1 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x1011b4 [0x4C, 0x21, 0xFB] (fun s => s.RIP = 0x1011b4) (andR64R64Effect 0x1011b4 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1011b4 3 15).toInstrSpec (and_r64_r64_effect_step 0x1011b4 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x1011b7 [0x48, 0x09, 0xEB] (fun s => s.RIP = 0x1011b7) (orR64R64Effect 0x1011b7 3 5)
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1011b7 3 5).toInstrSpec (or_r64_r64_effect_step 0x1011b7 0x48 0xeb (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x1011ba [0x48, 0xC1, 0xEB, 0x3F] (fun s => s.RIP = 0x1011ba) (shrR64Effect 0x1011ba 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x1011ba 4 3 63).toInstrSpec (shr_r64_imm8_effect_step 0x1011ba 0x48 0xeb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x1011be [0x48, 0x89, 0x5C, 0x24, 0x08] (StorePre 0x1011be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1011be + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1011be 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1011be 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1011be 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f71 : InstrSpec 0x1011c3 [0x48, 0x8D, 0x5C, 0x24, 0x08] (fun s => s.RIP = 0x1011c3) (leaR64Effect 0x1011c3 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x1011c3 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1011c3 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x1011c8 [0x48, 0x8B, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x1011c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1011c8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1011c8 3 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1011c8 3 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x1011c8 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f73 : InstrSpec 0x1011d0 [0x48, 0x89, 0x5C, 0x24, 0x08] (StorePre 0x1011d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1011d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1011d0 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1011d0 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1011d0 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f74 : InstrSpec 0x1011d5 [0x4C, 0x89, 0x54, 0x24, 0x10] (StorePre 0x1011d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1011d5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1011d5 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1011d5 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1011d5 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x1011da [0x4C, 0x89, 0x64, 0x24, 0x18] (StorePre 0x1011da 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1011da + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1011da 12 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1011da 12 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1011da 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f76 : InstrSpec 0x1011df [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x1011df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1011df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1011df 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1011df 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1011df 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f77 : InstrSpec 0x1011e4 [0x48, 0x89, 0x4C, 0x24, 0x48] (StorePre 0x1011e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1011e4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1011e4 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1011e4 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x1011e4 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f78 : InstrSpec 0x1011e9 [0x48, 0x8D, 0x44, 0x24, 0x48] (fun s => s.RIP = 0x1011e9) (leaR64Effect 0x1011e9 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1011e9 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x1011e9 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x1011ee [0x31, 0xC9] (fun s => s.RIP = 0x1011ee) (xorR32R32Effect 0x1011ee 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1011ee 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x1011ee 0xc9 (by decide)) pre_rip
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f60 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 14), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10119b) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f61 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 165), (1, 84), (2, 109), (3, 3), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 14), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10119d) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f62 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 167), (1, 84), (2, 109), (3, 3), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 14), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011a2) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f63 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 169), (1, 84), (2, 109), (3, 3), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 14), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011a6) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f64 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 171), (1, 84), (2, 109), (3, 3), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 14), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011a9) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f65 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 171), (1, 84), (2, 109), (3, 3), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011b1) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f66 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 171), (1, 84), (2, 109), (3, 175), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011b4) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f67 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 171), (1, 84), (2, 109), (3, 177), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011b7) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f68 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 171), (1, 84), (2, 109), (3, 179), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011ba) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f69 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 171), (1, 84), (2, 109), (3, 181), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011be) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.exec (n := 183) (ρ' := [(0, 171), (1, 84), (2, 109), (3, 181), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011c3) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 184) (RestInside.exec (n := 184) (ρ' := [(0, 171), (1, 84), (2, 109), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011c8) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f72 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 171), (1, 84), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011d0) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.exec (n := 187) (ρ' := [(0, 171), (1, 84), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011d5) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 188) (RestInside.exec (n := 188) (ρ' := [(0, 171), (1, 84), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011da) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 189) (RestInside.exec (n := 189) (ρ' := [(0, 171), (1, 84), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011df) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 190) (RestInside.exec (n := 190) (ρ' := [(0, 171), (1, 84), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011e4) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 191) (RestInside.exec (n := 191) (ρ' := [(0, 171), (1, 84), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011e9) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 192) (RestInside.exec (n := 192) (ρ' := [(1, 84), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011ee) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f79 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(1, 193), (2, 109), (3, 185), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011f0) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1010ae_4 code

theorem rest_l1010ae_2 [Bindings] (code : CodeMap) :
    Rest (n := 124) code lifted (codeRange 0x1010ae bytes_l1010ae) [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (9, 117), (10, 101), (12, 122), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      72 0x101151 bytes_l1010ae_2 b_l1010ae_2 := by
  have f40 : InstrSpec 0x101151 [0x4C, 0x8B, 0x4C, 0x24, 0x78] (LoadPre 0x101151 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101151 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101151 9 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x101151 9 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x101151 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x101156 [0x4D, 0x89, 0xCB] (fun s => s.RIP = 0x101156) (movR64R64Effect 0x101156 11 9)
      [.gpr 9] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x101156 11 9).toInstrSpec (mov_r64_r64_effect_step 0x101156 0x4d 0xcb (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x101159 [0x4D, 0x29, 0xEB] (fun s => s.RIP = 0x101159) (subR64R64Effect 0x101159 11 13)
      [.gpr 11, .gpr 13] [] [.reg 11, .flags, .rip] :=
    (subR64R64Effect_footprint 0x101159 11 13).toInstrSpec (sub_r64_r64_effect_step 0x101159 0x4d 0xeb (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x10115c [0x49, 0xC1, 0xFC, 0x3F] (fun s => s.RIP = 0x10115c) (sarR64Effect 0x10115c 4 12 63)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (sarR64Effect_footprint 0x10115c 4 12 63).toInstrSpec (sar_r64_imm8_effect_step 0x10115c 0x49 0xfc 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x101160 [0x4D, 0x01, 0xDC] (fun s => s.RIP = 0x101160) (addR64R64Effect 0x101160 12 11)
      [.gpr 12, .gpr 11] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101160 12 11).toInstrSpec (add_r64_r64_effect_step 0x101160 0x4d 0xdc (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x101163 [0x49, 0xF7, 0xD1] (fun s => s.RIP = 0x101163) (notR64Effect 0x101163 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (notR64Effect_footprint 0x101163 9).toInstrSpec (not_r64_effect_step 0x101163 0x49 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x101166 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x101166) (movR64R64Effect 0x101166 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101166 6 13).toInstrSpec (mov_r64_r64_effect_step 0x101166 0x4c 0xee (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x101169 [0x4C, 0x21, 0xCE] (fun s => s.RIP = 0x101169) (andR64R64Effect 0x101169 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x101169 6 9).toInstrSpec (and_r64_r64_effect_step 0x101169 0x4c 0xce (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x10116c [0x4D, 0x09, 0xE9] (fun s => s.RIP = 0x10116c) (orR64R64Effect 0x10116c 9 13)
      [.gpr 9, .gpr 13] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10116c 9 13).toInstrSpec (or_r64_r64_effect_step 0x10116c 0x4d 0xe9 (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x10116f [0x4D, 0x89, 0xE7] (fun s => s.RIP = 0x10116f) (movR64R64Effect 0x10116f 15 12)
      [.gpr 12] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10116f 15 12).toInstrSpec (mov_r64_r64_effect_step 0x10116f 0x4d 0xe7 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x101172 [0x4D, 0x21, 0xCF] (fun s => s.RIP = 0x101172) (andR64R64Effect 0x101172 15 9)
      [.gpr 15, .gpr 9] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x101172 15 9).toInstrSpec (and_r64_r64_effect_step 0x101172 0x4d 0xcf (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x101175 [0x49, 0x09, 0xF7] (fun s => s.RIP = 0x101175) (orR64R64Effect 0x101175 15 6)
      [.gpr 15, .gpr 6] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x101175 15 6).toInstrSpec (or_r64_r64_effect_step 0x101175 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x101178 [0x49, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x101178) (shrR64Effect 0x101178 4 15 63)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x101178 4 15 63).toInstrSpec (shr_r64_imm8_effect_step 0x101178 0x49 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x10117c [0x4C, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x10117c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10117c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10117c 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10117c 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10117c 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x101181 [0x4C, 0x8B, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x101181 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101181 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101181 15 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x101181 15 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x101181 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f55 : InstrSpec 0x101189 [0x4D, 0x89, 0xFD] (fun s => s.RIP = 0x101189) (movR64R64Effect 0x101189 13 15)
      [.gpr 15] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x101189 13 15).toInstrSpec (mov_r64_r64_effect_step 0x101189 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x10118c [0x49, 0x29, 0xDD] (fun s => s.RIP = 0x10118c) (subR64R64Effect 0x10118c 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10118c 13 3).toInstrSpec (sub_r64_r64_effect_step 0x10118c 0x49 0xdd (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x10118f [0x49, 0xF7, 0xD7] (fun s => s.RIP = 0x10118f) (notR64Effect 0x10118f 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (notR64Effect_footprint 0x10118f 15).toInstrSpec (not_r64_effect_step 0x10118f 0x49 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x101192 [0x48, 0x89, 0xDD] (fun s => s.RIP = 0x101192) (movR64R64Effect 0x101192 5 3)
      [.gpr 3] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x101192 5 3).toInstrSpec (mov_r64_r64_effect_step 0x101192 0x48 0xdd (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x101195 [0x4C, 0x21, 0xFD] (fun s => s.RIP = 0x101195) (andR64R64Effect 0x101195 5 15)
      [.gpr 5, .gpr 15] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x101195 5 15).toInstrSpec (and_r64_r64_effect_step 0x101195 0x4c 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f40 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (9, 124), (10, 101), (12, 122), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101156) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f41 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (9, 124), (10, 101), (11, 126), (12, 122), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101159) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f42 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (9, 124), (10, 101), (11, 128), (12, 122), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10115c) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f43 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (9, 124), (10, 101), (11, 128), (12, 130), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101160) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f44 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (9, 124), (10, 101), (11, 128), (12, 132), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101163) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f45 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (9, 134), (10, 101), (11, 128), (12, 132), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101166) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f46 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 136), (7, 107), (8, 97), (9, 134), (10, 101), (11, 128), (12, 132), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101169) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f47 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 138), (7, 107), (8, 97), (9, 134), (10, 101), (11, 128), (12, 132), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10116c) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f48 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10116f) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f49 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 13), (14, 14), (15, 142), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101172) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f50 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 13), (14, 14), (15, 144), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101175) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f51 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 13), (14, 14), (15, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101178) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f52 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 13), (14, 14), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10117c) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.exec (n := 150) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 13), (14, 14), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101181) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f54 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 13), (14, 14), (15, 151), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101189) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f55 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 153), (14, 14), (15, 151), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10118c) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f56 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 14), (15, 151), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10118f) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f57 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 14), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101192) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f58 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (5, 159), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 14), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101195) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f59 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (5, 161), (6, 138), (7, 107), (8, 97), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 14), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101198) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1010ae_3 code

theorem rest_l1010ae_1 [Bindings] (code : CodeMap) :
    Rest (n := 86) code lifted (codeRange 0x1010ae bytes_l1010ae) [(0, 69), (1, 84), (2, 76), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      92 0x101107 bytes_l1010ae_1 b_l1010ae_1 := by
  have f20 : InstrSpec 0x101107 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x101107 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101107 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101107 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101107 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x101107 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x10110c [0x48, 0x8D, 0x44, 0x24, 0x08] (fun s => s.RIP = 0x10110c) (leaR64Effect 0x10110c 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10110c 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10110c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x101111 [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x101111) (xorR32R32Effect 0x101111 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101111 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x101111 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x101114 [0x4C, 0x2B, 0x54, 0x24, 0x08] (LoadPre 0x101114 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101114 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x101114 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 10, .gpr 4] [] [.reg 10, .flags, .rip] :=
    (subR64M64Effect_footprint 0x101114 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x101114 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x101119 [0x48, 0x8B, 0x54, 0x24, 0x70] (LoadPre 0x101119 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x101119 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101119 2 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x101119 2 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x101119 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x10111e [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x10111e) (movR64R64Effect 0x10111e 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10111e 8 2).toInstrSpec (mov_r64_r64_effect_step 0x10111e 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x101121 [0x4D, 0x29, 0xF0] (fun s => s.RIP = 0x101121) (subR64R64Effect 0x101121 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x101121 8 14).toInstrSpec (sub_r64_r64_effect_step 0x101121 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x101124 [0x49, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x101124) (sarR64Effect 0x101124 4 10 63)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (sarR64Effect_footprint 0x101124 4 10 63).toInstrSpec (sar_r64_imm8_effect_step 0x101124 0x49 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x101128 [0x4D, 0x01, 0xC2] (fun s => s.RIP = 0x101128) (addR64R64Effect 0x101128 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101128 10 8).toInstrSpec (add_r64_r64_effect_step 0x101128 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x10112b [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x10112b) (notR64Effect 0x10112b 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x10112b 2).toInstrSpec (not_r64_effect_step 0x10112b 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10112e [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10112e) (movR64R64Effect 0x10112e 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10112e 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10112e 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x101131 [0x48, 0x21, 0xD7] (fun s => s.RIP = 0x101131) (andR64R64Effect 0x101131 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x101131 7 2).toInstrSpec (and_r64_r64_effect_step 0x101131 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x101134 [0x4C, 0x09, 0xF2] (fun s => s.RIP = 0x101134) (orR64R64Effect 0x101134 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x101134 2 14).toInstrSpec (or_r64_r64_effect_step 0x101134 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x101137 [0x4D, 0x89, 0xD1] (fun s => s.RIP = 0x101137) (movR64R64Effect 0x101137 9 10)
      [.gpr 10] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x101137 9 10).toInstrSpec (mov_r64_r64_effect_step 0x101137 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x10113a [0x49, 0x21, 0xD1] (fun s => s.RIP = 0x10113a) (andR64R64Effect 0x10113a 9 2)
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10113a 9 2).toInstrSpec (and_r64_r64_effect_step 0x10113a 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x10113d [0x49, 0x09, 0xF9] (fun s => s.RIP = 0x10113d) (orR64R64Effect 0x10113d 9 7)
      [.gpr 9, .gpr 7] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10113d 9 7).toInstrSpec (or_r64_r64_effect_step 0x10113d 0x49 0xf9 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x101140 [0x49, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x101140) (shrR64Effect 0x101140 4 9 63)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x101140 4 9 63).toInstrSpec (shr_r64_imm8_effect_step 0x101140 0x49 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x101144 [0x4C, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x101144 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101144 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101144 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101144 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x101144 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x101149 [0x45, 0x31, 0xE4] (fun s => s.RIP = 0x101149) (xorR32R32Effect 0x101149 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101149 3 12 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x101149 0x45 0xe4 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10114c [0x4C, 0x2B, 0x64, 0x24, 0x08] (LoadPre 0x10114c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10114c + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10114c 12 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 12, .gpr 4] [] [.reg 12, .flags, .rip] :=
    (subR64M64Effect_footprint 0x10114c 12 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x10114c 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 69), (1, 84), (2, 76), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10110c) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 84), (2, 76), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101111) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f22 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 87), (1, 84), (2, 76), (3, 3), (4, 4), (6, 61), (10, 89), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101114) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f23 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 87), (1, 84), (2, 76), (3, 3), (4, 4), (6, 61), (10, 91), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101119) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 87), (1, 84), (2, 93), (3, 3), (4, 4), (6, 61), (10, 91), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10111e) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f25 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 87), (1, 84), (2, 93), (3, 3), (4, 4), (6, 61), (8, 95), (10, 91), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101121) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f26 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 87), (1, 84), (2, 93), (3, 3), (4, 4), (6, 61), (8, 97), (10, 91), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101124) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f27 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 87), (1, 84), (2, 93), (3, 3), (4, 4), (6, 61), (8, 97), (10, 99), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101128) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f28 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 87), (1, 84), (2, 93), (3, 3), (4, 4), (6, 61), (8, 97), (10, 101), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10112b) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f29 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 87), (1, 84), (2, 103), (3, 3), (4, 4), (6, 61), (8, 97), (10, 101), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10112e) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f30 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 87), (1, 84), (2, 103), (3, 3), (4, 4), (6, 61), (7, 105), (8, 97), (10, 101), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101131) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f31 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 87), (1, 84), (2, 103), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (10, 101), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101134) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f32 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (10, 101), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101137) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f33 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (9, 111), (10, 101), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10113a) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f34 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (9, 113), (10, 101), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10113d) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f35 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (9, 115), (10, 101), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101140) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f36 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (9, 117), (10, 101), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101144) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.exec (n := 119) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (9, 117), (10, 101), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101149) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f38 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (9, 117), (10, 101), (12, 120), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10114c) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f39 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 87), (1, 84), (2, 109), (3, 3), (4, 4), (6, 61), (7, 107), (8, 97), (9, 117), (10, 101), (12, 122), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101151) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1010ae_2 code

theorem rest_l1010ae [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1010ae bytes_l1010ae) (entryMap (live .l1010ae))
      112 0x1010ae bytes_l1010ae b_l1010ae := by
  have f0 : InstrSpec 0x1010ae [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x1010ae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1010ae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010ae 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1010ae 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1010ae 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1010b3 [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x1010b3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1010b3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1010b3 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1010b3 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x1010b3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1010b8 [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x1010b8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1010b8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010b8 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1010b8 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1010b8 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1010bd [0x48, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x1010bd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1010bd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010bd 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1010bd 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1010bd 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1010c2 [0x48, 0x89, 0x4C, 0x24, 0x48] (StorePre 0x1010c2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1010c2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1010c2 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1010c2 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x1010c2 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1010c7 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x1010c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1010c7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010c7 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1010c7 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1010c7 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1010cc [0x48, 0x89, 0x4C, 0x24, 0x68] (StorePre 0x1010cc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1010cc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1010cc 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1010cc 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x1010cc 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1010d1 [0x48, 0x89, 0x54, 0x24, 0x70] (StorePre 0x1010d1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1010d1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1010d1 2 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1010d1 2 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x1010d1 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1010d6 [0x48, 0x89, 0x74, 0x24, 0x78] (StorePre 0x1010d6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1010d6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1010d6 6 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1010d6 6 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x1010d6 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1010db [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1010db 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1010db + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1010db 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1010db 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x1010db 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1010e3 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x1010e3) (movR64R64Effect 0x1010e3 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1010e3 0 1).toInstrSpec (mov_r64_r64_effect_step 0x1010e3 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1010e6 [0x4C, 0x29, 0xF8] (fun s => s.RIP = 0x1010e6) (subR64R64Effect 0x1010e6 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1010e6 0 15).toInstrSpec (sub_r64_r64_effect_step 0x1010e6 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1010e9 [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x1010e9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1010e9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1010e9 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1010e9 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x1010e9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1010f1 [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x1010f1) (notR64Effect 0x1010f1 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x1010f1 1).toInstrSpec (not_r64_effect_step 0x1010f1 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1010f4 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x1010f4) (movR64R64Effect 0x1010f4 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1010f4 2 15).toInstrSpec (mov_r64_r64_effect_step 0x1010f4 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1010f7 [0x48, 0x21, 0xCA] (fun s => s.RIP = 0x1010f7) (andR64R64Effect 0x1010f7 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1010f7 2 1).toInstrSpec (and_r64_r64_effect_step 0x1010f7 0x48 0xca (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1010fa [0x4C, 0x09, 0xF9] (fun s => s.RIP = 0x1010fa) (orR64R64Effect 0x1010fa 1 15)
      [.gpr 1, .gpr 15] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1010fa 1 15).toInstrSpec (or_r64_r64_effect_step 0x1010fa 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1010fd [0x48, 0x21, 0xC1] (fun s => s.RIP = 0x1010fd) (andR64R64Effect 0x1010fd 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1010fd 1 0).toInstrSpec (and_r64_r64_effect_step 0x1010fd 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x101100 [0x48, 0x09, 0xD1] (fun s => s.RIP = 0x101100) (orR64R64Effect 0x101100 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x101100 1 2).toInstrSpec (or_r64_r64_effect_step 0x101100 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x101103 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x101103) (shrR64Effect 0x101103 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x101103 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x101103 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010b3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010b8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 56), (3, 3), (4, 4), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010bd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 56), (2, 58), (3, 3), (4, 4), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010c2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 56), (2, 58), (3, 3), (4, 4), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010c7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 56), (2, 58), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010cc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 56), (2, 58), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010d1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 56), (2, 58), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010d6) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 56), (2, 58), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010db) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 56), (2, 58), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010e3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 56), (2, 58), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010e6) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 56), (2, 58), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010e9) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (1, 56), (2, 58), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010f1) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 69), (1, 72), (2, 58), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010f4) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 69), (1, 72), (2, 74), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010f7) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 69), (1, 72), (2, 76), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010fa) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 69), (1, 78), (2, 76), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010fd) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 69), (1, 80), (2, 76), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101100) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 69), (1, 82), (2, 76), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101103) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 69), (1, 84), (2, 76), (3, 3), (4, 4), (6, 61), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101107) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1010ae_1 code

theorem block_l1010ae [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1010ae :=
  Rest.liftedBlock (rest_l1010ae code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1010ae x hx)

theorem rest_l10126c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10126c bytes_l10126c) (entryMap (live .l10126c))
      8 0x10126c bytes_l10126c b_l10126c := by
  have f0 : InstrSpec 0x10126c [0x4C, 0x8D, 0xA4, 0x24, 0xC8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10126c) (leaR64Effect 0x10126c 12 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x10126c 12 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (lea_r64_effect_step 0x10126c 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101274 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x101274) (movR64R64Effect 0x101274 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101274 7 5).toInstrSpec (mov_r64_r64_effect_step 0x101274 0x48 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101277 [0x4C, 0x8B, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00] (LoadPre 0x101277 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x101277 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101277 15 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x101277 15 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_r64_m64_effect_step 0x101277 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10127f [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10127f) (movR64R64Effect 0x10127f 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10127f 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10127f 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101282 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x101282) (movR64R64Effect 0x101282 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x101282 2 12).toInstrSpec (mov_r64_r64_effect_step 0x101282 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101285 [0x48, 0x8B, 0x9C, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x101285 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x101285 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101285 3 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x101285 3 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x101285 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10128d [0x48, 0x89, 0xD9] (fun s => s.RIP = 0x10128d) (movR64R64Effect 0x10128d 1 3)
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10128d 1 3).toInstrSpec (mov_r64_r64_effect_step 0x10128d 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101290 [0xE8, 0x6B, 0xED, 0xFF, 0xFF] (PushPre 0x101290 5) (callEffect (fun _ => 0x100000) 0x101295)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101290 0x100000 0x101295).toInstrSpec (call_rel32_effect_step 0x101290 0xffffed6b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (12, 53), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101274) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (7, 55), (12, 53), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101277) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(4, 4), (5, 5), (7, 55), (12, 53), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10127f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(4, 4), (5, 5), (6, 59), (7, 55), (12, 53), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101282) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 61), (4, 4), (5, 5), (6, 59), (7, 55), (12, 53), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101285) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 61), (3, 63), (4, 4), (5, 5), (6, 59), (7, 55), (12, 53), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10128d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 65), (2, 61), (3, 63), (4, 4), (5, 5), (6, 59), (7, 55), (12, 53), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101290) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 65), (2, 61), (3, 63), (4, 67), (5, 5), (6, 59), (7, 55), (12, 53), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100000) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l10126c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10126c :=
  Rest.liftedBlock (rest_l10126c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10126c x hx)

theorem rest_l101295_1 [Bindings] (code : CodeMap) :
    Rest (n := 79) code lifted (codeRange 0x101295 bytes_l101295) [(0, 72), (3, 3), (4, 4), (5, 5), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x101320 bytes_l101295_1 b_l101295_1 := by
  have f20 : InstrSpec 0x101320 [0xBA, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101320) (movR32Imm32Effect 0x101320 5 2 0x3)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x101320 5 2 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x101320 0xba (by decide) 0x3) pre_rip
  have f21 : InstrSpec 0x101325 [0xE8, 0x06, 0x2C, 0x00, 0x00] (PushPre 0x101325 5) (callEffect (fun _ => 0x103f30) 0x10132a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101325 0x103f30 0x10132a).toInstrSpec (call_rel32_effect_step 0x101325 0x2c06 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 72), (2, 79), (3, 3), (4, 4), (5, 5), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101325) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f21 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 72), (2, 79), (3, 3), (4, 81), (5, 5), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f30) f21 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 83) (by decide) (by decide) rfl rfl

theorem rest_l101295 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101295 bytes_l101295) (entryMap (live .l101295))
      22 0x101295 bytes_l101295 b_l101295 := by
  have f0 : InstrSpec 0x101295 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101295 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101295 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x101295 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101295 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101295 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10129e [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10129e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10129e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10129e (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10129e (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10129e 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1012a7 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1012a7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1012a7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1012a7 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1012a7 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1012a7 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1012b0 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1012b0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1012b0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1012b0 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1012b0 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1012b0 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1012b9 [0x48, 0xB8, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01] (fun s => s.RIP = 0x1012b9) (movR64Imm64Effect 0x1012b9 0 0x101010101010101)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1012b9 0 0x101010101010101).toInstrSpec (mov_r64_imm64_effect_step 0x1012b9 0x48 0xb8 (by decide) (by decide) 0x101010101010101) pre_rip
  have f5 : InstrSpec 0x1012c3 [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x1012c3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1012c3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012c3 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1012c3 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1012c3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1012c8 [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x1012c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1012c8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012c8 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1012c8 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1012c8 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1012cd [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x1012cd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1012cd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012cd 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1012cd 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x1012cd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1012d2 [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x1012d2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1012d2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012d2 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1012d2 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1012d2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1012d7 [0x48, 0x8B, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x1012d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1012d7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1012d7 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1012d7 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x1012d7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1012df [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x1012df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1012df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012df 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1012df 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x1012df 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1012e4 [0x48, 0x89, 0x5C, 0x24, 0x70] (StorePre 0x1012e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1012e4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012e4 3 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1012e4 3 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x1012e4 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1012e9 [0x4C, 0x89, 0x64, 0x24, 0x78] (StorePre 0x1012e9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1012e9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012e9 12 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1012e9 12 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x1012e9 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1012ee [0x48, 0x89, 0x9C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1012ee 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1012ee + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1012ee 3 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1012ee 3 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x1012ee 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1012f6 [0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x1012f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1012f6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1012f6 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1012f6 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x1012f6 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1012fe [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1012fe 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1012fe + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1012fe 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1012fe 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x1012fe 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x101306 [0x48, 0x8B, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00] (LoadPre 0x101306 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x101306 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101306 0 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101306 0 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_r64_m64_effect_step 0x101306 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10130e [0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x10130e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10130e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10130e 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10130e 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x10130e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x101316 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x101316) (leaR64Effect 0x101316 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101316 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x101316 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x10131b [0x48, 0x8D, 0x74, 0x24, 0x68] (fun s => s.RIP = 0x10131b) (leaR64Effect 0x10131b 6 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10131b 6 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (lea_r64_effect_step 0x10131b 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10129e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012a7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012b0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012b9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012c3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012c8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012cd) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012d2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012d7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012df) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012e4) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012e9) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012ee) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012f6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012fe) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101306) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10130e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101316) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10131b) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101320) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101295_1 code

theorem block_l101295 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101295 :=
  Rest.liftedBlock (rest_l101295 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101295 x hx)

theorem rest_l10132a_1 [Bindings] (code : CodeMap) :
    Rest (n := 85) code lifted (codeRange 0x10132a bytes_l10132a) [(0, 78), (1, 73), (2, 2), (3, 82), (4, 83), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x101380 bytes_l10132a_1 b_l10132a_1 := by
  have f20 : InstrSpec 0x101380 [0x41, 0x5C] (PopPre 0x101380) (popR64Effect 0x101380 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101380 2 12).toInstrSpec (pop_r64_rex_effect_step 0x101380 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f21 : InstrSpec 0x101382 [0x41, 0x5D] (PopPre 0x101382) (popR64Effect 0x101382 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101382 2 13).toInstrSpec (pop_r64_rex_effect_step 0x101382 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f22 : InstrSpec 0x101384 [0x41, 0x5E] (PopPre 0x101384) (popR64Effect 0x101384 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101384 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101384 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f23 : InstrSpec 0x101386 [0x41, 0x5F] (PopPre 0x101386) (popR64Effect 0x101386 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101386 2 15).toInstrSpec (pop_r64_rex_effect_step 0x101386 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f24 : InstrSpec 0x101388 [0x5D] (PopPre 0x101388) (popR64Effect 0x101388 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101388 1 5).toInstrSpec (pop_r64_effect_step 0x101388 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f25 : InstrSpec 0x101389 [0xC3] (RetPre 0x101389) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101389).toInstrSpec (ret_effect_step 0x101389) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f20 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 78), (1, 73), (2, 2), (3, 82), (4, 86), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 85), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101382) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f21 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 89) f21 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 90) (ρ' := [(0, 78), (1, 73), (2, 2), (3, 82), (4, 89), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 85), (13, 88), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101384) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f22 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 92) f22 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 93) (ρ' := [(0, 78), (1, 73), (2, 2), (3, 82), (4, 92), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 85), (13, 88), (14, 91), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101386) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f23 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 95) f23 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 96) (ρ' := [(0, 78), (1, 73), (2, 2), (3, 82), (4, 95), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 85), (13, 88), (14, 91), (15, 94), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101388) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f24 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 98) f24 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 99) (ρ' := [(0, 78), (1, 73), (2, 2), (3, 82), (4, 98), (5, 97), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 85), (13, 88), (14, 91), (15, 94), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101389) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f25 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 101) f25 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 102) (ρ' := [(0, 78), (1, 73), (2, 2), (3, 82), (4, 101), (5, 97), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 85), (13, 88), (14, 91), (15, 94), (22, 22), (39, 39), (50, 50), (51, 51)]) f25 (by decide) rfl rfl rfl (by decide)

theorem rest_l10132a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10132a bytes_l10132a) (entryMap (live .l10132a))
      26 0x10132a bytes_l10132a b_l10132a := by
  have f0 : InstrSpec 0x10132a [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x10132a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10132a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10132a 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10132a 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10132a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10132f [0x49, 0x89, 0x46, 0x40] (StorePre 0x10132f 4 (fun s => AddrMode.addr (.base 14 (.d8 0x40)) s (0x10132f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10132f 0 (.base 14 (.d8 0x40)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x10132f 0 (.base 14 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x10132f 0x49 (by decide) 0 (.base 14 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x101333 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x101333 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x101333 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101333 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101333 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x101333 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x101338 [0x49, 0x89, 0x46, 0x38] (StorePre 0x101338 4 (fun s => AddrMode.addr (.base 14 (.d8 0x38)) s (0x101338 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101338 0 (.base 14 (.d8 0x38)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x101338 0 (.base 14 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x101338 0x49 (by decide) 0 (.base 14 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10133c [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x10133c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10133c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10133c 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10133c 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10133c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101341 [0x49, 0x89, 0x46, 0x30] (StorePre 0x101341 4 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x101341 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101341 0 (.base 14 (.d8 0x30)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x101341 0 (.base 14 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x101341 0x49 (by decide) 0 (.base 14 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101345 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x101345 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101345 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101345 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101345 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x101345 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10134a [0x49, 0x89, 0x46, 0x28] (StorePre 0x10134a 4 (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x10134a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10134a 0 (.base 14 (.d8 0x28)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x10134a 0 (.base 14 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10134a 0x49 (by decide) 0 (.base 14 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10134e [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x10134e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10134e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10134e 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10134e 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10134e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x101353 [0x49, 0x89, 0x46, 0x20] (StorePre 0x101353 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x101353 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101353 0 (.base 14 (.d8 0x20)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x101353 0 (.base 14 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x101353 0x49 (by decide) 0 (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x101357 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x101357 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101357 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101357 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101357 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101357 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10135c [0x49, 0x89, 0x46, 0x18] (StorePre 0x10135c 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x10135c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10135c 0 (.base 14 (.d8 0x18)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x10135c 0 (.base 14 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10135c 0x49 (by decide) 0 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x101360 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x101360 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101360 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101360 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101360 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x101360 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x101365 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x101365 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101365 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101365 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101365 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x101365 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10136a [0x49, 0x89, 0x4E, 0x10] (StorePre 0x10136a 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x10136a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10136a 1 (.base 14 (.d8 0x10)))
      [.gpr 1, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x10136a 1 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10136a 0x49 (by decide) 1 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10136e [0x49, 0x89, 0x46, 0x08] (StorePre 0x10136e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x10136e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10136e 0 (.base 14 (.d8 0x8)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x10136e 0 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10136e 0x49 (by decide) 0 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x101372 [0x4D, 0x89, 0x3E] (StorePre 0x101372 3 (fun s => AddrMode.addr (.base 14 .none) s (0x101372 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x101372 15 (.base 14 .none))
      [.gpr 15, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x101372 15 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x101372 0x4d (by decide) 7 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x101375 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x101375) (movR64R64Effect 0x101375 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101375 0 14).toInstrSpec (mov_r64_r64_effect_step 0x101375 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x101378 [0x48, 0x81, 0xC4, 0xE8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101378) (addR64Imm32Effect 0x101378 4 0xe8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x101378 4 0xe8).toInstrSpec (add_r64_imm32_effect_step 0x101378 0x48 0xc4 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x10137f [0x5B] (PopPre 0x10137f) (popR64Effect 0x10137f 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10137f 1 3).toInstrSpec (pop_r64_effect_step 0x10137f 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10132f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101333) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101338) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10133c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101341) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101345) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10134a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10134e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101353) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101357) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10135c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101360) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101365) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 73), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10136a) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 73), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10136e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 73), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101372) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 71), (1, 73), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101375) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 73), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101378) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 78), (1, 73), (2, 2), (4, 80), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10137f) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f19 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 78), (1, 73), (2, 2), (3, 82), (4, 83), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101380) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10132a_1 code

theorem block_l10132a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10132a :=
  Rest.liftedBlock (rest_l10132a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10132a x hx)

theorem rest_l10138a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10138a bytes_l10138a) (entryMap (live .l10138a))
      5 0x10138a bytes_l10138a b_l10138a := by
  have f0 : InstrSpec 0x10138a [0xBA, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10138a) (movR32Imm32Effect 0x10138a 5 2 0x20)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10138a 5 2 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x10138a 0xba (by decide) 0x20) pre_rip
  have f1 : InstrSpec 0x10138f [0x31, 0xFF] (fun s => s.RIP = 0x10138f) (xorR32R32Effect 0x10138f 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10138f 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x10138f 0xff (by decide)) pre_rip
  have f2 : InstrSpec 0x101391 [0x4C, 0x89, 0xDE] (fun s => s.RIP = 0x101391) (movR64R64Effect 0x101391 6 11)
      [.gpr 11] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101391 6 11).toInstrSpec (mov_r64_r64_effect_step 0x101391 0x4c 0xde (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101394 [0x48, 0xC7, 0xC1, 0xE0, 0x20, 0x20, 0x00] (fun s => s.RIP = 0x101394) (movR64Imm32Effect 0x101394 1 0x2020e0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x101394 1 0x2020e0).toInstrSpec (mov_r64_imm32_effect_step 0x101394 0x48 0xc1 (by decide) (by decide) (by decide) 0x2020e0) pre_rip
  have f4 : InstrSpec 0x10139b [0xE8, 0xC0, 0x87, 0x02, 0x00] (PushPre 0x10139b 5) (callEffect (fun _ => 0x129b60) 0x1013a0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10139b 0x129b60 0x1013a0).toInstrSpec (call_rel32_effect_step 0x10139b 0x287c0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (4, 4), (5, 5), (7, 7), (11, 11)]) (p' := 0x10138f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (4, 4), (5, 5), (7, 55), (11, 11)]) (p' := 0x101391) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 53), (4, 4), (5, 5), (6, 57), (7, 55), (11, 11)]) (p' := 0x101394) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (2, 53), (4, 4), (5, 5), (6, 57), (7, 55), (11, 11)]) (p' := 0x10139b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 59), (2, 53), (4, 61), (5, 5), (6, 57), (7, 55), (11, 11)]) (p' := 0x129b60) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10138a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10138a :=
  Rest.liftedBlock (rest_l10138a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10138a x hx)

theorem rest_l1013a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1013a0 bytes_l1013a0) (entryMap (live .l1013a0))
      4 0x1013a0 bytes_l1013a0 b_l1013a0 := by
  have f0 : InstrSpec 0x1013a0 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1013a0) (movR32Imm32Effect 0x1013a0 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1013a0 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x1013a0 0xbe (by decide) 0x8) pre_rip
  have f1 : InstrSpec 0x1013a5 [0x48, 0xC7, 0xC7, 0x98, 0x20, 0x20, 0x00] (fun s => s.RIP = 0x1013a5) (movR64Imm32Effect 0x1013a5 7 0x202098)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x1013a5 7 0x202098).toInstrSpec (mov_r64_imm32_effect_step 0x1013a5 0x48 0xc7 (by decide) (by decide) (by decide) 0x202098) pre_rip
  have f2 : InstrSpec 0x1013ac [0x48, 0xC7, 0xC2, 0xC8, 0x20, 0x20, 0x00] (fun s => s.RIP = 0x1013ac) (movR64Imm32Effect 0x1013ac 2 0x2020c8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x1013ac 2 0x2020c8).toInstrSpec (mov_r64_imm32_effect_step 0x1013ac 0x48 0xc2 (by decide) (by decide) (by decide) 0x2020c8) pre_rip
  have f3 : InstrSpec 0x1013b3 [0xE8, 0xA8, 0x81, 0x02, 0x00] (PushPre 0x1013b3 5) (callEffect (fun _ => 0x129560) 0x1013b8)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1013b3 0x129560 0x1013b8).toInstrSpec (call_rel32_effect_step 0x1013b3 0x281a8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 53)]) (p' := 0x1013a5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x1013ac) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x1013b3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)]) (p' := 0x129560) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1013a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1013a0 :=
  Rest.liftedBlock (rest_l1013a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1013a0 x hx)

theorem rest_l1013b8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1013b8 bytes_l1013b8) (entryMap (live .l1013b8))
      4 0x1013b8 bytes_l1013b8 b_l1013b8 := by
  have f0 : InstrSpec 0x1013b8 [0x31, 0xFF] (fun s => s.RIP = 0x1013b8) (xorR32R32Effect 0x1013b8 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1013b8 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x1013b8 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x1013ba [0x4C, 0x89, 0xC2] (fun s => s.RIP = 0x1013ba) (movR64R64Effect 0x1013ba 2 8)
      [.gpr 8] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1013ba 2 8).toInstrSpec (mov_r64_r64_effect_step 0x1013ba 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1013bd [0x48, 0xC7, 0xC1, 0x80, 0x20, 0x20, 0x00] (fun s => s.RIP = 0x1013bd) (movR64Imm32Effect 0x1013bd 1 0x202080)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x1013bd 1 0x202080).toInstrSpec (mov_r64_imm32_effect_step 0x1013bd 0x48 0xc1 (by decide) (by decide) (by decide) 0x202080) pre_rip
  have f3 : InstrSpec 0x1013c4 [0xE8, 0x97, 0x87, 0x02, 0x00] (PushPre 0x1013c4 5) (callEffect (fun _ => 0x129b60) 0x1013c9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1013c4 0x129b60 0x1013c9).toInstrSpec (call_rel32_effect_step 0x1013c4 0x28797 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53), (8, 8)]) (p' := 0x1013ba) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8)]) (p' := 0x1013bd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8)]) (p' := 0x1013c4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 57), (2, 55), (4, 59), (5, 5), (6, 6), (7, 53), (8, 8)]) (p' := 0x129b60) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1013b8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1013b8 :=
  Rest.liftedBlock (rest_l1013b8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1013b8 x hx)

theorem rest_l1013c9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1013c9 bytes_l1013c9) (entryMap (live .l1013c9))
      9 0x1013c9 bytes_l1013c9 b_l1013c9 := by
  have f0 : InstrSpec 0x1013c9 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x98, 0x24, 0x20, 0x00] (StorePre 0x1013c9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1013c9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1013c9 (.sib 4 none 0 (.d8 0x8)) 0x202498)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1013c9 (.sib 4 none 0 (.d8 0x8)) 0x202498).toInstrSpec (mov_m64_imm32_effect_step 0x1013c9 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x202498) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1013d2 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x1013d2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1013d2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1013d2 (.sib 4 none 0 (.d8 0x10)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1013d2 (.sib 4 none 0 (.d8 0x10)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x1013d2 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1013db [0x48, 0x8D, 0x84, 0x24, 0x9C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1013db) (leaR64Effect 0x1013db 0 (.sib 4 none 0 (.d32 0x9c)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1013db 0 (.sib 4 none 0 (.d32 0x9c))).toInstrSpec (lea_r64_effect_step 0x1013db 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x9c)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1013e3 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x1013e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1013e3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1013e3 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1013e3 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1013e3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1013e8 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x90, 0xA1, 0x12, 0x00] (StorePre 0x1013e8 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1013e8 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1013e8 (.sib 4 none 0 (.d8 0x20)) 0x12a190)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1013e8 (.sib 4 none 0 (.d8 0x20)) 0x12a190).toInstrSpec (mov_m64_imm32_effect_step 0x1013e8 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x12a190) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1013f1 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x1013f1) (leaR64Effect 0x1013f1 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1013f1 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1013f1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1013f6 [0x48, 0xC7, 0xC7, 0x8F, 0x02, 0x20, 0x00] (fun s => s.RIP = 0x1013f6) (movR64Imm32Effect 0x1013f6 7 0x20028f)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x1013f6 7 0x20028f).toInstrSpec (mov_r64_imm32_effect_step 0x1013f6 0x48 0xc7 (by decide) (by decide) (by decide) 0x20028f) pre_rip
  have f7 : InstrSpec 0x1013fd [0x48, 0xC7, 0xC2, 0xA0, 0x22, 0x20, 0x00] (fun s => s.RIP = 0x1013fd) (movR64Imm32Effect 0x1013fd 2 0x2022a0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x1013fd 2 0x2022a0).toInstrSpec (mov_r64_imm32_effect_step 0x1013fd 0x48 0xc2 (by decide) (by decide) (by decide) 0x2022a0) pre_rip
  have f8 : InstrSpec 0x101404 [0xE8, 0x67, 0x83, 0x02, 0x00] (PushPre 0x101404 5) (callEffect (fun _ => 0x129770) 0x101409)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101404 0x129770 0x101409).toInstrSpec (call_rel32_effect_step 0x101404 0x28367 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x1013d2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5)]) (p' := 0x1013db) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x1013e3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x1013e8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (4, 4), (5, 5)]) (p' := 0x1013f1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (4, 4), (5, 5), (6, 59)]) (p' := 0x1013f6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (4, 4), (5, 5), (6, 59), (7, 61)]) (p' := 0x1013fd) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (2, 63), (4, 4), (5, 5), (6, 59), (7, 61)]) (p' := 0x101404) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (2, 63), (4, 65), (5, 5), (6, 59), (7, 61)]) (p' := 0x129770) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l1013c9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1013c9 :=
  Rest.liftedBlock (rest_l1013c9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1013c9 x hx)

theorem rest_l101409 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101409 bytes_l101409) (entryMap (live .l101409))
      13 0x101409 bytes_l101409 b_l101409 := by
  have f0 : InstrSpec 0x101409 [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101409) (fun _ => nopEffect 0x101409 7)
      [] [] [.rip] :=
    (nopEffect_footprint 0x101409 7).toInstrSpec (nop_m_effect_step 0x101409 [] (by decide) (by decide) (.base 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101410 [0x55] (PushPre 0x101410 1) (pushR64Effect 0x101410 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101410 1 5).toInstrSpec (push_r64_effect_step 0x101410 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101411 [0x41, 0x57] (PushPre 0x101411 2) (pushR64Effect 0x101411 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101411 2 15).toInstrSpec (push_r64_rex_effect_step 0x101411 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101413 [0x41, 0x56] (PushPre 0x101413 2) (pushR64Effect 0x101413 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101413 2 14).toInstrSpec (push_r64_rex_effect_step 0x101413 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101415 [0x41, 0x55] (PushPre 0x101415 2) (pushR64Effect 0x101415 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101415 2 13).toInstrSpec (push_r64_rex_effect_step 0x101415 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101417 [0x41, 0x54] (PushPre 0x101417 2) (pushR64Effect 0x101417 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101417 2 12).toInstrSpec (push_r64_rex_effect_step 0x101417 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x101419 [0x53] (PushPre 0x101419 1) (pushR64Effect 0x101419 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101419 1 3).toInstrSpec (push_r64_effect_step 0x101419 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x10141a [0x48, 0x81, 0xEC, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10141a) (subR64Imm32Effect 0x10141a 4 0xf8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10141a 4 0xf8).toInstrSpec (sub_r64_imm32_effect_step 0x10141a 0x48 0xec 0xf8 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101421 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x101421) (movR64R64Effect 0x101421 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101421 14 2).toInstrSpec (mov_r64_r64_effect_step 0x101421 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101424 [0x49, 0x89, 0xF7] (fun s => s.RIP = 0x101424) (movR64R64Effect 0x101424 15 6)
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x101424 15 6).toInstrSpec (mov_r64_r64_effect_step 0x101424 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101427 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x101427) (movR64R64Effect 0x101427 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x101427 3 7).toInstrSpec (mov_r64_r64_effect_step 0x101427 0x48 0xfb (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10142a [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x10142a) (movR64R64Effect 0x10142a 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10142a 7 4).toInstrSpec (mov_r64_r64_effect_step 0x10142a 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10142d [0xE8, 0x5E, 0x62, 0x02, 0x00] (PushPre 0x10142d 5) (callEffect (fun _ => 0x127690) 0x101432)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10142d 0x127690 0x101432).toInstrSpec (call_rel32_effect_step 0x10142d 0x2625e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101410) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101411) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101413) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101415) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101417) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 2), (3, 3), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101419) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 2), (3, 3), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10141a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101421) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101424) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101427) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(2, 2), (3, 72), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10142a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(2, 2), (3, 72), (4, 66), (5, 5), (6, 6), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10142d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(2, 2), (3, 72), (4, 76), (5, 5), (6, 6), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127690) f12 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 78) (by decide) (by decide) rfl rfl

theorem block_l101409 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101409 :=
  Rest.liftedBlock (rest_l101409 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101409 x hx)

theorem rest_l101432 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101432 bytes_l101432) (entryMap (live .l101432))
      2 0x101432 bytes_l101432 b_l101432 := by
  have f0 : InstrSpec 0x101432 [0x83, 0x3C, 0x24, 0x02] (LoadPre 0x101432 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101432 + BitVec.ofNat 64 4)) 4) (cmpMImm8Effect 0x101432 4 32 (.sib 4 none 0 .none) 0x2)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x101432 4 (.sib 4 none 0 .none) 0x2).toInstrSpec (cmp_m32_imm8_effect_step 0x101432 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x2) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101436) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x101436 5 0x1e8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101432 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101432 :=
  Rest.liftedBlock (rest_l101432 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101432 x hx)

theorem rest_l10143c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10143c bytes_l10143c) (entryMap (live .l10143c))
      13 0x10143c bytes_l10143c b_l10143c := by
  have f0 : InstrSpec 0x10143c [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x10143c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10143c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10143c 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10143c 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10143c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101441 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x101441 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101441 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101441 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101441 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x101441 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101446 [0x48, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x101446 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101446 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101446 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x101446 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101446 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10144b [0x48, 0x8B, 0x74, 0x24, 0x20] (LoadPre 0x10144b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10144b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10144b 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10144b 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10144b 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x101450 [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x101450 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101450 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101450 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x101450 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x101450 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101455 [0x48, 0x89, 0x44, 0x24, 0x50] (StorePre 0x101455 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101455 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101455 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101455 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x101455 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10145a [0x48, 0x89, 0x4C, 0x24, 0x58] (StorePre 0x10145a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10145a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10145a 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10145a 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x10145a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10145f [0x48, 0x89, 0x54, 0x24, 0x60] (StorePre 0x10145f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10145f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10145f 2 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10145f 2 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x10145f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101464 [0x48, 0x89, 0x74, 0x24, 0x68] (StorePre 0x101464 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101464 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101464 6 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101464 6 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x101464 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101469 [0x48, 0x89, 0x7C, 0x24, 0x70] (StorePre 0x101469 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x101469 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101469 7 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101469 7 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x101469 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10146e [0x48, 0x8D, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10146e) (leaR64Effect 0x10146e 7 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10146e 7 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (lea_r64_effect_step 0x10146e 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101476 [0x48, 0x8D, 0x74, 0x24, 0x50] (fun s => s.RIP = 0x101476) (leaR64Effect 0x101476 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101476 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x101476 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10147b [0xE8, 0x80, 0x54, 0x00, 0x00] (PushPre 0x10147b 5) (callEffect (fun _ => 0x106900) 0x101480)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10147b 0x106900 0x101480).toInstrSpec (call_rel32_effect_step 0x10147b 0x5480 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101441) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101446) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10144b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101450) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101455) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10145a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10145f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101464) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101469) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10146e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101476) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 70), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10147b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106900) f12 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 74) (by decide) (by decide) rfl rfl

theorem block_l10143c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10143c :=
  Rest.liftedBlock (rest_l10143c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10143c x hx)

theorem rest_l101480 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101480 bytes_l101480) (entryMap (live .l101480))
      2 0x101480 bytes_l101480 b_l101480 := by
  have f0 : InstrSpec 0x101480 [0x83, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x02] (LoadPre 0x101480 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x101480 + BitVec.ofNat 64 8)) 4) (cmpMImm8Effect 0x101480 8 32 (.sib 4 none 0 (.d32 0xc0)) 0x2)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x101480 8 (.sib 4 none 0 (.d32 0xc0)) 0x2).toInstrSpec (cmp_m32_imm8_effect_step 0x101480 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide) 0x2) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101488) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x101488 5 0x196) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101480 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101480 :=
  Rest.liftedBlock (rest_l101480 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101480 x hx)

theorem rest_l10148e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10148e bytes_l10148e) (entryMap (live .l10148e))
      5 0x10148e bytes_l10148e b_l10148e := by
  have f0 : InstrSpec 0x10148e [0x4C, 0x8B, 0xA4, 0x24, 0xC4, 0x00, 0x00, 0x00] (LoadPre 0x10148e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc4)) s (0x10148e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10148e 12 (.sib 4 none 0 (.d32 0xc4)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10148e 12 (.sib 4 none 0 (.d32 0xc4))).toInstrSpec (mov_r64_m64_effect_step 0x10148e 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xc4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101496 [0x0F, 0xB6, 0xAC, 0x24, 0xCC, 0x00, 0x00, 0x00] (LoadPre 0x101496 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc)) s (0x101496 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x101496 8 5 (.sib 4 none 0 (.d32 0xcc)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x101496 8 5 (.sib 4 none 0 (.d32 0xcc))).toInstrSpec (movzx_r32_m8_effect_step 0x101496 5 (.sib 4 none 0 (.d32 0xcc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10149e [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x10149e) (movR64R64Effect 0x10149e 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10149e 7 4).toInstrSpec (mov_r64_r64_effect_step 0x10149e 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1014a1 [0x48, 0x8D, 0x74, 0x24, 0x50] (fun s => s.RIP = 0x1014a1) (leaR64Effect 0x1014a1 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1014a1 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x1014a1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1014a6 [0xE8, 0x75, 0x4C, 0x00, 0x00] (PushPre 0x1014a6 5) (callEffect (fun _ => 0x106120) 0x1014ab)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1014a6 0x106120 0x1014ab).toInstrSpec (call_rel32_effect_step 0x1014a6 0x4c75 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101496) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10149e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 55), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014a1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 55), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014a6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 55), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106120) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10148e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10148e :=
  Rest.liftedBlock (rest_l10148e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10148e x hx)

theorem rest_l1014ab [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1014ab bytes_l1014ab) (entryMap (live .l1014ab))
      2 0x1014ab bytes_l1014ab b_l1014ab := by
  have f0 : InstrSpec 0x1014ab [0x83, 0x3C, 0x24, 0x02] (LoadPre 0x1014ab (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1014ab + BitVec.ofNat 64 4)) 4) (cmpMImm8Effect 0x1014ab 4 32 (.sib 4 none 0 .none) 0x2)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x1014ab 4 (.sib 4 none 0 .none) 0x2).toInstrSpec (cmp_m32_imm8_effect_step 0x1014ab (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x2) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014af) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1014af 5 0x16f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1014ab [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1014ab :=
  Rest.liftedBlock (rest_l1014ab code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1014ab x hx)

theorem rest_l1014b5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1014b5 bytes_l1014b5) (entryMap (live .l1014b5))
      9 0x1014b5 bytes_l1014b5 b_l1014b5 := by
  have f0 : InstrSpec 0x1014b5 [0x8B, 0x44, 0x24, 0x04] (LoadPre 0x1014b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1014b5 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1014b5 0 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1014b5 0 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x1014b5 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1014b9 [0x40, 0x80, 0xE5, 0x01] (fun s => s.RIP = 0x1014b9) (andR8Imm8Effect 0x1014b9 4 5 0x1)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x1014b9 4 5 0x1).toInstrSpec (and_r8_imm8_rex_effect_step 0x1014b9 0x40 0xe5 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1014bd [0x4C, 0x89, 0x64, 0x24, 0x78] (StorePre 0x1014bd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1014bd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1014bd 12 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1014bd 12 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x1014bd 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1014c2 [0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1014c2 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1014c2 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1014c2 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1014c2 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m32_r32_low_effect_step 0x1014c2 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1014c9 [0x40, 0x88, 0xAC, 0x24, 0x84, 0x00, 0x00, 0x00] (StorePre 0x1014c9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x1014c9 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x1014c9 8 5 (.sib 4 none 0 (.d32 0x84)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1014c9 8 5 (.sib 4 none 0 (.d32 0x84))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1014c9 0x40 (by decide) 5 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1014d1 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x1014d1) (movR64R64Effect 0x1014d1 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1014d1 7 4).toInstrSpec (mov_r64_r64_effect_step 0x1014d1 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1014d4 [0xBA, 0x0A, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1014d4) (movR32Imm32Effect 0x1014d4 5 2 0xa)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1014d4 5 2 0xa).toInstrSpec (mov_r32_imm32_effect_step 0x1014d4 0xba (by decide) 0xa) pre_rip
  have f7 : InstrSpec 0x1014d9 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x1014d9) (movR64R64Effect 0x1014d9 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1014d9 6 12).toInstrSpec (mov_r64_r64_effect_step 0x1014d9 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1014dc [0xE8, 0xEF, 0x61, 0x02, 0x00] (PushPre 0x1014dc 5) (callEffect (fun _ => 0x1276d0) 0x1014e1)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1014dc 0x1276d0 0x1014e1).toInstrSpec (call_rel32_effect_step 0x1014dc 0x261ef (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014b9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014bd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014c2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014c9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014d1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 55), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014d4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 1), (2, 62), (3, 3), (4, 4), (5, 55), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014d9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 62), (3, 3), (4, 4), (5, 55), (6, 64), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014dc) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 1), (2, 62), (3, 3), (4, 66), (5, 55), (6, 64), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276d0) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l1014b5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1014b5 :=
  Rest.liftedBlock (rest_l1014b5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1014b5 x hx)

theorem rest_l1014e1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1014e1 bytes_l1014e1) (entryMap (live .l1014e1))
      2 0x1014e1 bytes_l1014e1 b_l1014e1 := by
  have f0 : InstrSpec 0x1014e1 [0x83, 0x3C, 0x24, 0x02] (LoadPre 0x1014e1 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1014e1 + BitVec.ofNat 64 4)) 4) (cmpMImm8Effect 0x1014e1 4 32 (.sib 4 none 0 .none) 0x2)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x1014e1 4 (.sib 4 none 0 .none) 0x2).toInstrSpec (cmp_m32_imm8_effect_step 0x1014e1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x2) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014e5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1014e5 5 0x139) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1014e1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1014e1 :=
  Rest.liftedBlock (rest_l1014e1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1014e1 x hx)

theorem rest_l1014eb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1014eb bytes_l1014eb) (entryMap (live .l1014eb))
      4 0x1014eb bytes_l1014eb b_l1014eb := by
  have f0 : InstrSpec 0x1014eb [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1014eb) (leaR64Effect 0x1014eb 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1014eb 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x1014eb 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1014f3 [0x48, 0x8D, 0x74, 0x24, 0x50] (fun s => s.RIP = 0x1014f3) (leaR64Effect 0x1014f3 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1014f3 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x1014f3 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1014f8 [0x48, 0x8D, 0x54, 0x24, 0x78] (fun s => s.RIP = 0x1014f8) (leaR64Effect 0x1014f8 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1014f8 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x1014f8 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1014fd [0xE8, 0x6E, 0x21, 0x00, 0x00] (PushPre 0x1014fd 5) (callEffect (fun _ => 0x103670) 0x101502)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1014fd 0x103670 0x101502).toInstrSpec (call_rel32_effect_step 0x1014fd 0x216e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014f3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014f8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014fd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103670) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1014eb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1014eb :=
  Rest.liftedBlock (rest_l1014eb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1014eb x hx)

theorem rest_l101502 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101502 bytes_l101502) (entryMap (live .l101502))
      2 0x101502 bytes_l101502 b_l101502 := by
  have f0 : InstrSpec 0x101502 [0x83, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x02] (LoadPre 0x101502 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x101502 + BitVec.ofNat 64 8)) 4) (cmpMImm8Effect 0x101502 8 32 (.sib 4 none 0 (.d32 0x88)) 0x2)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x101502 8 (.sib 4 none 0 (.d32 0x88)) 0x2).toInstrSpec (cmp_m32_imm8_effect_step 0x101502 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x2) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10150a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10150a 5 0x114) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101502 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101502 :=
  Rest.liftedBlock (rest_l101502 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101502 x hx)

theorem rest_l101510 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101510 bytes_l101510) (entryMap (live .l101510))
      2 0x101510 bytes_l101510 b_l101510 := by
  have f0 : InstrSpec 0x101510 [0xF6, 0x44, 0x24, 0x70, 0x01] (LoadPre 0x101510 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x101510 + BitVec.ofNat 64 5)) 1) (testM8Imm8Effect 0x101510 5 (.sib 4 none 0 (.d8 0x70)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (testM8Imm8Effect_footprint 0x101510 5 (.sib 4 none 0 (.d8 0x70)) 0x1).toInstrSpec (test_m8_imm8_effect_step 0x101510 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101515) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x101515 5 0x109) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101510 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101510 :=
  Rest.liftedBlock (rest_l101510 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101510 x hx)

theorem rest_l10151b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10151b bytes_l10151b) (entryMap (live .l10151b))
      3 0x10151b bytes_l10151b b_l10151b := by
  have f0 : InstrSpec 0x10151b [0x8B, 0x44, 0x24, 0x68] (LoadPre 0x10151b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10151b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10151b 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x10151b 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r32_m32_low_effect_step 0x10151b 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10151f [0x3B, 0x44, 0x24, 0x6C] (LoadPre 0x10151f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x10151f + BitVec.ofNat 64 4)) 4) (cmpR32M32Effect 0x10151f 4 0 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (cmpR32M32Effect_footprint 0x10151f 4 0 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (cmp_r32_m32_effect_step 0x10151f 0 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10151f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101523) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel32_effect_step 0x101523 7 0xfb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10151b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10151b :=
  Rest.liftedBlock (rest_l10151b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10151b x hx)

theorem rest_l101529 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101529 bytes_l101529) (entryMap (live .l101529))
      8 0x101529 bytes_l101529 b_l101529 := by
  have f0 : InstrSpec 0x101529 [0x4C, 0x8B, 0xAC, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x101529 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x101529 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101529 13 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x101529 13 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x101529 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101531 [0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x101531 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x101531 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101531 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101531 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x101531 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101539 [0x49, 0x83, 0xFD, 0x21] (fun s => s.RIP = 0x101539) (cmpR64Imm8Effect 0x101539 13 0x21)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x101539 13 0x21).toInstrSpec (cmp_r64_imm8_effect_step 0x101539 0x49 0xfd 0x21 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10153d [0x0F, 0x93, 0xC1] (fun s => s.RIP = 0x10153d) (atFlags (condHolds 3) (setccR8Effect 0x10153d 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x10153d 3 1 3).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x10153d 3 0xc1 (by decide) (by decide) c)) pre_rip
  have f4 : InstrSpec 0x101540 [0x48, 0x83, 0xF8, 0x21] (fun s => s.RIP = 0x101540) (cmpR64Imm8Effect 0x101540 0 0x21)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x101540 0 0x21).toInstrSpec (cmp_r64_imm8_effect_step 0x101540 0x48 0xf8 0x21 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101544 [0x0F, 0x93, 0xC2] (fun s => s.RIP = 0x101544) (atFlags (condHolds 3) (setccR8Effect 0x101544 3 2))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .rip] :=
    (setccR8Effect_footprint 0x101544 3 2 3).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x101544 3 0xc2 (by decide) (by decide) c)) pre_rip
  have f6 : InstrSpec 0x101547 [0x08, 0xCA] (fun s => s.RIP = 0x101547) (orR8R8Effect 0x101547 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (orR8R8Effect_footprint 0x101547 2 2 1).toInstrSpec (or_r8_r8_effect_step 0x101547 0xca (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101531) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101539) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10153d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101540) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101544) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 59), (2, 63), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101547) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 59), (2, 65), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101549) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 68) (jcc_rel32_effect_step 0x101549 5 0xd5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101529 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101529 :=
  Rest.liftedBlock (rest_l101529 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101529 x hx)

theorem rest_l10154f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10154f bytes_l10154f) (entryMap (live .l10154f))
      3 0x10154f bytes_l10154f b_l10154f := by
  have f0 : InstrSpec 0x10154f [0x48, 0x8B, 0xAC, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x10154f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10154f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10154f 5 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10154f 5 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x10154f 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101557 [0x4C, 0x29, 0xFD] (fun s => s.RIP = 0x101557) (subR64R64Effect 0x101557 5 15)
      [.gpr 5, .gpr 15] [] [.reg 5, .flags, .rip] :=
    (subR64R64Effect_footprint 0x101557 5 15).toInstrSpec (sub_r64_r64_effect_step 0x101557 0x4c 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101557) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10155a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel32_effect_step 0x10155a 2 0xc4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10154f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10154f :=
  Rest.liftedBlock (rest_l10154f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10154f x hx)

theorem rest_l101560 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101560 bytes_l101560) (entryMap (live .l101560))
      2 0x101560 bytes_l101560 b_l101560 := by
  have f0 : InstrSpec 0x101560 [0x49, 0x01, 0xED] (fun s => s.RIP = 0x101560) (addR64R64Effect 0x101560 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101560 13 5).toInstrSpec (add_r64_r64_effect_step 0x101560 0x49 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (16, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101563) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x101563 2 0xbb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101560 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101560 :=
  Rest.liftedBlock (rest_l101560 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101560 x hx)

theorem rest_l101569 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101569 bytes_l101569) (entryMap (live .l101569))
      3 0x101569 bytes_l101569 b_l101569 := by
  have f0 : InstrSpec 0x101569 [0x4C, 0x8B, 0xA4, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x101569 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x101569 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101569 12 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x101569 12 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x101569 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101571 [0x4D, 0x29, 0xFC] (fun s => s.RIP = 0x101571) (subR64R64Effect 0x101571 12 15)
      [.gpr 12, .gpr 15] [] [.reg 12, .flags, .rip] :=
    (subR64R64Effect_footprint 0x101571 12 15).toInstrSpec (sub_r64_r64_effect_step 0x101571 0x4d 0xfc (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101571) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101574) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel32_effect_step 0x101574 2 0xaa) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101569 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101569 :=
  Rest.liftedBlock (rest_l101569 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101569 x hx)

theorem rest_l10157a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10157a bytes_l10157a) (entryMap (live .l10157a))
      2 0x10157a bytes_l10157a b_l10157a := by
  have f0 : InstrSpec 0x10157a [0x4C, 0x01, 0xE0] (fun s => s.RIP = 0x10157a) (addR64R64Effect 0x10157a 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10157a 0 12).toInstrSpec (add_r64_r64_effect_step 0x10157a 0x4c 0xe0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10157d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x10157d 2 0xa1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10157a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10157a :=
  Rest.liftedBlock (rest_l10157a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10157a x hx)

theorem rest_l101583 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101583 bytes_l101583) (entryMap (live .l101583))
      2 0x101583 bytes_l101583 b_l101583 := by
  have f0 : InstrSpec 0x101583 [0x4C, 0x39, 0xF0] (fun s => s.RIP = 0x101583) (cmpR64R64Effect 0x101583 0 14)
      [.gpr 0, .gpr 14] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x101583 0 14).toInstrSpec (cmp_r64_r64_effect_step 0x101583 0x4c 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101586) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x101586 5 0x98) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101583 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101583 :=
  Rest.liftedBlock (rest_l101583 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101583 x hx)

theorem rest_l10158c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10158c bytes_l10158c) (entryMap (live .l10158c))
      12 0x10158c bytes_l10158c b_l10158c := by
  have f0 : InstrSpec 0x10158c [0xC6, 0x44, 0x24, 0x48, 0x00] (StorePre 0x10158c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10158c + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x10158c (.sib 4 none 0 (.d8 0x48)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x10158c (.sib 4 none 0 (.d8 0x48)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x10158c (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x101591 [0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101591 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101591 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x101591 (.sib 4 none 0 (.d8 0x40)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101591 (.sib 4 none 0 (.d8 0x40)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101591 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10159a [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10159a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10159a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10159a (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10159a (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10159a 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1015a3 [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1015a3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1015a3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1015a3 (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1015a3 (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1015a3 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1015ac [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1015ac 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1015ac + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1015ac (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1015ac (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1015ac 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1015b5 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1015b5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1015b5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1015b5 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1015b5 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1015b5 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1015be [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1015be 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1015be + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1015be (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1015be (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1015be 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1015c7 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1015c7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1015c7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1015c7 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1015c7 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1015c7 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1015d0 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1015d0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1015d0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1015d0 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1015d0 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1015d0 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1015d9 [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1015d9 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1015d9 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1015d9 (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1015d9 (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1015d9 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1015e1 [0x49, 0x83, 0xFE, 0x4A] (fun s => s.RIP = 0x1015e1) (cmpR64Imm8Effect 0x1015e1 14 0x4a)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1015e1 14 0x4a).toInstrSpec (cmp_r64_imm8_effect_step 0x1015e1 0x49 0xfe 0x4a (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101591) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10159a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015a3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015ac) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015b5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015be) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015c7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015d0) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015d9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015e1) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015e5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 65) (jcc_rel8_effect_step 0x1015e5 3 0x61) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10158c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10158c :=
  Rest.liftedBlock (rest_l10158c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10158c x hx)

theorem rest_l1015e7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1015e7 bytes_l1015e7) (entryMap (live .l1015e7))
      6 0x1015e7 bytes_l1015e7 b_l1015e7 := by
  have f0 : InstrSpec 0x1015e7 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x1015e7) (movR64R64Effect 0x1015e7 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1015e7 7 4).toInstrSpec (mov_r64_r64_effect_step 0x1015e7 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1015ea [0x48, 0x8D, 0x05, 0x2F, 0x92, 0x02, 0x00] (fun s => s.RIP = 0x1015ea) (leaR64Effect 0x1015ea 0 (.rip 0x2922f))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1015ea 0 (.rip 0x2922f)).toInstrSpec (lea_r64_effect_step 0x1015ea 0x48 (by decide) 0 (.rip 0x2922f) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1015f1 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x1015f1) (movR64R64Effect 0x1015f1 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1015f1 6 15).toInstrSpec (mov_r64_r64_effect_step 0x1015f1 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1015f4 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x1015f4) (movR64R64Effect 0x1015f4 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1015f4 2 14).toInstrSpec (mov_r64_r64_effect_step 0x1015f4 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1015f7 [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x1015f7) (movR64R64Effect 0x1015f7 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1015f7 15 0).toInstrSpec (mov_r64_r64_effect_step 0x1015f7 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1015fa [0xFF, 0xD0] (GoesTo (CallPre 0x1015fa 2 (fun s => (Operand.reg 0 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 0 : Operand 64).read s) 0x1015fc) 0x12a820) (callEffect (fun s => (Operand.reg 0 : Operand 64).read s) 0x1015fc)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x1015fa 0 0x1015fc).toInstrSpec (call_r64_effect_step 0x1015fa 0xd0 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 0 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015ea) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015f1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015f4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015f7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1015fa) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (2, 59), (3, 3), (4, 63), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f5 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l1015e7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1015e7 :=
  Rest.liftedBlock (rest_l1015e7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1015e7 x hx)

theorem rest_l1015fc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1015fc bytes_l1015fc) (entryMap (live .l1015fc))
      4 0x1015fc bytes_l1015fc b_l1015fc := by
  have f0 : InstrSpec 0x1015fc [0x48, 0x8D, 0x7B, 0x28] (fun s => s.RIP = 0x1015fc) (leaR64Effect 0x1015fc 7 (.base 3 (.d8 0x28)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1015fc 7 (.base 3 (.d8 0x28))).toInstrSpec (lea_r64_effect_step 0x1015fc 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101600 [0xBA, 0x49, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101600) (movR32Imm32Effect 0x101600 5 2 0x49)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x101600 5 2 0x49).toInstrSpec (mov_r32_imm32_effect_step 0x101600 0xba (by decide) 0x49) pre_rip
  have f2 : InstrSpec 0x101605 [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x101605) (movR64R64Effect 0x101605 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101605 6 4).toInstrSpec (mov_r64_r64_effect_step 0x101605 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101608 [0x41, 0xFF, 0xD7] (GoesTo (CallPre 0x101608 3 (fun s => (Operand.reg 15 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x10160b) 0x12a820) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x10160b)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x101608 15 0x10160b).toInstrSpec (call_r64_rex_effect_step 0x101608 0x41 0xd7 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 15 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101600) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101605) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101608) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1015fc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1015fc :=
  Rest.liftedBlock (rest_l1015fc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1015fc x hx)

theorem rest_l10160b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10160b bytes_l10160b) (entryMap (live .l10160b))
      6 0x10160b bytes_l10160b b_l10160b := by
  have f0 : InstrSpec 0x10160b [0x48, 0x89, 0x6B, 0x08] (StorePre 0x10160b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10160b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10160b 5 (.base 3 (.d8 0x8)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10160b 5 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10160b 0x48 (by decide) 5 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10160f [0x4C, 0x89, 0x6B, 0x10] (StorePre 0x10160f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10160f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10160f 13 (.base 3 (.d8 0x10)))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10160f 13 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10160f 0x4c (by decide) 5 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x101613 [0x4C, 0x89, 0x63, 0x18] (StorePre 0x101613 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x101613 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101613 12 (.base 3 (.d8 0x18)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101613 12 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x101613 0x4c (by decide) 4 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101617 [0x4C, 0x89, 0x73, 0x20] (StorePre 0x101617 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x101617 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101617 14 (.base 3 (.d8 0x20)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101617 14 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x101617 0x4c (by decide) 6 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10161b [0x48, 0xC7, 0x03, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10161b 7 (fun s => AddrMode.addr (.base 3 .none) s (0x10161b + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x10161b (.base 3 .none) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10161b (.base 3 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10161b 0x48 (by decide) (.base 3 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10160f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101613) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101617) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10161b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101622) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 58) (jmp_rel8_effect_step 0x101622 0xf (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10160b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10160b :=
  Rest.liftedBlock (rest_l10160b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10160b x hx)

theorem rest_l101624 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101624 bytes_l101624) (entryMap (live .l101624))
      2 0x101624 bytes_l101624 b_l101624 := by
  have f0 : InstrSpec 0x101624 [0x48, 0xC7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101624 8 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x101624 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x101624 (.base 3 (.d8 0x8)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101624 (.base 3 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101624 0x48 (by decide) (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10162c [0x48, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00] (StorePre 0x10162c 7 (fun s => AddrMode.addr (.base 3 .none) s (0x10162c + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x10162c (.base 3 .none) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10162c (.base 3 .none) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x10162c 0x48 (by decide) (.base 3 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10162c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101633) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l101624 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101624 :=
  Rest.liftedBlock (rest_l101624 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101624 x hx)

theorem rest_l101633 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101633 bytes_l101633) (entryMap (live .l101633))
      9 0x101633 bytes_l101633 b_l101633 := by
  have f0 : InstrSpec 0x101633 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x101633) (movR64R64Effect 0x101633 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101633 0 3).toInstrSpec (mov_r64_r64_effect_step 0x101633 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101636 [0x48, 0x81, 0xC4, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101636) (addR64Imm32Effect 0x101636 4 0xf8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x101636 4 0xf8).toInstrSpec (add_r64_imm32_effect_step 0x101636 0x48 0xc4 0xf8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10163d [0x5B] (PopPre 0x10163d) (popR64Effect 0x10163d 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10163d 1 3).toInstrSpec (pop_r64_effect_step 0x10163d 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10163e [0x41, 0x5C] (PopPre 0x10163e) (popR64Effect 0x10163e 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10163e 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10163e 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101640 [0x41, 0x5D] (PopPre 0x101640) (popR64Effect 0x101640 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101640 2 13).toInstrSpec (pop_r64_rex_effect_step 0x101640 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101642 [0x41, 0x5E] (PopPre 0x101642) (popR64Effect 0x101642 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101642 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101642 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x101644 [0x41, 0x5F] (PopPre 0x101644) (popR64Effect 0x101644 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101644 2 15).toInstrSpec (pop_r64_rex_effect_step 0x101644 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x101646 [0x5D] (PopPre 0x101646) (popR64Effect 0x101646 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101646 1 5).toInstrSpec (pop_r64_effect_step 0x101646 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x101647 [0xC3] (RetPre 0x101647) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101647).toInstrSpec (ret_effect_step 0x101647) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101636) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10163d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10163e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101640) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101642) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101644) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101646) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101647) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l101633 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101633 :=
  Rest.liftedBlock (rest_l101633 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101633 x hx)

theorem rest_l101648 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101648 bytes_l101648) (entryMap (live .l101648))
      5 0x101648 bytes_l101648 b_l101648 := by
  have f0 : InstrSpec 0x101648 [0xBA, 0x49, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101648) (movR32Imm32Effect 0x101648 5 2 0x49)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x101648 5 2 0x49).toInstrSpec (mov_r32_imm32_effect_step 0x101648 0xba (by decide) 0x49) pre_rip
  have f1 : InstrSpec 0x10164d [0x31, 0xFF] (fun s => s.RIP = 0x10164d) (xorR32R32Effect 0x10164d 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10164d 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x10164d 0xff (by decide)) pre_rip
  have f2 : InstrSpec 0x10164f [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10164f) (movR64R64Effect 0x10164f 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10164f 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10164f 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101652 [0x48, 0xC7, 0xC1, 0xF8, 0x20, 0x20, 0x00] (fun s => s.RIP = 0x101652) (movR64Imm32Effect 0x101652 1 0x2020f8)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x101652 1 0x2020f8).toInstrSpec (mov_r64_imm32_effect_step 0x101652 0x48 0xc1 (by decide) (by decide) (by decide) 0x2020f8) pre_rip
  have f4 : InstrSpec 0x101659 [0xE8, 0x02, 0x85, 0x02, 0x00] (PushPre 0x101659 5) (callEffect (fun _ => 0x129b60) 0x10165e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101659 0x129b60 0x10165e).toInstrSpec (call_rel32_effect_step 0x101659 0x28502 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (4, 4), (5, 5), (7, 7), (14, 14)]) (p' := 0x10164d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (4, 4), (5, 5), (7, 55), (14, 14)]) (p' := 0x10164f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 53), (4, 4), (5, 5), (6, 57), (7, 55), (14, 14)]) (p' := 0x101652) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (2, 53), (4, 4), (5, 5), (6, 57), (7, 55), (14, 14)]) (p' := 0x101659) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 59), (2, 53), (4, 61), (5, 5), (6, 57), (7, 55), (14, 14)]) (p' := 0x129b60) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l101648 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101648 :=
  Rest.liftedBlock (rest_l101648 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101648 x hx)

theorem rest_l10165e_1 [Bindings] (code : CodeMap) :
    Rest (n := 87) code lifted (codeRange 0x10165e bytes_l10165e) [(0, 81), (1, 83), (2, 2), (3, 73), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x1016a9 bytes_l10165e_1 b_l10165e_1 := by
  have f20 : InstrSpec 0x1016a9 [0x4C, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1016a9) (leaR64Effect 0x1016a9 15 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x1016a9 15 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x1016a9 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1016b1 [0x48, 0x8D, 0x74, 0x24, 0x58] (fun s => s.RIP = 0x1016b1) (leaR64Effect 0x1016b1 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1016b1 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (lea_r64_effect_step 0x1016b1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x1016b6 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x1016b6) (movR64R64Effect 0x1016b6 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1016b6 7 15).toInstrSpec (mov_r64_r64_effect_step 0x1016b6 0x4c 0xff (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x1016b9 [0xE8, 0xA2, 0x87, 0x00, 0x00] (PushPre 0x1016b9 5) (callEffect (fun _ => 0x109e60) 0x1016be)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1016b9 0x109e60 0x1016be).toInstrSpec (call_rel32_effect_step 0x1016b9 0x87a2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f20 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016b1) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 69), (5, 5), (6, 89), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016b6) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f22 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 69), (5, 5), (6, 89), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016b9) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f23 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 93), (5, 5), (6, 89), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e60) f23 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 95) (by decide) (by decide) rfl rfl

theorem rest_l10165e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10165e bytes_l10165e) (entryMap (live .l10165e))
      24 0x10165e bytes_l10165e b_l10165e := by
  have f0 : InstrSpec 0x10165e [0x66, 0x90] (fun s => s.RIP = 0x10165e) (fun _ => nopEffect 0x10165e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10165e 2).toInstrSpec (nop_66_effect_step 0x10165e) pre_rip
  have f1 : InstrSpec 0x101660 [0x55] (PushPre 0x101660 1) (pushR64Effect 0x101660 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101660 1 5).toInstrSpec (push_r64_effect_step 0x101660 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101661 [0x41, 0x57] (PushPre 0x101661 2) (pushR64Effect 0x101661 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101661 2 15).toInstrSpec (push_r64_rex_effect_step 0x101661 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101663 [0x41, 0x56] (PushPre 0x101663 2) (pushR64Effect 0x101663 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101663 2 14).toInstrSpec (push_r64_rex_effect_step 0x101663 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101665 [0x41, 0x55] (PushPre 0x101665 2) (pushR64Effect 0x101665 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101665 2 13).toInstrSpec (push_r64_rex_effect_step 0x101665 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101667 [0x41, 0x54] (PushPre 0x101667 2) (pushR64Effect 0x101667 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101667 2 12).toInstrSpec (push_r64_rex_effect_step 0x101667 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x101669 [0x53] (PushPre 0x101669 1) (pushR64Effect 0x101669 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101669 1 3).toInstrSpec (push_r64_effect_step 0x101669 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x10166a [0x48, 0x81, 0xEC, 0x00, 0x10, 0x00, 0x00] (fun s => s.RIP = 0x10166a) (subR64Imm32Effect 0x10166a 4 0x1000)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10166a 4 0x1000).toInstrSpec (sub_r64_imm32_effect_step 0x10166a 0x48 0xec 0x1000 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101671 [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101671 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101671 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x101671 (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101671 (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101671 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101679 [0x48, 0x81, 0xEC, 0xD8, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x101679) (subR64Imm32Effect 0x101679 4 0x7d8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x101679 4 0x7d8).toInstrSpec (sub_r64_imm32_effect_step 0x101679 0x48 0xec 0x7d8 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101680 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x101680) (movR64R64Effect 0x101680 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101680 14 2).toInstrSpec (mov_r64_r64_effect_step 0x101680 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101683 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x101683) (movR64R64Effect 0x101683 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x101683 3 7).toInstrSpec (mov_r64_r64_effect_step 0x101683 0x48 0xfb (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101686 [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x101686 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x101686 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101686 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101686 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101686 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10168a [0x48, 0x89, 0x44, 0x24, 0x70] (StorePre 0x10168a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10168a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10168a 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10168a 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x10168a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x10168f [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x10168f (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10168f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10168f 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10168f 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10168f 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x101693 [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x101693 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101693 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101693 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101693 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x101693 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x101698 [0x48, 0x8B, 0x06] (LoadPre 0x101698 (fun s => AddrMode.addr (.base 6 .none) s (0x101698 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101698 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101698 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x101698 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10169b [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x10169b (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10169b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10169b 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10169b 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10169b 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x10169f [0x48, 0x89, 0x4C, 0x24, 0x60] (StorePre 0x10169f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10169f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10169f 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10169f 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x10169f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1016a4 [0x48, 0x89, 0x44, 0x24, 0x58] (StorePre 0x1016a4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1016a4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1016a4 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1016a4 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x1016a4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101660) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101661) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101663) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101665) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101667) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 2), (3, 3), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101669) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 2), (3, 3), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10166a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101671) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101679) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 2), (3, 3), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101680) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 2), (3, 3), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101683) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(2, 2), (3, 73), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101686) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (2, 2), (3, 73), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10168a) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (2, 2), (3, 73), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10168f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (2, 2), (3, 73), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101693) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (2, 2), (3, 73), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101698) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (2, 2), (3, 73), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10169b) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10169f) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016a4) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 81), (1, 83), (2, 2), (3, 73), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016a9) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10165e_1 code

theorem block_l10165e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10165e :=
  Rest.liftedBlock (rest_l10165e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10165e x hx)

theorem rest_l1016be [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1016be bytes_l1016be) (entryMap (live .l1016be))
      11 0x1016be bytes_l1016be b_l1016be := by
  have f0 : InstrSpec 0x1016be [0x48, 0xC7, 0x84, 0x24, 0xF0, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1016be 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f0)) s (0x1016be + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1016be (.sib 4 none 0 (.d32 0x8f0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1016be (.sib 4 none 0 (.d32 0x8f0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1016be 0x48 (by decide) (.sib 4 none 0 (.d32 0x8f0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1016ca [0x48, 0xC7, 0x84, 0x24, 0xE8, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1016ca 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8e8)) s (0x1016ca + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1016ca (.sib 4 none 0 (.d32 0x8e8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1016ca (.sib 4 none 0 (.d32 0x8e8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1016ca 0x48 (by decide) (.sib 4 none 0 (.d32 0x8e8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1016d6 [0x48, 0xC7, 0x84, 0x24, 0xE0, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1016d6 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8e0)) s (0x1016d6 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1016d6 (.sib 4 none 0 (.d32 0x8e0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1016d6 (.sib 4 none 0 (.d32 0x8e0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1016d6 0x48 (by decide) (.sib 4 none 0 (.d32 0x8e0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1016e2 [0x48, 0xC7, 0x84, 0x24, 0xD8, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1016e2 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8d8)) s (0x1016e2 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1016e2 (.sib 4 none 0 (.d32 0x8d8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1016e2 (.sib 4 none 0 (.d32 0x8d8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1016e2 0x48 (by decide) (.sib 4 none 0 (.d32 0x8d8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1016ee [0x8B, 0xAC, 0x24, 0x78, 0x01, 0x00, 0x00] (LoadPre 0x1016ee (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x1016ee + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1016ee 5 (.sib 4 none 0 (.d32 0x178)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x1016ee 5 (.sib 4 none 0 (.d32 0x178))).toInstrSpec (mov_r32_m32_low_effect_step 0x1016ee 5 (.sib 4 none 0 (.d32 0x178)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1016f5 [0x4C, 0x8D, 0xA4, 0x24, 0x98, 0x0C, 0x00, 0x00] (fun s => s.RIP = 0x1016f5) (leaR64Effect 0x1016f5 12 (.sib 4 none 0 (.d32 0xc98)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x1016f5 12 (.sib 4 none 0 (.d32 0xc98))).toInstrSpec (lea_r64_effect_step 0x1016f5 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xc98)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1016fd [0x48, 0x8D, 0xB4, 0x24, 0xD8, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x1016fd) (leaR64Effect 0x1016fd 6 (.sib 4 none 0 (.d32 0x8d8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1016fd 6 (.sib 4 none 0 (.d32 0x8d8))).toInstrSpec (lea_r64_effect_step 0x1016fd 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x8d8)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101705 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x101705) (movR64R64Effect 0x101705 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101705 7 12).toInstrSpec (mov_r64_r64_effect_step 0x101705 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101708 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x101708) (movR64R64Effect 0x101708 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x101708 2 15).toInstrSpec (mov_r64_r64_effect_step 0x101708 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10170b [0x89, 0xE9] (fun s => s.RIP = 0x10170b) (movR32R32Effect 0x10170b 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10170b 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x10170b 0xe9 (by decide)) pre_rip
  have f10 : InstrSpec 0x10170d [0xE8, 0x0E, 0x8B, 0x00, 0x00] (PushPre 0x10170d 5) (callEffect (fun _ => 0x10a220) 0x101712)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10170d 0x10a220 0x101712).toInstrSpec (call_rel32_effect_step 0x10170d 0x8b0e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016ca) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016d6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016e2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016ee) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016f5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 57), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1016fd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 57), (6, 61), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101705) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101708) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 65), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10170b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 67), (2, 65), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10170d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 67), (2, 65), (3, 3), (4, 69), (5, 57), (6, 61), (7, 63), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a220) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l1016be [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1016be :=
  Rest.liftedBlock (rest_l1016be code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1016be x hx)

theorem rest_l101712 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101712 bytes_l101712) (entryMap (live .l101712))
      7 0x101712 bytes_l101712 b_l101712 := by
  have f0 : InstrSpec 0x101712 [0x48, 0xC7, 0x84, 0x24, 0x70, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101712 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1070)) s (0x101712 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101712 (.sib 4 none 0 (.d32 0x1070)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101712 (.sib 4 none 0 (.d32 0x1070)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101712 0x48 (by decide) (.sib 4 none 0 (.d32 0x1070)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10171e [0x48, 0xC7, 0x84, 0x24, 0x68, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10171e 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1068)) s (0x10171e + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10171e (.sib 4 none 0 (.d32 0x1068)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10171e (.sib 4 none 0 (.d32 0x1068)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10171e 0x48 (by decide) (.sib 4 none 0 (.d32 0x1068)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10172a [0x48, 0xC7, 0x84, 0x24, 0x60, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10172a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1060)) s (0x10172a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10172a (.sib 4 none 0 (.d32 0x1060)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10172a (.sib 4 none 0 (.d32 0x1060)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10172a 0x48 (by decide) (.sib 4 none 0 (.d32 0x1060)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101736 [0x48, 0xC7, 0x84, 0x24, 0x58, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101736 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1058)) s (0x101736 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101736 (.sib 4 none 0 (.d32 0x1058)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101736 (.sib 4 none 0 (.d32 0x1058)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101736 0x48 (by decide) (.sib 4 none 0 (.d32 0x1058)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101742 [0x48, 0x8D, 0xB4, 0x24, 0x58, 0x10, 0x00, 0x00] (fun s => s.RIP = 0x101742) (leaR64Effect 0x101742 6 (.sib 4 none 0 (.d32 0x1058)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101742 6 (.sib 4 none 0 (.d32 0x1058))).toInstrSpec (lea_r64_effect_step 0x101742 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x1058)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10174a [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x10174a) (movR64R64Effect 0x10174a 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10174a 7 12).toInstrSpec (mov_r64_r64_effect_step 0x10174a 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10174d [0xE8, 0x2E, 0x8B, 0x00, 0x00] (PushPre 0x10174d 5) (callEffect (fun _ => 0x10a280) 0x101752)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10174d 0x10a280 0x101752).toInstrSpec (call_rel32_effect_step 0x10174d 0x8b2e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10171e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10172a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101736) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101742) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10174a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10174d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (3, 3), (4, 61), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a280) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l101712 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101712 :=
  Rest.liftedBlock (rest_l101712 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101712 x hx)

theorem rest_l101752 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101752 bytes_l101752) (entryMap (live .l101752))
      4 0x101752 bytes_l101752 b_l101752 := by
  have f0 : InstrSpec 0x101752 [0xF6, 0xD0] (fun s => s.RIP = 0x101752) (notR8Effect 0x101752 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x101752 2 0).toInstrSpec (not_r8_effect_step 0x101752 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101754 [0x24, 0x01] (fun s => s.RIP = 0x101754) (andAlImm8Effect 0x101754 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x101754 0x1).toInstrSpec (and_al_imm8_effect_step 0x101754 0x1) pre_rip
  have f2 : InstrSpec 0x101756 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x101756) (movzxR32R8Effect 0x101756 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x101756 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x101756 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101759 [0xE8, 0xF2, 0x65, 0x02, 0x00] (PushPre 0x101759 5) (callEffect (fun _ => 0x127d50) 0x10175e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101759 0x127d50 0x10175e).toInstrSpec (call_rel32_effect_step 0x101759 0x265f2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101754) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101756) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101759) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101752 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101752 :=
  Rest.liftedBlock (rest_l101752 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101752 x hx)

theorem rest_l10175e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10175e bytes_l10175e) (entryMap (live .l10175e))
      11 0x10175e bytes_l10175e b_l10175e := by
  have f0 : InstrSpec 0x10175e [0x48, 0x8B, 0x8C, 0x24, 0x98, 0x0C, 0x00, 0x00] (LoadPre 0x10175e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc98)) s (0x10175e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10175e 1 (.sib 4 none 0 (.d32 0xc98)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10175e 1 (.sib 4 none 0 (.d32 0xc98))).toInstrSpec (mov_r64_m64_effect_step 0x10175e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xc98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101766 [0x48, 0x8B, 0x94, 0x24, 0xA0, 0x0C, 0x00, 0x00] (LoadPre 0x101766 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca0)) s (0x101766 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101766 2 (.sib 4 none 0 (.d32 0xca0)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x101766 2 (.sib 4 none 0 (.d32 0xca0))).toInstrSpec (mov_r64_m64_effect_step 0x101766 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xca0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10176e [0x48, 0x89, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x10176e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10176e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10176e 1 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10176e 1 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x10176e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101776 [0x48, 0x89, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x101776 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x101776 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101776 2 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101776 2 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x101776 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10177e [0x48, 0x8B, 0x8C, 0x24, 0xA8, 0x0C, 0x00, 0x00] (LoadPre 0x10177e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca8)) s (0x10177e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10177e 1 (.sib 4 none 0 (.d32 0xca8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10177e 1 (.sib 4 none 0 (.d32 0xca8))).toInstrSpec (mov_r64_m64_effect_step 0x10177e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xca8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101786 [0x48, 0x89, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x101786 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x101786 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101786 1 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101786 1 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x101786 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10178e [0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x0C, 0x00, 0x00] (LoadPre 0x10178e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcb0)) s (0x10178e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10178e 1 (.sib 4 none 0 (.d32 0xcb0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10178e 1 (.sib 4 none 0 (.d32 0xcb0))).toInstrSpec (mov_r64_m64_effect_step 0x10178e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xcb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x101796 [0x48, 0x89, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x101796 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x101796 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101796 1 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101796 1 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x101796 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10179e [0x40, 0x20, 0xE8] (fun s => s.RIP = 0x10179e) (andR8R8Effect 0x10179e 3 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (andR8R8Effect_footprint 0x10179e 3 0 5).toInstrSpec (and_r8_r8_rex_effect_step 0x10179e 0x40 0xe8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1017a1 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x1017a1) (movzxR32R8Effect 0x1017a1 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x1017a1 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x1017a1 0xf8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1017a4 [0xE8, 0xA7, 0x65, 0x02, 0x00] (PushPre 0x1017a4 5) (callEffect (fun _ => 0x127d50) 0x1017a9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1017a4 0x127d50 0x1017a9).toInstrSpec (call_rel32_effect_step 0x1017a4 0x265a7 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101766) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10176e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101776) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10177e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101786) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 59), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10178e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101796) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10179e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017a1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017a4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 62), (2, 55), (3, 3), (4, 69), (5, 5), (6, 6), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l10175e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10175e :=
  Rest.liftedBlock (rest_l10175e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10175e x hx)

theorem rest_l1017a9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1017a9 bytes_l1017a9) (entryMap (live .l1017a9))
      2 0x1017a9 bytes_l1017a9 b_l1017a9 := by
  have f0 : InstrSpec 0x1017a9 [0x3C, 0x01] (fun s => s.RIP = 0x1017a9) (cmpAlImm8Effect 0x1017a9 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x1017a9 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x1017a9 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017ab) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1017ab 5 0x4ad) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1017a9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1017a9 :=
  Rest.liftedBlock (rest_l1017a9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1017a9 x hx)

theorem rest_l1017b1_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x1017b1 bytes_l1017b1) [(0, 74), (1, 76), (3, 3), (4, 4), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x10181e bytes_l1017b1_1 b_l1017b1_1 := by
  have f20 : InstrSpec 0x10181e [0xE8, 0x0D, 0xF7, 0x01, 0x00] (PushPre 0x10181e 5) (callEffect (fun _ => 0x120f30) 0x101823)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10181e 0x120f30 0x101823).toInstrSpec (call_rel32_effect_step 0x10181e 0x1f70d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 74), (1, 76), (3, 3), (4, 84), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f30) f20 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 86) (by decide) (by decide) rfl rfl

theorem rest_l1017b1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1017b1 bytes_l1017b1) (entryMap (live .l1017b1))
      21 0x1017b1 bytes_l1017b1 b_l1017b1 := by
  have f0 : InstrSpec 0x1017b1 [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x1017b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1017b1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1017b1 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1017b1 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x1017b1 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1017b9 [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x1017b9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1017b9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017b9 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017b9 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1017b9 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1017be [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x1017be (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1017be + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1017be 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1017be 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x1017be 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1017c6 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x1017c6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1017c6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017c6 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017c6 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1017c6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1017cb [0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x1017cb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1017cb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1017cb 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1017cb 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x1017cb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1017d3 [0x48, 0x8B, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x1017d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1017d3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1017d3 1 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1017d3 1 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x1017d3 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1017db [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x1017db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1017db + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017db 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017db 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1017db 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1017e0 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x1017e0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1017e0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017e0 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017e0 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1017e0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1017e5 [0x41, 0x0F, 0xB6, 0x46, 0x20] (LoadPre 0x1017e5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1017e5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1017e5 5 0 (.base 14 (.d8 0x20)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1017e5 5 0 (.base 14 (.d8 0x20))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1017e5 0x41 (by decide) 0 (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1017ea [0x88, 0x44, 0x24, 0x50] (StorePre 0x1017ea 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1017ea + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1017ea 4 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1017ea 4 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m8_r8_effect_step 0x1017ea 0 (by decide) (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1017ee [0x49, 0x8B, 0x46, 0x18] (LoadPre 0x1017ee (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1017ee + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1017ee 0 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1017ee 0 (.base 14 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1017ee 0x49 (by decide) 0 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1017f2 [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x1017f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1017f2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017f2 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017f2 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x1017f2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1017f7 [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x1017f7 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1017f7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1017f7 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1017f7 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1017f7 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1017fb [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x1017fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1017fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017fb 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1017fb 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1017fb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x101800 [0x49, 0x8B, 0x06] (LoadPre 0x101800 (fun s => AddrMode.addr (.base 14 .none) s (0x101800 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101800 0 (.base 14 .none))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101800 0 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x101800 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x101803 [0x49, 0x8B, 0x4E, 0x08] (LoadPre 0x101803 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x101803 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101803 1 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101803 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x101803 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x101807 [0x48, 0x89, 0x4C, 0x24, 0x38] (StorePre 0x101807 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x101807 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101807 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101807 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x101807 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x10180c [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x10180c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10180c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10180c 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10180c 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10180c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x101811 [0x48, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101811) (leaR64Effect 0x101811 7 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101811 7 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x101811 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x101819 [0x48, 0x8D, 0x74, 0x24, 0x30] (fun s => s.RIP = 0x101819) (leaR64Effect 0x101819 6 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101819 6 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x101819 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017b9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017be) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017c6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017cb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017d3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017db) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017e0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017e5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017ea) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017ee) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017f2) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017f7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1017fb) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101800) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101803) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 74), (1, 76), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101807) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 74), (1, 76), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10180c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 74), (1, 76), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101811) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 74), (1, 76), (3, 3), (4, 4), (5, 5), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101819) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 74), (1, 76), (3, 3), (4, 4), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10181e) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1017b1_1 code

theorem block_l1017b1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1017b1 :=
  Rest.liftedBlock (rest_l1017b1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1017b1 x hx)

theorem rest_l101823 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101823 bytes_l101823) (entryMap (live .l101823))
      2 0x101823 bytes_l101823 b_l101823 := by
  have f0 : InstrSpec 0x101823 [0x80, 0xBC, 0x24, 0xB0, 0x01, 0x00, 0x00, 0x01] (LoadPre 0x101823 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x101823 + BitVec.ofNat 64 8)) 1) (cmpM8Imm8Effect 0x101823 8 (.sib 4 none 0 (.d32 0x1b0)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x101823 8 (.sib 4 none 0 (.d32 0x1b0)) 0x1).toInstrSpec (cmp_m8_imm8_effect_step 0x101823 (.sib 4 none 0 (.d32 0x1b0)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10182b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10182b 5 0x42d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101823 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101823 :=
  Rest.liftedBlock (rest_l101823 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101823 x hx)

theorem rest_l101831 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101831 bytes_l101831) (entryMap (live .l101831))
      9 0x101831 bytes_l101831 b_l101831 := by
  have f0 : InstrSpec 0x101831 [0x48, 0x8D, 0x84, 0x24, 0x58, 0x10, 0x00, 0x00] (fun s => s.RIP = 0x101831) (leaR64Effect 0x101831 0 (.sib 4 none 0 (.d32 0x1058)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x101831 0 (.sib 4 none 0 (.d32 0x1058))).toInstrSpec (lea_r64_effect_step 0x101831 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1058)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101839 [0x48, 0x8D, 0xB4, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101839) (leaR64Effect 0x101839 6 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101839 6 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x101839 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101841 [0xB9, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101841) (movR32Imm32Effect 0x101841 5 1 0xb)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101841 5 1 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x101841 0xb9 (by decide) 0xb) pre_rip
  have f3 : InstrSpec 0x101846 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x101846) (movR64R64Effect 0x101846 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101846 7 0).toInstrSpec (mov_r64_r64_effect_step 0x101846 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101849 [0xF3, 0x48, 0xA5] (RepPre 0x101849 (RepMovsqPre 0x101849)) (repMovsqEffect 0x101849)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101849).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101849 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x10184c [0x4C, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10184c) (leaR64Effect 0x10184c 15 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x10184c 15 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x10184c 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101854 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x101854) (movR64R64Effect 0x101854 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101854 7 15).toInstrSpec (mov_r64_r64_effect_step 0x101854 0x4c 0xff (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101857 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x101857) (movR64R64Effect 0x101857 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101857 6 0).toInstrSpec (mov_r64_r64_effect_step 0x101857 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10185a [0xE8, 0xB1, 0xE1, 0x00, 0x00] (PushPre 0x10185a 5) (callEffect (fun _ => 0x10fa10) 0x10185f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10185a 0x10fa10 0x10185f).toInstrSpec (call_rel32_effect_step 0x10185a 0xe1b1 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101839) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101841) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101846) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101849) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10184c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101854) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101857) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10185a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa10) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l101831 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101831 :=
  Rest.liftedBlock (rest_l101831 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101831 x hx)

theorem rest_l10185f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10185f bytes_l10185f) (entryMap (live .l10185f))
      14 0x10185f bytes_l10185f b_l10185f := by
  have f0 : InstrSpec 0x10185f [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x10185f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10185f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10185f 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10185f 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10185f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101864 [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x101864 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101864 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101864 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101864 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101864 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101869 [0x48, 0x89, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00] (StorePre 0x101869 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x101869 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101869 0 (.sib 4 none 0 (.d32 0x1d0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101869 0 (.sib 4 none 0 (.d32 0x1d0))).toInstrSpec (mov_m64_r64_effect_step 0x101869 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1d0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101871 [0x48, 0x89, 0x8C, 0x24, 0xD8, 0x01, 0x00, 0x00] (StorePre 0x101871 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x101871 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101871 1 (.sib 4 none 0 (.d32 0x1d8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101871 1 (.sib 4 none 0 (.d32 0x1d8))).toInstrSpec (mov_m64_r64_effect_step 0x101871 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x1d8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101879 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x101879 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101879 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101879 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101879 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x101879 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10187e [0x48, 0x89, 0x84, 0x24, 0xE0, 0x01, 0x00, 0x00] (StorePre 0x10187e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x10187e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10187e 0 (.sib 4 none 0 (.d32 0x1e0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10187e 0 (.sib 4 none 0 (.d32 0x1e0))).toInstrSpec (mov_m64_r64_effect_step 0x10187e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1e0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101886 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x101886 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101886 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101886 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101886 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x101886 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10188b [0x48, 0x89, 0x84, 0x24, 0xE8, 0x01, 0x00, 0x00] (StorePre 0x10188b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x10188b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10188b 0 (.sib 4 none 0 (.d32 0x1e8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10188b 0 (.sib 4 none 0 (.d32 0x1e8))).toInstrSpec (mov_m64_r64_effect_step 0x10188b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x1e8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101893 [0x4C, 0x8D, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101893) (leaR64Effect 0x101893 14 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x101893 14 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (lea_r64_effect_step 0x101893 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10189b [0x4C, 0x8D, 0x2D, 0x7E, 0x8F, 0x02, 0x00] (fun s => s.RIP = 0x10189b) (leaR64Effect 0x10189b 13 (.rip 0x28f7e))
      [] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x10189b 13 (.rip 0x28f7e)).toInstrSpec (lea_r64_effect_step 0x10189b 0x4c (by decide) 5 (.rip 0x28f7e) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1018a2 [0xBA, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1018a2) (movR32Imm32Effect 0x1018a2 5 2 0x98)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1018a2 5 2 0x98).toInstrSpec (mov_r32_imm32_effect_step 0x1018a2 0xba (by decide) 0x98) pre_rip
  have f11 : InstrSpec 0x1018a7 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1018a7) (movR64R64Effect 0x1018a7 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1018a7 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1018a7 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1018aa [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x1018aa) (movR64R64Effect 0x1018aa 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1018aa 6 15).toInstrSpec (mov_r64_r64_effect_step 0x1018aa 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1018ad [0x41, 0xFF, 0xD5] (GoesTo (CallPre 0x1018ad 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x1018b0) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x1018b0)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x1018ad 13 0x1018b0).toInstrSpec (call_r64_rex_effect_step 0x1018ad 0x41 0xd5 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 13 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101864) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101869) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101871) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101879) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10187e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101886) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10188b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101893) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10189b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 62), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018a2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 55), (2, 69), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018a7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 55), (2, 69), (3, 3), (4, 4), (5, 5), (7, 71), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018aa) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 62), (1, 55), (2, 69), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018ad) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 62), (1, 55), (2, 69), (3, 3), (4, 75), (5, 5), (6, 73), (7, 71), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f13 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l10185f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10185f :=
  Rest.liftedBlock (rest_l10185f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10185f x hx)

theorem rest_l1018b0_3 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 159) code lifted (codeRange 0x1018b0 bytes_l1018b0) [(0, 53), (1, 157), (3, 3), (4, 4), (5, 5), (7, 155), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]
      11 0x101a05 bytes_l1018b0_3 b_l1018b0_3 := by
  have f60 : InstrSpec 0x101a05 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x101a05) (movR64Imm32Effect 0x101a05 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x101a05 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x101a05 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f61 : InstrSpec 0x101a0c [0xF3, 0x48, 0xA5] (RepPre 0x101a0c (RepMovsqPre 0x101a0c)) (repMovsqEffect 0x101a0c)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101a0c).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101a0c 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f62 : InstrSpec 0x101a0f [0x48, 0x8D, 0xBC, 0x24, 0xE0, 0x0F, 0x00, 0x00] (fun s => s.RIP = 0x101a0f) (leaR64Effect 0x101a0f 7 (.sib 4 none 0 (.d32 0xfe0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101a0f 7 (.sib 4 none 0 (.d32 0xfe0))).toInstrSpec (lea_r64_effect_step 0x101a0f 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xfe0)) (by decide) (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x101a17 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101a17) (movR32Imm32Effect 0x101a17 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101a17 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101a17 0xb9 (by decide) 0xf) pre_rip
  have f64 : InstrSpec 0x101a1c [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x101a1c) (movR64Imm32Effect 0x101a1c 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x101a1c 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x101a1c 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f65 : InstrSpec 0x101a23 [0xF3, 0x48, 0xA5] (RepPre 0x101a23 (RepMovsqPre 0x101a23)) (repMovsqEffect 0x101a23)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101a23).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101a23 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f66 : InstrSpec 0x101a26 [0x4C, 0x8D, 0xA4, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101a26) (leaR64Effect 0x101a26 12 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x101a26 12 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x101a26 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x101a2e [0xBA, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x101a2e) (movR32Imm32Effect 0x101a2e 5 2 0x3c0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x101a2e 5 2 0x3c0).toInstrSpec (mov_r32_imm32_effect_step 0x101a2e 0xba (by decide) 0x3c0) pre_rip
  have f68 : InstrSpec 0x101a33 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x101a33) (movR64R64Effect 0x101a33 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101a33 7 12).toInstrSpec (mov_r64_r64_effect_step 0x101a33 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x101a36 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x101a36) (movR64R64Effect 0x101a36 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101a36 6 0).toInstrSpec (mov_r64_r64_effect_step 0x101a36 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x101a39 [0x41, 0xFF, 0xD5] (GoesTo (CallPre 0x101a39 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a3c) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a3c)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x101a39 13 0x101a3c).toInstrSpec (call_r64_rex_effect_step 0x101a39 0x41 0xd5 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 13 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f60 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 53), (1, 157), (3, 3), (4, 4), (5, 5), (6, 159), (7, 155), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a0c) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.exec (n := 161) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a0f) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f62 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 162), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a17) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f63 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 53), (1, 164), (3, 3), (4, 4), (5, 5), (7, 162), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a1c) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f64 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 53), (1, 164), (3, 3), (4, 4), (5, 5), (6, 166), (7, 162), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a23) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.exec (n := 168) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a26) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f66 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a2e) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f67 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 53), (2, 171), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a33) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f68 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 53), (2, 171), (3, 3), (4, 4), (5, 5), (7, 173), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a36) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f69 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 53), (2, 171), (3, 3), (4, 4), (5, 5), (6, 175), (7, 173), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a39) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f70 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 53), (2, 171), (3, 3), (4, 177), (5, 5), (6, 175), (7, 173), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f70 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 179) (by decide) (by decide) rfl rfl

theorem rest_l1018b0_2 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 124) code lifted (codeRange 0x1018b0 bytes_l1018b0) [(0, 53), (1, 122), (3, 3), (4, 4), (5, 5), (7, 120), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]
      31 0x101992 bytes_l1018b0_2 b_l1018b0_2 := by
  have f40 : InstrSpec 0x101992 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x101992) (movR64Imm32Effect 0x101992 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x101992 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x101992 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f41 : InstrSpec 0x101999 [0xF3, 0x48, 0xA5] (RepPre 0x101999 (RepMovsqPre 0x101999)) (repMovsqEffect 0x101999)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101999).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101999 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f42 : InstrSpec 0x10199c [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x0D, 0x00, 0x00] (fun s => s.RIP = 0x10199c) (leaR64Effect 0x10199c 7 (.sib 4 none 0 (.d32 0xd88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10199c 7 (.sib 4 none 0 (.d32 0xd88))).toInstrSpec (lea_r64_effect_step 0x10199c 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xd88)) (by decide) (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x1019a4 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1019a4) (movR32Imm32Effect 0x1019a4 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1019a4 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1019a4 0xb9 (by decide) 0xf) pre_rip
  have f44 : InstrSpec 0x1019a9 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x1019a9) (movR64Imm32Effect 0x1019a9 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1019a9 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x1019a9 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f45 : InstrSpec 0x1019b0 [0xF3, 0x48, 0xA5] (RepPre 0x1019b0 (RepMovsqPre 0x1019b0)) (repMovsqEffect 0x1019b0)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1019b0).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1019b0 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f46 : InstrSpec 0x1019b3 [0x48, 0x8D, 0xBC, 0x24, 0x00, 0x0E, 0x00, 0x00] (fun s => s.RIP = 0x1019b3) (leaR64Effect 0x1019b3 7 (.sib 4 none 0 (.d32 0xe00)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1019b3 7 (.sib 4 none 0 (.d32 0xe00))).toInstrSpec (lea_r64_effect_step 0x1019b3 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xe00)) (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x1019bb [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1019bb) (movR32Imm32Effect 0x1019bb 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1019bb 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1019bb 0xb9 (by decide) 0xf) pre_rip
  have f48 : InstrSpec 0x1019c0 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x1019c0) (movR64Imm32Effect 0x1019c0 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1019c0 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x1019c0 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f49 : InstrSpec 0x1019c7 [0xF3, 0x48, 0xA5] (RepPre 0x1019c7 (RepMovsqPre 0x1019c7)) (repMovsqEffect 0x1019c7)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1019c7).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1019c7 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f50 : InstrSpec 0x1019ca [0x48, 0x8D, 0xBC, 0x24, 0x78, 0x0E, 0x00, 0x00] (fun s => s.RIP = 0x1019ca) (leaR64Effect 0x1019ca 7 (.sib 4 none 0 (.d32 0xe78)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1019ca 7 (.sib 4 none 0 (.d32 0xe78))).toInstrSpec (lea_r64_effect_step 0x1019ca 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xe78)) (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x1019d2 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1019d2) (movR32Imm32Effect 0x1019d2 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1019d2 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1019d2 0xb9 (by decide) 0xf) pre_rip
  have f52 : InstrSpec 0x1019d7 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x1019d7) (movR64Imm32Effect 0x1019d7 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1019d7 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x1019d7 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f53 : InstrSpec 0x1019de [0xF3, 0x48, 0xA5] (RepPre 0x1019de (RepMovsqPre 0x1019de)) (repMovsqEffect 0x1019de)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1019de).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1019de 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f54 : InstrSpec 0x1019e1 [0x48, 0x8D, 0xBC, 0x24, 0xF0, 0x0E, 0x00, 0x00] (fun s => s.RIP = 0x1019e1) (leaR64Effect 0x1019e1 7 (.sib 4 none 0 (.d32 0xef0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1019e1 7 (.sib 4 none 0 (.d32 0xef0))).toInstrSpec (lea_r64_effect_step 0x1019e1 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xef0)) (by decide) (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x1019e9 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1019e9) (movR32Imm32Effect 0x1019e9 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1019e9 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1019e9 0xb9 (by decide) 0xf) pre_rip
  have f56 : InstrSpec 0x1019ee [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x1019ee) (movR64Imm32Effect 0x1019ee 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1019ee 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x1019ee 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f57 : InstrSpec 0x1019f5 [0xF3, 0x48, 0xA5] (RepPre 0x1019f5 (RepMovsqPre 0x1019f5)) (repMovsqEffect 0x1019f5)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1019f5).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1019f5 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f58 : InstrSpec 0x1019f8 [0x48, 0x8D, 0xBC, 0x24, 0x68, 0x0F, 0x00, 0x00] (fun s => s.RIP = 0x1019f8) (leaR64Effect 0x1019f8 7 (.sib 4 none 0 (.d32 0xf68)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1019f8 7 (.sib 4 none 0 (.d32 0xf68))).toInstrSpec (lea_r64_effect_step 0x1019f8 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xf68)) (by decide) (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x101a00 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101a00) (movR32Imm32Effect 0x101a00 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101a00 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101a00 0xb9 (by decide) 0xf) pre_rip
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 53), (1, 122), (3, 3), (4, 4), (5, 5), (6, 124), (7, 120), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101999) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.exec (n := 126) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10199c) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f42 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 127), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019a4) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f43 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 53), (1, 129), (3, 3), (4, 4), (5, 5), (7, 127), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019a9) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f44 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 53), (1, 129), (3, 3), (4, 4), (5, 5), (6, 131), (7, 127), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019b0) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.exec (n := 133) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019b3) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f46 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 134), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019bb) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f47 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 53), (1, 136), (3, 3), (4, 4), (5, 5), (7, 134), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019c0) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f48 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 53), (1, 136), (3, 3), (4, 4), (5, 5), (6, 138), (7, 134), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019c7) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.exec (n := 140) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019ca) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f50 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 141), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019d2) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f51 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 53), (1, 143), (3, 3), (4, 4), (5, 5), (7, 141), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019d7) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f52 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 53), (1, 143), (3, 3), (4, 4), (5, 5), (6, 145), (7, 141), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019de) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.exec (n := 147) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019e1) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f54 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 148), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019e9) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f55 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 53), (1, 150), (3, 3), (4, 4), (5, 5), (7, 148), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019ee) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f56 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 53), (1, 150), (3, 3), (4, 4), (5, 5), (6, 152), (7, 148), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019f5) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.exec (n := 154) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1019f8) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f58 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 155), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a00) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f59 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 53), (1, 157), (3, 3), (4, 4), (5, 5), (7, 155), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a05) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1018b0_3 hstride code

theorem rest_l1018b0_1 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x1018b0 bytes_l1018b0) [(0, 53), (1, 85), (3, 3), (4, 4), (5, 5), (6, 87), (7, 83), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]
      51 0x101923 bytes_l1018b0_1 b_l1018b0_1 := by
  have f20 : InstrSpec 0x101923 [0xF3, 0x48, 0xA5] (RepPre 0x101923 (RepMovsqPre 0x101923)) (repMovsqEffect 0x101923)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101923).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101923 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f21 : InstrSpec 0x101926 [0x48, 0x8D, 0xBC, 0x24, 0x30, 0x0B, 0x00, 0x00] (fun s => s.RIP = 0x101926) (leaR64Effect 0x101926 7 (.sib 4 none 0 (.d32 0xb30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101926 7 (.sib 4 none 0 (.d32 0xb30))).toInstrSpec (lea_r64_effect_step 0x101926 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb30)) (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10192e [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10192e) (movR32Imm32Effect 0x10192e 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10192e 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10192e 0xb9 (by decide) 0xf) pre_rip
  have f23 : InstrSpec 0x101933 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x101933) (movR64Imm32Effect 0x101933 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x101933 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x101933 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f24 : InstrSpec 0x10193a [0xF3, 0x48, 0xA5] (RepPre 0x10193a (RepMovsqPre 0x10193a)) (repMovsqEffect 0x10193a)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10193a).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10193a 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f25 : InstrSpec 0x10193d [0x48, 0x8D, 0xBC, 0x24, 0xA8, 0x0B, 0x00, 0x00] (fun s => s.RIP = 0x10193d) (leaR64Effect 0x10193d 7 (.sib 4 none 0 (.d32 0xba8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10193d 7 (.sib 4 none 0 (.d32 0xba8))).toInstrSpec (lea_r64_effect_step 0x10193d 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xba8)) (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x101945 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101945) (movR32Imm32Effect 0x101945 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101945 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101945 0xb9 (by decide) 0xf) pre_rip
  have f27 : InstrSpec 0x10194a [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x10194a) (movR64Imm32Effect 0x10194a 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10194a 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x10194a 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f28 : InstrSpec 0x101951 [0xF3, 0x48, 0xA5] (RepPre 0x101951 (RepMovsqPre 0x101951)) (repMovsqEffect 0x101951)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101951).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101951 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f29 : InstrSpec 0x101954 [0x48, 0x8D, 0xBC, 0x24, 0x20, 0x0C, 0x00, 0x00] (fun s => s.RIP = 0x101954) (leaR64Effect 0x101954 7 (.sib 4 none 0 (.d32 0xc20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101954 7 (.sib 4 none 0 (.d32 0xc20))).toInstrSpec (lea_r64_effect_step 0x101954 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc20)) (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10195c [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10195c) (movR32Imm32Effect 0x10195c 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10195c 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10195c 0xb9 (by decide) 0xf) pre_rip
  have f31 : InstrSpec 0x101961 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x101961) (movR64Imm32Effect 0x101961 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x101961 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x101961 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f32 : InstrSpec 0x101968 [0xF3, 0x48, 0xA5] (RepPre 0x101968 (RepMovsqPre 0x101968)) (repMovsqEffect 0x101968)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101968).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101968 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f33 : InstrSpec 0x10196b [0x4C, 0x8D, 0xBC, 0x24, 0x98, 0x0C, 0x00, 0x00] (fun s => s.RIP = 0x10196b) (leaR64Effect 0x10196b 15 (.sib 4 none 0 (.d32 0xc98)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x10196b 15 (.sib 4 none 0 (.d32 0xc98))).toInstrSpec (lea_r64_effect_step 0x10196b 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xc98)) (by decide) (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x101973 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101973) (movR32Imm32Effect 0x101973 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101973 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101973 0xb9 (by decide) 0xf) pre_rip
  have f35 : InstrSpec 0x101978 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x101978) (movR64R64Effect 0x101978 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101978 7 15).toInstrSpec (mov_r64_r64_effect_step 0x101978 0x4c 0xff (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10197b [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x10197b) (movR64Imm32Effect 0x10197b 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10197b 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x10197b 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f37 : InstrSpec 0x101982 [0xF3, 0x48, 0xA5] (RepPre 0x101982 (RepMovsqPre 0x101982)) (repMovsqEffect 0x101982)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101982).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101982 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f38 : InstrSpec 0x101985 [0x48, 0x8D, 0xBC, 0x24, 0x10, 0x0D, 0x00, 0x00] (fun s => s.RIP = 0x101985) (leaR64Effect 0x101985 7 (.sib 4 none 0 (.d32 0xd10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101985 7 (.sib 4 none 0 (.d32 0xd10))).toInstrSpec (lea_r64_effect_step 0x101985 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xd10)) (by decide) (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10198d [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10198d) (movR32Imm32Effect 0x10198d 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10198d 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x10198d 0xb9 (by decide) 0xf) pre_rip
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101926) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f21 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 90), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10192e) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 53), (1, 92), (3, 3), (4, 4), (5, 5), (7, 90), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101933) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 53), (1, 92), (3, 3), (4, 4), (5, 5), (6, 94), (7, 90), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10193a) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10193d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f25 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 97), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101945) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 53), (1, 99), (3, 3), (4, 4), (5, 5), (7, 97), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10194a) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f27 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 53), (1, 99), (3, 3), (4, 4), (5, 5), (6, 101), (7, 97), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101951) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.exec (n := 103) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101954) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f29 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 104), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10195c) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 53), (1, 106), (3, 3), (4, 4), (5, 5), (7, 104), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101961) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f31 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 53), (1, 106), (3, 3), (4, 4), (5, 5), (6, 108), (7, 104), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101968) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10196b) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f33 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101973) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 53), (1, 113), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101978) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f35 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 53), (1, 113), (3, 3), (4, 4), (5, 5), (7, 115), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10197b) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f36 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 53), (1, 113), (3, 3), (4, 4), (5, 5), (6, 117), (7, 115), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101982) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.exec (n := 119) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101985) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f38 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 120), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10198d) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f39 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 53), (1, 122), (3, 3), (4, 4), (5, 5), (7, 120), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101992) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1018b0_2 hstride code

theorem rest_l1018b0 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1018b0 bytes_l1018b0) (entryMap (live .l1018b0))
      71 0x1018b0 bytes_l1018b0 b_l1018b0 := by
  have f0 : InstrSpec 0x1018b0 [0x48, 0x8D, 0x84, 0x24, 0xD8, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x1018b0) (leaR64Effect 0x1018b0 0 (.sib 4 none 0 (.d32 0x8d8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1018b0 0 (.sib 4 none 0 (.d32 0x8d8))).toInstrSpec (lea_r64_effect_step 0x1018b0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x8d8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1018b8 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1018b8) (movR32Imm32Effect 0x1018b8 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1018b8 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1018b8 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x1018bd [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x1018bd) (movR64R64Effect 0x1018bd 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1018bd 7 0).toInstrSpec (mov_r64_r64_effect_step 0x1018bd 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1018c0 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x1018c0) (movR64Imm32Effect 0x1018c0 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1018c0 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x1018c0 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f4 : InstrSpec 0x1018c7 [0xF3, 0x48, 0xA5] (RepPre 0x1018c7 (RepMovsqPre 0x1018c7)) (repMovsqEffect 0x1018c7)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1018c7).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1018c7 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x1018ca [0x48, 0x8D, 0xBC, 0x24, 0x50, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x1018ca) (leaR64Effect 0x1018ca 7 (.sib 4 none 0 (.d32 0x950)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1018ca 7 (.sib 4 none 0 (.d32 0x950))).toInstrSpec (lea_r64_effect_step 0x1018ca 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x950)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1018d2 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1018d2) (movR32Imm32Effect 0x1018d2 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1018d2 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1018d2 0xb9 (by decide) 0xf) pre_rip
  have f7 : InstrSpec 0x1018d7 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x1018d7) (movR64Imm32Effect 0x1018d7 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1018d7 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x1018d7 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f8 : InstrSpec 0x1018de [0xF3, 0x48, 0xA5] (RepPre 0x1018de (RepMovsqPre 0x1018de)) (repMovsqEffect 0x1018de)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1018de).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1018de 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x1018e1 [0x48, 0x8D, 0xBC, 0x24, 0xC8, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x1018e1) (leaR64Effect 0x1018e1 7 (.sib 4 none 0 (.d32 0x9c8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1018e1 7 (.sib 4 none 0 (.d32 0x9c8))).toInstrSpec (lea_r64_effect_step 0x1018e1 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x9c8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1018e9 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1018e9) (movR32Imm32Effect 0x1018e9 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1018e9 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x1018e9 0xb9 (by decide) 0xf) pre_rip
  have f11 : InstrSpec 0x1018ee [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x1018ee) (movR64Imm32Effect 0x1018ee 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1018ee 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x1018ee 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f12 : InstrSpec 0x1018f5 [0xF3, 0x48, 0xA5] (RepPre 0x1018f5 (RepMovsqPre 0x1018f5)) (repMovsqEffect 0x1018f5)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1018f5).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1018f5 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f13 : InstrSpec 0x1018f8 [0x48, 0x8D, 0xBC, 0x24, 0x40, 0x0A, 0x00, 0x00] (fun s => s.RIP = 0x1018f8) (leaR64Effect 0x1018f8 7 (.sib 4 none 0 (.d32 0xa40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1018f8 7 (.sib 4 none 0 (.d32 0xa40))).toInstrSpec (lea_r64_effect_step 0x1018f8 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xa40)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101900 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101900) (movR32Imm32Effect 0x101900 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101900 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101900 0xb9 (by decide) 0xf) pre_rip
  have f15 : InstrSpec 0x101905 [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x101905) (movR64Imm32Effect 0x101905 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x101905 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x101905 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  have f16 : InstrSpec 0x10190c [0xF3, 0x48, 0xA5] (RepPre 0x10190c (RepMovsqPre 0x10190c)) (repMovsqEffect 0x10190c)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10190c).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10190c 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x10190f [0x48, 0x8D, 0xBC, 0x24, 0xB8, 0x0A, 0x00, 0x00] (fun s => s.RIP = 0x10190f) (leaR64Effect 0x10190f 7 (.sib 4 none 0 (.d32 0xab8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10190f 7 (.sib 4 none 0 (.d32 0xab8))).toInstrSpec (lea_r64_effect_step 0x10190f 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xab8)) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x101917 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101917) (movR32Imm32Effect 0x101917 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101917 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101917 0xb9 (by decide) 0xf) pre_rip
  have f19 : InstrSpec 0x10191c [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00] (fun s => s.RIP = 0x10191c) (movR64Imm32Effect 0x10191c 6 0x202420)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10191c 6 0x202420).toInstrSpec (mov_r64_imm32_effect_step 0x10191c 0x48 0xc6 (by decide) (by decide) (by decide) 0x202420) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018b8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018bd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 57), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018c0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018c7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018ca) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 62), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018d2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 64), (3, 3), (4, 4), (5, 5), (7, 62), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018d7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 64), (3, 3), (4, 4), (5, 5), (6, 66), (7, 62), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018de) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018e1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 69), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018e9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 71), (3, 3), (4, 4), (5, 5), (7, 69), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018ee) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 71), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018f5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1018f8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 76), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101900) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 53), (1, 78), (3, 3), (4, 4), (5, 5), (7, 76), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101905) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 53), (1, 78), (3, 3), (4, 4), (5, 5), (6, 80), (7, 76), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10190c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10190f) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 83), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101917) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 53), (1, 85), (3, 3), (4, 4), (5, 5), (7, 83), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10191c) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 53), (1, 85), (3, 3), (4, 4), (5, 5), (6, 87), (7, 83), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101923) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1018b0_1 hstride code

theorem block_l1018b0 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1018b0 :=
  Rest.liftedBlock (rest_l1018b0 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1018b0 x hx)

theorem rest_l101a3c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101a3c bytes_l101a3c) (entryMap (live .l101a3c))
      4 0x101a3c bytes_l101a3c b_l101a3c := by
  have f0 : InstrSpec 0x101a3c [0x48, 0x8D, 0xBC, 0x24, 0x18, 0x05, 0x00, 0x00] (fun s => s.RIP = 0x101a3c) (leaR64Effect 0x101a3c 7 (.sib 4 none 0 (.d32 0x518)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101a3c 7 (.sib 4 none 0 (.d32 0x518))).toInstrSpec (lea_r64_effect_step 0x101a3c 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x518)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101a44 [0xBA, 0xC0, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x101a44) (movR32Imm32Effect 0x101a44 5 2 0x3c0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x101a44 5 2 0x3c0).toInstrSpec (mov_r32_imm32_effect_step 0x101a44 0xba (by decide) 0x3c0) pre_rip
  have f2 : InstrSpec 0x101a49 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x101a49) (movR64R64Effect 0x101a49 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101a49 6 15).toInstrSpec (mov_r64_r64_effect_step 0x101a49 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101a4c [0x41, 0xFF, 0xD5] (GoesTo (CallPre 0x101a4c 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a4f) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a4f)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x101a4c 13 0x101a4f).toInstrSpec (call_r64_rex_effect_step 0x101a4c 0x41 0xd5 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 13 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a44) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a49) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a4c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101a3c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101a3c :=
  Rest.liftedBlock (rest_l101a3c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101a3c x hx)

theorem rest_l101a4f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101a4f bytes_l101a4f) (entryMap (live .l101a4f))
      5 0x101a4f bytes_l101a4f b_l101a4f := by
  have f0 : InstrSpec 0x101a4f [0x4C, 0x8D, 0xBC, 0x24, 0x58, 0x10, 0x00, 0x00] (fun s => s.RIP = 0x101a4f) (leaR64Effect 0x101a4f 15 (.sib 4 none 0 (.d32 0x1058)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x101a4f 15 (.sib 4 none 0 (.d32 0x1058))).toInstrSpec (lea_r64_effect_step 0x101a4f 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x1058)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101a57 [0xBA, 0x80, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x101a57) (movR32Imm32Effect 0x101a57 5 2 0x780)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x101a57 5 2 0x780).toInstrSpec (mov_r32_imm32_effect_step 0x101a57 0xba (by decide) 0x780) pre_rip
  have f2 : InstrSpec 0x101a5c [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x101a5c) (movR64R64Effect 0x101a5c 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101a5c 7 15).toInstrSpec (mov_r64_r64_effect_step 0x101a5c 0x4c 0xff (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101a5f [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x101a5f) (movR64R64Effect 0x101a5f 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101a5f 6 12).toInstrSpec (mov_r64_r64_effect_step 0x101a5f 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101a62 [0x41, 0xFF, 0xD5] (GoesTo (CallPre 0x101a62 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a65) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a65)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x101a62 13 0x101a65).toInstrSpec (call_r64_rex_effect_step 0x101a62 0x41 0xd5 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 13 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a57) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a5c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a5f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a62) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 55), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l101a4f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101a4f :=
  Rest.liftedBlock (rest_l101a4f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101a4f x hx)

theorem rest_l101a65 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101a65 bytes_l101a65) (entryMap (live .l101a65))
      18 0x101a65 bytes_l101a65 b_l101a65 := by
  have f0 : InstrSpec 0x101a65 [0x66, 0xC7, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101a65 10 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x101a65 + BitVec.ofNat 64 10)) 2) (movM16Imm16Effect 0x101a65 (.sib 4 none 0 (.d32 0xb8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM16Imm16Effect_footprint 0x101a65 (.sib 4 none 0 (.d32 0xb8)) 0x0).toInstrSpec (mov_m16_imm16_effect_step 0x101a65 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x101a6f [0x48, 0xC7, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101a6f 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x101a6f + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101a6f (.sib 4 none 0 (.d32 0xb0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101a6f (.sib 4 none 0 (.d32 0xb0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101a6f 0x48 (by decide) (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x101a7b [0x48, 0xC7, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101a7b 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x101a7b + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101a7b (.sib 4 none 0 (.d32 0xa8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101a7b (.sib 4 none 0 (.d32 0xa8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101a7b 0x48 (by decide) (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101a87 [0x48, 0xC7, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101a87 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x101a87 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101a87 (.sib 4 none 0 (.d32 0xa0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101a87 (.sib 4 none 0 (.d32 0xa0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101a87 0x48 (by decide) (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101a93 [0x48, 0xC7, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101a93 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x101a93 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101a93 (.sib 4 none 0 (.d32 0x98)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101a93 (.sib 4 none 0 (.d32 0x98)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101a93 0x48 (by decide) (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x101a9f [0x48, 0xC7, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101a9f 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x101a9f + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101a9f (.sib 4 none 0 (.d32 0x90)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101a9f (.sib 4 none 0 (.d32 0x90)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101a9f 0x48 (by decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101aab [0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101aab 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x101aab + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101aab (.sib 4 none 0 (.d32 0x88)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101aab (.sib 4 none 0 (.d32 0x88)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101aab 0x48 (by decide) (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x101ab7 [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101ab7 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101ab7 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101ab7 (.sib 4 none 0 (.d32 0x80)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101ab7 (.sib 4 none 0 (.d32 0x80)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101ab7 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101ac3 [0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101ac3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101ac3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x101ac3 (.sib 4 none 0 (.d8 0x78)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101ac3 (.sib 4 none 0 (.d8 0x78)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101ac3 0x48 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101acc [0x48, 0xC7, 0x04, 0x24, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101acc 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101acc + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x101acc (.sib 4 none 0 .none) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101acc (.sib 4 none 0 .none) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x101acc 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x101ad4 [0x4C, 0x8D, 0xA4, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101ad4) (leaR64Effect 0x101ad4 12 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x101ad4 12 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x101ad4 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101adc [0x4C, 0x8D, 0x4C, 0x24, 0x78] (fun s => s.RIP = 0x101adc) (leaR64Effect 0x101adc 9 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x101adc 9 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x101adc 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101ae1 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101ae1) (movR32Imm32Effect 0x101ae1 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x101ae1 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x101ae1 0xba (by decide) 0x1) pre_rip
  have f13 : InstrSpec 0x101ae6 [0x41, 0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101ae6) (movR32Imm32Effect 0x101ae6 6 8 0x1)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x101ae6 6 8 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x101ae6 0x41 0xb8 (by decide) (by decide) 0x1) pre_rip
  have f14 : InstrSpec 0x101aec [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x101aec) (movR64R64Effect 0x101aec 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101aec 7 12).toInstrSpec (mov_r64_r64_effect_step 0x101aec 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x101aef [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x101aef) (movR64R64Effect 0x101aef 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101aef 6 14).toInstrSpec (mov_r64_r64_effect_step 0x101aef 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x101af2 [0x4C, 0x89, 0xF9] (fun s => s.RIP = 0x101af2) (movR64R64Effect 0x101af2 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x101af2 1 15).toInstrSpec (mov_r64_r64_effect_step 0x101af2 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x101af5 [0xE8, 0x86, 0xAD, 0x01, 0x00] (PushPre 0x101af5 5) (callEffect (fun _ => 0x11c880) 0x101afa)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101af5 0x11c880 0x101afa).toInstrSpec (call_rel32_effect_step 0x101af5 0x1ad86 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a6f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a7b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a87) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a93) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101a9f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101aab) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ab7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ac3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101acc) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ad4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101adc) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 65), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ae1) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 67), (3, 3), (4, 4), (5, 5), (9, 65), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ae6) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 67), (3, 3), (4, 4), (5, 5), (8, 69), (9, 65), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101aec) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 67), (3, 3), (4, 4), (5, 5), (7, 71), (8, 69), (9, 65), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101aef) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(2, 67), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (8, 69), (9, 65), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101af2) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 75), (2, 67), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (8, 69), (9, 65), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101af5) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f17 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 75), (2, 67), (3, 3), (4, 77), (5, 5), (6, 73), (7, 71), (8, 69), (9, 65), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c880) f17 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 79) (by decide) (by decide) rfl rfl

theorem block_l101a65 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101a65 :=
  Rest.liftedBlock (rest_l101a65 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101a65 x hx)

theorem rest_l101afa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101afa bytes_l101afa) (entryMap (live .l101afa))
      4 0x101afa bytes_l101afa b_l101afa := by
  have f0 : InstrSpec 0x101afa [0x4C, 0x8D, 0xB4, 0x24, 0x58, 0x10, 0x00, 0x00] (fun s => s.RIP = 0x101afa) (leaR64Effect 0x101afa 14 (.sib 4 none 0 (.d32 0x1058)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x101afa 14 (.sib 4 none 0 (.d32 0x1058))).toInstrSpec (lea_r64_effect_step 0x101afa 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x1058)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101b02 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x101b02) (movR64R64Effect 0x101b02 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101b02 7 14).toInstrSpec (mov_r64_r64_effect_step 0x101b02 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101b05 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x101b05) (movR64R64Effect 0x101b05 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101b05 6 12).toInstrSpec (mov_r64_r64_effect_step 0x101b05 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101b08 [0xE8, 0x43, 0xE3, 0x00, 0x00] (PushPre 0x101b08 5) (callEffect (fun _ => 0x10fe50) 0x101b0d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101b08 0x10fe50 0x101b0d).toInstrSpec (call_rel32_effect_step 0x101b08 0xe343 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b02) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b05) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b08) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fe50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101afa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101afa :=
  Rest.liftedBlock (rest_l101afa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101afa x hx)

theorem rest_l101b0d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101b0d bytes_l101b0d) (entryMap (live .l101b0d))
      3 0x101b0d bytes_l101b0d b_l101b0d := by
  have f0 : InstrSpec 0x101b0d [0x48, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101b0d) (leaR64Effect 0x101b0d 7 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101b0d 7 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (lea_r64_effect_step 0x101b0d 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101b15 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x101b15) (movR64R64Effect 0x101b15 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101b15 6 14).toInstrSpec (mov_r64_r64_effect_step 0x101b15 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101b18 [0xE8, 0x33, 0xE8, 0x01, 0x00] (PushPre 0x101b18 5) (callEffect (fun _ => 0x120350) 0x101b1d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101b18 0x120350 0x101b1d).toInstrSpec (call_rel32_effect_step 0x101b18 0x1e833 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b15) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b18) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120350) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l101b0d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101b0d :=
  Rest.liftedBlock (rest_l101b0d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101b0d x hx)

theorem rest_l101b1d_2 [Bindings] (code : CodeMap) :
    Rest (n := 97) code lifted (codeRange 0x101b1d bytes_l101b1d) [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x101c4c bytes_l101b1d_2 b_l101b1d_2 := by
  have f40 : InstrSpec 0x101c4c [0x48, 0x81, 0xC4, 0xD8, 0x17, 0x00, 0x00] (fun s => s.RIP = 0x101c4c) (addR64Imm32Effect 0x101c4c 4 0x17d8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x101c4c 4 0x17d8).toInstrSpec (add_r64_imm32_effect_step 0x101c4c 0x48 0xc4 0x17d8 (by decide) (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x101c53 [0x5B] (PopPre 0x101c53) (popR64Effect 0x101c53 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c53 1 3).toInstrSpec (pop_r64_effect_step 0x101c53 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f42 : InstrSpec 0x101c54 [0x41, 0x5C] (PopPre 0x101c54) (popR64Effect 0x101c54 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c54 2 12).toInstrSpec (pop_r64_rex_effect_step 0x101c54 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f43 : InstrSpec 0x101c56 [0x41, 0x5D] (PopPre 0x101c56) (popR64Effect 0x101c56 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c56 2 13).toInstrSpec (pop_r64_rex_effect_step 0x101c56 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f44 : InstrSpec 0x101c58 [0x41, 0x5E] (PopPre 0x101c58) (popR64Effect 0x101c58 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c58 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101c58 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f45 : InstrSpec 0x101c5a [0x41, 0x5F] (PopPre 0x101c5a) (popR64Effect 0x101c5a 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c5a 2 15).toInstrSpec (pop_r64_rex_effect_step 0x101c5a 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f46 : InstrSpec 0x101c5c [0x5D] (PopPre 0x101c5c) (popR64Effect 0x101c5c 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101c5c 1 5).toInstrSpec (pop_r64_effect_step 0x101c5c 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f47 : InstrSpec 0x101c5d [0xC3] (RetPre 0x101c5d) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101c5d).toInstrSpec (ret_effect_step 0x101c5d) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f40 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 97), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c53) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f41 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 100) f41 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 101) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 99), (4, 100), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c54) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f42 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 103) f42 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 104) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 99), (4, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 102), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c56) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f43 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 106) f43 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 107) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 99), (4, 106), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 102), (13, 105), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c58) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f44 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 109) f44 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 110) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 99), (4, 109), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 102), (13, 105), (14, 108), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c5a) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f45 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 112) f45 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 113) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 99), (4, 112), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 102), (13, 105), (14, 108), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c5c) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f46 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 115) f46 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 116) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 99), (4, 115), (5, 114), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 102), (13, 105), (14, 108), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c5d) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f47 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 118) f47 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 119) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 99), (4, 118), (5, 114), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 102), (13, 105), (14, 108), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) f47 (by decide) rfl rfl rfl (by decide)

theorem rest_l101b1d_1 [Bindings] (code : CodeMap) :
    Rest (n := 77) code lifted (codeRange 0x101b1d bytes_l101b1d) [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]
      28 0x101bac bytes_l101b1d_1 b_l101b1d_1 := by
  have f20 : InstrSpec 0x101bac [0xC6, 0x84, 0x24, 0x64, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bac 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x164)) s (0x101bac + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bac (.sib 4 none 0 (.d32 0x164)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bac (.sib 4 none 0 (.d32 0x164)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bac (.sib 4 none 0 (.d32 0x164)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x101bb4 [0xC6, 0x84, 0x24, 0x65, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bb4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x165)) s (0x101bb4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bb4 (.sib 4 none 0 (.d32 0x165)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bb4 (.sib 4 none 0 (.d32 0x165)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bb4 (.sib 4 none 0 (.d32 0x165)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x101bbc [0xC6, 0x84, 0x24, 0x66, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bbc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x166)) s (0x101bbc + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bbc (.sib 4 none 0 (.d32 0x166)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bbc (.sib 4 none 0 (.d32 0x166)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bbc (.sib 4 none 0 (.d32 0x166)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x101bc4 [0xC6, 0x84, 0x24, 0x67, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bc4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x167)) s (0x101bc4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bc4 (.sib 4 none 0 (.d32 0x167)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bc4 (.sib 4 none 0 (.d32 0x167)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bc4 (.sib 4 none 0 (.d32 0x167)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x101bcc [0xC6, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bcc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x101bcc + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bcc (.sib 4 none 0 (.d32 0x168)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bcc (.sib 4 none 0 (.d32 0x168)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bcc (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x101bd4 [0xC6, 0x84, 0x24, 0x69, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bd4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x169)) s (0x101bd4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bd4 (.sib 4 none 0 (.d32 0x169)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bd4 (.sib 4 none 0 (.d32 0x169)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bd4 (.sib 4 none 0 (.d32 0x169)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x101bdc [0xC6, 0x84, 0x24, 0x6A, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bdc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16a)) s (0x101bdc + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bdc (.sib 4 none 0 (.d32 0x16a)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bdc (.sib 4 none 0 (.d32 0x16a)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bdc (.sib 4 none 0 (.d32 0x16a)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x101be4 [0xC6, 0x84, 0x24, 0x6B, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101be4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16b)) s (0x101be4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101be4 (.sib 4 none 0 (.d32 0x16b)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101be4 (.sib 4 none 0 (.d32 0x16b)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101be4 (.sib 4 none 0 (.d32 0x16b)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x101bec [0xC6, 0x84, 0x24, 0x6C, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bec 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16c)) s (0x101bec + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bec (.sib 4 none 0 (.d32 0x16c)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bec (.sib 4 none 0 (.d32 0x16c)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bec (.sib 4 none 0 (.d32 0x16c)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x101bf4 [0xC6, 0x84, 0x24, 0x6D, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bf4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16d)) s (0x101bf4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bf4 (.sib 4 none 0 (.d32 0x16d)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bf4 (.sib 4 none 0 (.d32 0x16d)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bf4 (.sib 4 none 0 (.d32 0x16d)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x101bfc [0xC6, 0x84, 0x24, 0x6E, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101bfc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16e)) s (0x101bfc + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bfc (.sib 4 none 0 (.d32 0x16e)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101bfc (.sib 4 none 0 (.d32 0x16e)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101bfc (.sib 4 none 0 (.d32 0x16e)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x101c04 [0xC6, 0x84, 0x24, 0x6F, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c04 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16f)) s (0x101c04 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c04 (.sib 4 none 0 (.d32 0x16f)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c04 (.sib 4 none 0 (.d32 0x16f)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c04 (.sib 4 none 0 (.d32 0x16f)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x101c0c [0xC6, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c0c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x101c0c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c0c (.sib 4 none 0 (.d32 0x170)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c0c (.sib 4 none 0 (.d32 0x170)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c0c (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x101c14 [0xC6, 0x84, 0x24, 0x71, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c14 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x171)) s (0x101c14 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c14 (.sib 4 none 0 (.d32 0x171)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c14 (.sib 4 none 0 (.d32 0x171)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c14 (.sib 4 none 0 (.d32 0x171)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x101c1c [0xC6, 0x84, 0x24, 0x72, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c1c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x172)) s (0x101c1c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c1c (.sib 4 none 0 (.d32 0x172)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c1c (.sib 4 none 0 (.d32 0x172)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c1c (.sib 4 none 0 (.d32 0x172)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x101c24 [0xC6, 0x84, 0x24, 0x73, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c24 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x173)) s (0x101c24 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c24 (.sib 4 none 0 (.d32 0x173)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c24 (.sib 4 none 0 (.d32 0x173)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c24 (.sib 4 none 0 (.d32 0x173)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x101c2c [0xC6, 0x84, 0x24, 0x74, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c2c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x174)) s (0x101c2c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c2c (.sib 4 none 0 (.d32 0x174)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c2c (.sib 4 none 0 (.d32 0x174)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c2c (.sib 4 none 0 (.d32 0x174)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x101c34 [0xC6, 0x84, 0x24, 0x75, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c34 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x175)) s (0x101c34 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c34 (.sib 4 none 0 (.d32 0x175)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c34 (.sib 4 none 0 (.d32 0x175)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c34 (.sib 4 none 0 (.d32 0x175)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x101c3c [0xC6, 0x84, 0x24, 0x76, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c3c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x176)) s (0x101c3c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c3c (.sib 4 none 0 (.d32 0x176)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c3c (.sib 4 none 0 (.d32 0x176)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c3c (.sib 4 none 0 (.d32 0x176)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x101c44 [0xC6, 0x84, 0x24, 0x77, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101c44 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x177)) s (0x101c44 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c44 (.sib 4 none 0 (.d32 0x177)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101c44 (.sib 4 none 0 (.d32 0x177)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101c44 (.sib 4 none 0 (.d32 0x177)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bb4) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bbc) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bc4) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bcc) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bd4) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bdc) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101be4) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bec) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bf4) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bfc) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c04) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c0c) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c14) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c1c) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c24) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c2c) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c34) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c3c) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c44) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c4c) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l101b1d_2 code

theorem rest_l101b1d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101b1d bytes_l101b1d) (entryMap (live .l101b1d))
      48 0x101b1d bytes_l101b1d b_l101b1d := by
  have f0 : InstrSpec 0x101b1d [0x48, 0x8B, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00] (LoadPre 0x101b1d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x101b1d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101b1d 0 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101b1d 0 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (mov_r64_m64_effect_step 0x101b1d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101b25 [0x48, 0x89, 0x43, 0x18] (StorePre 0x101b25 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x101b25 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101b25 0 (.base 3 (.d8 0x18)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101b25 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x101b25 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x101b29 [0x48, 0x8B, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00] (LoadPre 0x101b29 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x101b29 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101b29 0 (.sib 4 none 0 (.d32 0x168)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101b29 0 (.sib 4 none 0 (.d32 0x168))).toInstrSpec (mov_r64_m64_effect_step 0x101b29 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x101b31 [0x48, 0x89, 0x43, 0x10] (StorePre 0x101b31 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x101b31 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101b31 0 (.base 3 (.d8 0x10)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101b31 0 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x101b31 0x48 (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101b35 [0x48, 0x8B, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00] (LoadPre 0x101b35 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x101b35 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101b35 0 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101b35 0 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (mov_r64_m64_effect_step 0x101b35 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101b3d [0x48, 0x8B, 0x8C, 0x24, 0x60, 0x01, 0x00, 0x00] (LoadPre 0x101b3d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x101b3d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101b3d 1 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101b3d 1 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (mov_r64_m64_effect_step 0x101b3d 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x101b45 [0x48, 0x89, 0x4B, 0x08] (StorePre 0x101b45 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x101b45 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101b45 1 (.base 3 (.d8 0x8)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101b45 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x101b45 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x101b49 [0x48, 0x89, 0x03] (StorePre 0x101b49 3 (fun s => AddrMode.addr (.base 3 .none) s (0x101b49 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x101b49 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101b49 0 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x101b49 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101b4c [0xC6, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b4c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x101b4c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b4c (.sib 4 none 0 (.d32 0x158)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b4c (.sib 4 none 0 (.d32 0x158)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b4c (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101b54 [0xC6, 0x84, 0x24, 0x59, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b54 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x159)) s (0x101b54 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b54 (.sib 4 none 0 (.d32 0x159)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b54 (.sib 4 none 0 (.d32 0x159)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b54 (.sib 4 none 0 (.d32 0x159)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x101b5c [0xC6, 0x84, 0x24, 0x5A, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b5c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15a)) s (0x101b5c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b5c (.sib 4 none 0 (.d32 0x15a)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b5c (.sib 4 none 0 (.d32 0x15a)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b5c (.sib 4 none 0 (.d32 0x15a)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x101b64 [0xC6, 0x84, 0x24, 0x5B, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b64 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15b)) s (0x101b64 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b64 (.sib 4 none 0 (.d32 0x15b)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b64 (.sib 4 none 0 (.d32 0x15b)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b64 (.sib 4 none 0 (.d32 0x15b)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x101b6c [0xC6, 0x84, 0x24, 0x5C, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b6c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15c)) s (0x101b6c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b6c (.sib 4 none 0 (.d32 0x15c)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b6c (.sib 4 none 0 (.d32 0x15c)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b6c (.sib 4 none 0 (.d32 0x15c)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x101b74 [0xC6, 0x84, 0x24, 0x5D, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b74 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15d)) s (0x101b74 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b74 (.sib 4 none 0 (.d32 0x15d)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b74 (.sib 4 none 0 (.d32 0x15d)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b74 (.sib 4 none 0 (.d32 0x15d)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x101b7c [0xC6, 0x84, 0x24, 0x5E, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b7c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15e)) s (0x101b7c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b7c (.sib 4 none 0 (.d32 0x15e)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b7c (.sib 4 none 0 (.d32 0x15e)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b7c (.sib 4 none 0 (.d32 0x15e)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x101b84 [0xC6, 0x84, 0x24, 0x5F, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b84 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15f)) s (0x101b84 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b84 (.sib 4 none 0 (.d32 0x15f)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b84 (.sib 4 none 0 (.d32 0x15f)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b84 (.sib 4 none 0 (.d32 0x15f)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x101b8c [0xC6, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b8c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x101b8c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b8c (.sib 4 none 0 (.d32 0x160)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b8c (.sib 4 none 0 (.d32 0x160)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b8c (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x101b94 [0xC6, 0x84, 0x24, 0x61, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b94 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x161)) s (0x101b94 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b94 (.sib 4 none 0 (.d32 0x161)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b94 (.sib 4 none 0 (.d32 0x161)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b94 (.sib 4 none 0 (.d32 0x161)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x101b9c [0xC6, 0x84, 0x24, 0x62, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101b9c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x162)) s (0x101b9c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b9c (.sib 4 none 0 (.d32 0x162)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101b9c (.sib 4 none 0 (.d32 0x162)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101b9c (.sib 4 none 0 (.d32 0x162)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x101ba4 [0xC6, 0x84, 0x24, 0x63, 0x01, 0x00, 0x00, 0x00] (StorePre 0x101ba4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x163)) s (0x101ba4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101ba4 (.sib 4 none 0 (.d32 0x163)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x101ba4 (.sib 4 none 0 (.d32 0x163)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x101ba4 (.sib 4 none 0 (.d32 0x163)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b25) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b29) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b31) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b35) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b3d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b45) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b49) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b4c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b54) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b5c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b64) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b6c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b74) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b7c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b84) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b8c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b94) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101b9c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ba4) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101bac) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l101b1d_1 code

theorem block_l101b1d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101b1d :=
  Rest.liftedBlock (rest_l101b1d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101b1d x hx)

theorem rest_l101c5e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101c5e bytes_l101c5e) (entryMap (live .l101c5e))
      1 0x101c5e bytes_l101c5e b_l101c5e := by
  have f0 : InstrSpec 0x101c5e [0xE8, 0xCD, 0xED, 0xFF, 0xFF] (PushPre 0x101c5e 5) (callEffect (fun _ => 0x100a30) 0x101c63)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101c5e 0x100a30 0x101c63).toInstrSpec (call_rel32_effect_step 0x101c5e 0xffffedcd (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := []) (p' := 0x100a30) f0 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 54) (by decide) (by decide) rfl rfl

theorem block_l101c5e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101c5e :=
  Rest.liftedBlock (rest_l101c5e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101c5e x hx)

theorem rest_l101c63 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101c63 bytes_l101c63) (entryMap (live .l101c63))
      20 0x101c63 bytes_l101c63 b_l101c63 := by
  have f0 : InstrSpec 0x101c63 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101c63) (fun _ => nopEffect 0x101c63 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x101c63 10).toInstrSpec (nop_m_effect_step 0x101c63 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101c6d [0x0F, 0x1F, 0x00] (fun s => s.RIP = 0x101c6d) (fun _ => nopEffect 0x101c6d 3)
      [] [] [.rip] :=
    (nopEffect_footprint 0x101c6d 3).toInstrSpec (nop_m_effect_step 0x101c6d [] (by decide) (by decide) (.base 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101c70 [0x41, 0x56] (PushPre 0x101c70 2) (pushR64Effect 0x101c70 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101c70 2 14).toInstrSpec (push_r64_rex_effect_step 0x101c70 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101c72 [0x53] (PushPre 0x101c72 1) (pushR64Effect 0x101c72 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101c72 1 3).toInstrSpec (push_r64_effect_step 0x101c72 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101c73 [0x48, 0x81, 0xEC, 0xE8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101c73) (subR64Imm32Effect 0x101c73 4 0x1e8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x101c73 4 0x1e8).toInstrSpec (sub_r64_imm32_effect_step 0x101c73 0x48 0xec 0x1e8 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101c7a [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x101c7a) (movR64R64Effect 0x101c7a 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101c7a 14 2).toInstrSpec (mov_r64_r64_effect_step 0x101c7a 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101c7d [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x101c7d) (movR64R64Effect 0x101c7d 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x101c7d 3 7).toInstrSpec (mov_r64_r64_effect_step 0x101c7d 0x48 0xfb (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101c80 [0x0F, 0xB6, 0x46, 0x20] (LoadPre 0x101c80 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x101c80 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x101c80 4 0 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101c80 4 0 (.base 6 (.d8 0x20))).toInstrSpec (movzx_r32_m8_effect_step 0x101c80 0 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x101c84 [0x88, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x101c84 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x101c84 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x101c84 7 0 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101c84 7 0 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m8_r8_effect_step 0x101c84 0 (by decide) (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101c8b [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x101c8b (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x101c8b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101c8b 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101c8b 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101c8b 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x101c8f [0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x101c8f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x101c8f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101c8f 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101c8f 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m64_r64_effect_step 0x101c8f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x101c97 [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x101c97 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x101c97 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101c97 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101c97 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x101c97 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x101c9b [0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x101c9b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x101c9b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101c9b 0 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101c9b 0 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m64_r64_effect_step 0x101c9b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x101ca3 [0x48, 0x8B, 0x06] (LoadPre 0x101ca3 (fun s => AddrMode.addr (.base 6 .none) s (0x101ca3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101ca3 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101ca3 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x101ca3 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x101ca6 [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x101ca6 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x101ca6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101ca6 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101ca6 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x101ca6 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x101caa [0x48, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x101caa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x101caa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101caa 1 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101caa 1 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m64_r64_effect_step 0x101caa 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x101cb2 [0x48, 0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x101cb2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x101cb2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101cb2 0 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101cb2 0 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x101cb2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x101cba [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x101cba) (movR64R64Effect 0x101cba 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101cba 7 4).toInstrSpec (mov_r64_r64_effect_step 0x101cba 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x101cbd [0x48, 0x8D, 0xB4, 0x24, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101cbd) (leaR64Effect 0x101cbd 6 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101cbd 6 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (lea_r64_effect_step 0x101cbd 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x101cc5 [0xE8, 0x36, 0xE2, 0x00, 0x00] (PushPre 0x101cc5 5) (callEffect (fun _ => 0x10ff00) 0x101cca)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101cc5 0x10ff00 0x101cca).toInstrSpec (call_rel32_effect_step 0x101cc5 0xe236 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c6d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c70) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c72) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c73) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c7a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c7d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c80) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c84) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c8b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c8f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c97) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c9b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ca3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ca6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 74), (1, 76), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101caa) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 74), (1, 76), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cb2) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 74), (1, 76), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cba) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 74), (1, 76), (2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cbd) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 74), (1, 76), (2, 2), (3, 63), (4, 59), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cc5) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 74), (1, 76), (2, 2), (3, 63), (4, 84), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff00) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 86) (by decide) (by decide) rfl rfl

theorem block_l101c63 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101c63 :=
  Rest.liftedBlock (rest_l101c63 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101c63 x hx)

theorem rest_l101cca [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101cca bytes_l101cca) (entryMap (live .l101cca))
      2 0x101cca bytes_l101cca b_l101cca := by
  have f0 : InstrSpec 0x101cca [0x80, 0x7C, 0x24, 0x78, 0x01] (LoadPre 0x101cca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101cca + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x101cca 5 (.sib 4 none 0 (.d8 0x78)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x101cca 5 (.sib 4 none 0 (.d8 0x78)) 0x1).toInstrSpec (cmp_m8_imm8_effect_step 0x101cca (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ccf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x101ccf 5 0xf6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101cca [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101cca :=
  Rest.liftedBlock (rest_l101cca code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101cca x hx)

theorem rest_l101cd5 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101cd5 bytes_l101cd5) (entryMap (live .l101cd5))
      17 0x101cd5 bytes_l101cd5 b_l101cd5 := by
  have f0 : InstrSpec 0x101cd5 [0x48, 0x8D, 0xBC, 0x24, 0x70, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101cd5) (leaR64Effect 0x101cd5 7 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101cd5 7 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (lea_r64_effect_step 0x101cd5 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101cdd [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x101cdd) (movR64R64Effect 0x101cdd 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101cdd 6 4).toInstrSpec (mov_r64_r64_effect_step 0x101cdd 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101ce0 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101ce0) (movR32Imm32Effect 0x101ce0 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101ce0 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101ce0 0xb9 (by decide) 0xf) pre_rip
  have f3 : InstrSpec 0x101ce5 [0xF3, 0x48, 0xA5] (RepPre 0x101ce5 (RepMovsqPre 0x101ce5)) (repMovsqEffect 0x101ce5)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101ce5).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101ce5 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x101ce8 [0x41, 0x0F, 0xB6, 0x46, 0x20] (LoadPre 0x101ce8 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x101ce8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101ce8 5 0 (.base 14 (.d8 0x20)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101ce8 5 0 (.base 14 (.d8 0x20))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101ce8 0x41 (by decide) 0 (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101ced [0x88, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x101ced 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x101ced + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x101ced 7 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x101ced 7 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m8_r8_effect_step 0x101ced 0 (by decide) (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101cf4 [0x49, 0x8B, 0x46, 0x18] (LoadPre 0x101cf4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x101cf4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101cf4 0 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101cf4 0 (.base 14 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101cf4 0x49 (by decide) 0 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x101cf8 [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x101cf8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x101cf8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101cf8 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101cf8 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x101cf8 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101d00 [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x101d00 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x101d00 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101d00 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101d00 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x101d00 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x101d04 [0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x101d04 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x101d04 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101d04 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101d04 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x101d04 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x101d0c [0x49, 0x8B, 0x06] (LoadPre 0x101d0c (fun s => AddrMode.addr (.base 14 .none) s (0x101d0c + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101d0c 0 (.base 14 .none))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101d0c 0 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x101d0c 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x101d0f [0x49, 0x8B, 0x4E, 0x08] (LoadPre 0x101d0f (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x101d0f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101d0f 1 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101d0f 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x101d0f 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x101d13 [0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x101d13 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x101d13 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101d13 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101d13 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x101d13 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x101d1b [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x101d1b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101d1b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101d1b 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101d1b 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x101d1b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x101d23 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x101d23) (movR64R64Effect 0x101d23 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101d23 7 4).toInstrSpec (mov_r64_r64_effect_step 0x101d23 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x101d26 [0x48, 0x8D, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101d26) (leaR64Effect 0x101d26 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101d26 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (lea_r64_effect_step 0x101d26 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x101d2e [0xE8, 0xCD, 0xE1, 0x00, 0x00] (PushPre 0x101d2e 5) (callEffect (fun _ => 0x10ff00) 0x101d33)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101d2e 0x10ff00 0x101d33).toInstrSpec (call_rel32_effect_step 0x101d2e 0xe1cd (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cdd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ce0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ce5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ce8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ced) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cf4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cf8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d00) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d04) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d0c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d0f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 71), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d13) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 69), (1, 71), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d1b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 71), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d23) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 69), (1, 71), (3, 3), (4, 4), (5, 5), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d26) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 69), (1, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d2e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 69), (1, 71), (3, 3), (4, 79), (5, 5), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff00) f16 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 81) (by decide) (by decide) rfl rfl

theorem block_l101cd5 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101cd5 :=
  Rest.liftedBlock (rest_l101cd5 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101cd5 x hx)

theorem rest_l101d33 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101d33 bytes_l101d33) (entryMap (live .l101d33))
      2 0x101d33 bytes_l101d33 b_l101d33 := by
  have f0 : InstrSpec 0x101d33 [0x80, 0x7C, 0x24, 0x78, 0x01] (LoadPre 0x101d33 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101d33 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x101d33 5 (.sib 4 none 0 (.d8 0x78)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x101d33 5 (.sib 4 none 0 (.d8 0x78)) 0x1).toInstrSpec (cmp_m8_imm8_effect_step 0x101d33 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d38) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x101d38 5 0x8d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101d33 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101d33 :=
  Rest.liftedBlock (rest_l101d33 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101d33 x hx)

theorem rest_l101d3e [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101d3e bytes_l101d3e) (entryMap (live .l101d3e))
      13 0x101d3e bytes_l101d3e b_l101d3e := by
  have f0 : InstrSpec 0x101d3e [0x48, 0x8D, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101d3e) (leaR64Effect 0x101d3e 0 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x101d3e 0 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (lea_r64_effect_step 0x101d3e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101d46 [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x101d46) (movR64R64Effect 0x101d46 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101d46 6 4).toInstrSpec (mov_r64_r64_effect_step 0x101d46 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101d49 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101d49) (movR32Imm32Effect 0x101d49 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101d49 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101d49 0xb9 (by decide) 0xf) pre_rip
  have f3 : InstrSpec 0x101d4e [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x101d4e) (movR64R64Effect 0x101d4e 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101d4e 7 0).toInstrSpec (mov_r64_r64_effect_step 0x101d4e 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101d51 [0xF3, 0x48, 0xA5] (RepPre 0x101d51 (RepMovsqPre 0x101d51)) (repMovsqEffect 0x101d51)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101d51).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101d51 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x101d54 [0x49, 0x89, 0xE6] (fun s => s.RIP = 0x101d54) (movR64R64Effect 0x101d54 14 4)
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101d54 14 4).toInstrSpec (mov_r64_r64_effect_step 0x101d54 0x49 0xe6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101d57 [0x48, 0x8D, 0xB4, 0x24, 0x70, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101d57) (leaR64Effect 0x101d57 6 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101d57 6 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (lea_r64_effect_step 0x101d57 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101d5f [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101d5f) (movR32Imm32Effect 0x101d5f 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101d5f 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101d5f 0xb9 (by decide) 0xf) pre_rip
  have f8 : InstrSpec 0x101d64 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x101d64) (movR64R64Effect 0x101d64 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101d64 7 14).toInstrSpec (mov_r64_r64_effect_step 0x101d64 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101d67 [0xF3, 0x48, 0xA5] (RepPre 0x101d67 (RepMovsqPre 0x101d67)) (repMovsqEffect 0x101d67)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101d67).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101d67 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f10 : InstrSpec 0x101d6a [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x101d6a) (movR64R64Effect 0x101d6a 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101d6a 7 14).toInstrSpec (mov_r64_r64_effect_step 0x101d6a 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101d6d [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x101d6d) (movR64R64Effect 0x101d6d 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101d6d 6 0).toInstrSpec (mov_r64_r64_effect_step 0x101d6d 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101d70 [0xE8, 0x9B, 0x86, 0x00, 0x00] (PushPre 0x101d70 5) (callEffect (fun _ => 0x10a410) 0x101d75)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101d70 0x10a410 0x101d75).toInstrSpec (call_rel32_effect_step 0x101d70 0x869b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d46) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 55), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d49) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d4e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d51) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d54) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d57) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 64), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d5f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 66), (3, 3), (4, 4), (5, 5), (6, 64), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d64) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 66), (3, 3), (4, 4), (5, 5), (6, 64), (7, 68), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d67) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d6a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 71), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d6d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 73), (7, 71), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d70) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 53), (3, 3), (4, 75), (5, 5), (6, 73), (7, 71), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a410) f12 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l101d3e [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101d3e :=
  Rest.liftedBlock (rest_l101d3e hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101d3e x hx)

theorem rest_l101d75 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101d75 bytes_l101d75) (entryMap (live .l101d75))
      8 0x101d75 bytes_l101d75 b_l101d75 := by
  have f0 : InstrSpec 0x101d75 [0x48, 0x8D, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101d75) (leaR64Effect 0x101d75 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x101d75 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (lea_r64_effect_step 0x101d75 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101d7d [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101d7d) (movR32Imm32Effect 0x101d7d 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101d7d 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x101d7d 0xb9 (by decide) 0xf) pre_rip
  have f2 : InstrSpec 0x101d82 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x101d82) (movR64R64Effect 0x101d82 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101d82 7 0).toInstrSpec (mov_r64_r64_effect_step 0x101d82 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101d85 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x101d85) (movR64R64Effect 0x101d85 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101d85 6 14).toInstrSpec (mov_r64_r64_effect_step 0x101d85 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101d88 [0xF3, 0x48, 0xA5] (RepPre 0x101d88 (RepMovsqPre 0x101d88)) (repMovsqEffect 0x101d88)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x101d88).toInstrSpecOfRuns (rep_movsq_runs hstride 0x101d88 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x101d8b [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x101d8b) (movR64R64Effect 0x101d8b 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101d8b 7 4).toInstrSpec (mov_r64_r64_effect_step 0x101d8b 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101d8e [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x101d8e) (movR64R64Effect 0x101d8e 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101d8e 6 0).toInstrSpec (mov_r64_r64_effect_step 0x101d8e 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101d91 [0xE8, 0xDA, 0xE2, 0x00, 0x00] (PushPre 0x101d91 5) (callEffect (fun _ => 0x110070) 0x101d96)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101d91 0x110070 0x101d96).toInstrSpec (call_rel32_effect_step 0x101d91 0xe2da (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d7d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d82) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 57), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d85) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d88) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d8b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d8e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d91) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (3, 3), (4, 66), (5, 5), (6, 64), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110070) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l101d75 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101d75 :=
  Rest.liftedBlock (rest_l101d75 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101d75 x hx)

theorem rest_l101d96 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101d96 bytes_l101d96) (entryMap (live .l101d96))
      14 0x101d96 bytes_l101d96 b_l101d96 := by
  have f0 : InstrSpec 0x101d96 [0x0F, 0xB6, 0x44, 0x24, 0x20] (LoadPre 0x101d96 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101d96 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101d96 5 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x101d96 5 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (movzx_r32_m8_effect_step 0x101d96 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101d9b [0x88, 0x43, 0x20] (StorePre 0x101d9b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x101d9b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101d9b 3 0 (.base 3 (.d8 0x20)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x101d9b 3 0 (.base 3 (.d8 0x20))).toInstrSpec (mov_m8_r8_effect_step 0x101d9b 0 (by decide) (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x101d9e [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x101d9e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101d9e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101d9e 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101d9e 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101d9e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x101da3 [0x48, 0x89, 0x43, 0x18] (StorePre 0x101da3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x101da3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101da3 0 (.base 3 (.d8 0x18)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101da3 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x101da3 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101da7 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x101da7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101da7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101da7 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101da7 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x101da7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101dac [0x48, 0x89, 0x43, 0x10] (StorePre 0x101dac 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x101dac + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101dac 0 (.base 3 (.d8 0x10)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101dac 0 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x101dac 0x48 (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101db0 [0x48, 0x8B, 0x04, 0x24] (LoadPre 0x101db0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101db0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101db0 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101db0 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x101db0 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x101db4 [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x101db4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101db4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101db4 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101db4 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x101db4 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x101db9 [0x48, 0x89, 0x4B, 0x08] (StorePre 0x101db9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x101db9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101db9 1 (.base 3 (.d8 0x8)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101db9 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x101db9 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101dbd [0x48, 0x89, 0x03] (StorePre 0x101dbd 3 (fun s => AddrMode.addr (.base 3 .none) s (0x101dbd + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x101dbd 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x101dbd 0 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x101dbd 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x101dc0 [0x48, 0x81, 0xC4, 0xE8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x101dc0) (addR64Imm32Effect 0x101dc0 4 0x1e8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x101dc0 4 0x1e8).toInstrSpec (add_r64_imm32_effect_step 0x101dc0 0x48 0xc4 0x1e8 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101dc7 [0x5B] (PopPre 0x101dc7) (popR64Effect 0x101dc7 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101dc7 1 3).toInstrSpec (pop_r64_effect_step 0x101dc7 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x101dc8 [0x41, 0x5E] (PopPre 0x101dc8) (popR64Effect 0x101dc8 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101dc8 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101dc8 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f13 : InstrSpec 0x101dca [0xC3] (RetPre 0x101dca) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101dca).toInstrSpec (ret_effect_step 0x101dca) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d9b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d9e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101da3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101da7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dac) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101db0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101db4) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101db9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dbd) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dc0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 62), (1, 64), (2, 2), (3, 3), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dc7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 64), (2, 2), (3, 70), (4, 71), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dc8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 62), (1, 64), (2, 2), (3, 70), (4, 74), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dca) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 78) (ρ' := [(0, 62), (1, 64), (2, 2), (3, 70), (4, 77), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f13 (by decide) rfl rfl rfl (by decide)

theorem block_l101d96 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101d96 :=
  Rest.liftedBlock (rest_l101d96 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101d96 x hx)

theorem rest_l101dcb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101dcb bytes_l101dcb) (entryMap (live .l101dcb))
      1 0x101dcb bytes_l101dcb b_l101dcb := by
  have f0 : InstrSpec 0x101dcb [0xE8, 0x60, 0xEC, 0xFF, 0xFF] (PushPre 0x101dcb 5) (callEffect (fun _ => 0x100a30) 0x101dd0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101dcb 0x100a30 0x101dd0).toInstrSpec (call_rel32_effect_step 0x101dcb 0xffffec60 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := []) (p' := 0x100a30) f0 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 54) (by decide) (by decide) rfl rfl

theorem block_l101dcb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101dcb :=
  Rest.liftedBlock (rest_l101dcb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101dcb x hx)

theorem rest_l101dd0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101dd0 bytes_l101dd0) (entryMap (live .l101dd0))
      6 0x101dd0 bytes_l101dd0 b_l101dd0 := by
  have f0 : InstrSpec 0x101dd0 [0x41, 0x56] (PushPre 0x101dd0 2) (pushR64Effect 0x101dd0 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101dd0 2 14).toInstrSpec (push_r64_rex_effect_step 0x101dd0 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x101dd2 [0x53] (PushPre 0x101dd2 1) (pushR64Effect 0x101dd2 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101dd2 1 3).toInstrSpec (push_r64_effect_step 0x101dd2 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101dd3 [0x48, 0x81, 0xEC, 0xE8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101dd3) (subR64Imm32Effect 0x101dd3 4 0xe8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x101dd3 4 0xe8).toInstrSpec (sub_r64_imm32_effect_step 0x101dd3 0x48 0xec 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101dda [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x101dda) (movR64R64Effect 0x101dda 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101dda 14 7).toInstrSpec (mov_r64_r64_effect_step 0x101dda 0x49 0xfe (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101ddd [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101ddd) (leaR64Effect 0x101ddd 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101ddd 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x101ddd 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101de5 [0xE8, 0xA6, 0x45, 0x00, 0x00] (PushPre 0x101de5 5) (callEffect (fun _ => 0x106390) 0x101dea)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101de5 0x106390 0x101dea).toInstrSpec (call_rel32_effect_step 0x101de5 0x45a6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dd2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dd3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dda) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ddd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101de5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106390) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l101dd0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101dd0 :=
  Rest.liftedBlock (rest_l101dd0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101dd0 x hx)

theorem rest_l101dea [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101dea bytes_l101dea) (entryMap (live .l101dea))
      3 0x101dea bytes_l101dea b_l101dea := by
  have f0 : InstrSpec 0x101dea [0x48, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x101dea (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x101dea + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101dea 3 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x101dea 3 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x101dea 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101df2 [0x48, 0x83, 0xFB, 0x01] (fun s => s.RIP = 0x101df2) (cmpR64Imm8Effect 0x101df2 3 0x1)
      [.gpr 3] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x101df2 3 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x101df2 0x48 0xfb 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101df2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101df6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x101df6 4 0x6a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101dea [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101dea :=
  Rest.liftedBlock (rest_l101dea code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101dea x hx)

theorem rest_l101df8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101df8 bytes_l101df8) (entryMap (live .l101df8))
      4 0x101df8 bytes_l101df8 b_l101df8 := by
  have f0 : InstrSpec 0x101df8 [0x48, 0x8D, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101df8) (leaR64Effect 0x101df8 6 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101df8 6 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (lea_r64_effect_step 0x101df8 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101e00 [0x48, 0x8D, 0x7C, 0x24, 0x0F] (fun s => s.RIP = 0x101e00) (leaR64Effect 0x101e00 7 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101e00 7 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x101e00 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e05 [0x31, 0xD2] (fun s => s.RIP = 0x101e05) (xorR32R32Effect 0x101e05 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101e05 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x101e05 0xd2 (by decide)) pre_rip
  have f3 : InstrSpec 0x101e07 [0xE8, 0xD4, 0xF7, 0x01, 0x00] (PushPre 0x101e07 5) (callEffect (fun _ => 0x1215e0) 0x101e0c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101e07 0x1215e0 0x101e0c).toInstrSpec (call_rel32_effect_step 0x101e07 0x1f7d4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e00) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e05) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e07) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215e0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101df8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101df8 :=
  Rest.liftedBlock (rest_l101df8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101df8 x hx)

theorem rest_l101e0c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e0c bytes_l101e0c) (entryMap (live .l101e0c))
      7 0x101e0c bytes_l101e0c b_l101e0c := by
  have f0 : InstrSpec 0x101e0c [0x0F, 0xB6, 0x4C, 0x24, 0x0F] (LoadPre 0x101e0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101e0c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101e0c 5 1 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x101e0c 5 1 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x101e0c 1 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101e11 [0x48, 0x83, 0xF9, 0x06] (fun s => s.RIP = 0x101e11) (cmpR64Imm8Effect 0x101e11 1 0x6)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x101e11 1 0x6).toInstrSpec (cmp_r64_imm8_effect_step 0x101e11 0x48 0xf9 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e15 [0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x101e15) (atFlags (condHolds 2) (setccR8Effect 0x101e15 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x101e15 3 0 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x101e15 2 0xc0 (by decide) (by decide) c)) pre_rip
  have f3 : InstrSpec 0x101e18 [0xB2, 0x3D] (fun s => s.RIP = 0x101e18) (movR8Imm8Effect 0x101e18 2 2 0x3d)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR8Imm8Effect_footprint 0x101e18 2 2 0x3d).toInstrSpec (mov_r8_imm8_effect_step 0x101e18 0xb2 (by decide) 0x3d) pre_rip
  have f4 : InstrSpec 0x101e1a [0xD2, 0xEA] (fun s => s.RIP = 0x101e1a) (shrR8ClEffect 0x101e1a 2 2)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR8ClEffect_footprint 0x101e1a 2 2).toInstrSpec (shr_r8_cl_effect_step 0x101e1a 0xea (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101e1c [0x84, 0xD0] (fun s => s.RIP = 0x101e1c) (testR8R8Effect 0x101e1c 2 0 2)
      [.gpr 0, .gpr 2] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x101e1c 2 0 2).toInstrSpec (test_r8_r8_effect_step 0x101e1c 0xd0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e11) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e15) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e18) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 53), (2, 59), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e1a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 53), (2, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e1c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 53), (2, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e1e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 65) (jcc_rel8_effect_step 0x101e1e 5 0x2c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101e0c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e0c :=
  Rest.liftedBlock (rest_l101e0c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e0c x hx)

theorem rest_l101e20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e20 bytes_l101e20) (entryMap (live .l101e20))
      7 0x101e20 bytes_l101e20 b_l101e20 := by
  have f0 : InstrSpec 0x101e20 [0xC7, 0x44, 0x24, 0x50, 0x03, 0x00, 0x00, 0x00] (StorePre 0x101e20 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101e20 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x101e20 8 (.sib 4 none 0 (.d8 0x50)) 0x3)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x101e20 8 (.sib 4 none 0 (.d8 0x50)) 0x3).toInstrSpec (mov_m32_imm32_effect_step 0x101e20 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide) 0x3) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x101e28 [0x48, 0x8D, 0x54, 0x24, 0x50] (fun s => s.RIP = 0x101e28) (leaR64Effect 0x101e28 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x101e28 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x101e28 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e2d [0xBE, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101e2d) (movR32Imm32Effect 0x101e2d 5 6 0xb)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x101e2d 5 6 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x101e2d 0xbe (by decide) 0xb) pre_rip
  have f3 : InstrSpec 0x101e32 [0x48, 0xC7, 0xC7, 0x00, 0x28, 0x20, 0x00] (fun s => s.RIP = 0x101e32) (movR64Imm32Effect 0x101e32 7 0x202800)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x101e32 7 0x202800).toInstrSpec (mov_r64_imm32_effect_step 0x101e32 0x48 0xc7 (by decide) (by decide) (by decide) 0x202800) pre_rip
  have f4 : InstrSpec 0x101e39 [0x48, 0xC7, 0xC1, 0xE0, 0x27, 0x20, 0x00] (fun s => s.RIP = 0x101e39) (movR64Imm32Effect 0x101e39 1 0x2027e0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x101e39 1 0x2027e0).toInstrSpec (mov_r64_imm32_effect_step 0x101e39 0x48 0xc1 (by decide) (by decide) (by decide) 0x2027e0) pre_rip
  have f5 : InstrSpec 0x101e40 [0x49, 0xC7, 0xC0, 0x10, 0x28, 0x20, 0x00] (fun s => s.RIP = 0x101e40) (movR64Imm32Effect 0x101e40 8 0x202810)
      [] [] [.reg 8, .rip] :=
    (movR64Imm32Effect_footprint 0x101e40 8 0x202810).toInstrSpec (mov_r64_imm32_effect_step 0x101e40 0x49 0xc0 (by decide) (by decide) (by decide) 0x202810) pre_rip
  have f6 : InstrSpec 0x101e47 [0xE8, 0x54, 0x77, 0x02, 0x00] (PushPre 0x101e47 5) (callEffect (fun _ => 0x1295a0) 0x101e4c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101e47 0x1295a0 0x101e4c).toInstrSpec (call_rel32_effect_step 0x101e47 0x27754 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x101e28) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 54), (4, 4), (5, 5)]) (p' := 0x101e2d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56)]) (p' := 0x101e32) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x101e39) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x101e40) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x101e47) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 60), (2, 54), (4, 64), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x1295a0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l101e20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e20 :=
  Rest.liftedBlock (rest_l101e20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e20 x hx)

theorem rest_l101e4c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e4c bytes_l101e4c) (entryMap (live .l101e4c))
      4 0x101e4c bytes_l101e4c b_l101e4c := by
  have f0 : InstrSpec 0x101e4c [0x48, 0x8B, 0x14, 0xCD, 0xB8, 0x22, 0x20, 0x00] (LoadPre 0x101e4c (fun s => AddrMode.addr (.abs (some 1) 3 0x2022b8) s (0x101e4c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101e4c 2 (.abs (some 1) 3 0x2022b8))
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x101e4c 2 (.abs (some 1) 3 0x2022b8)).toInstrSpec (mov_r64_m64_effect_step 0x101e4c 0x48 (by decide) 2 (.abs (some 1) 3 0x2022b8) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101e54 [0x48, 0x8D, 0x74, 0x24, 0x0F] (fun s => s.RIP = 0x101e54) (leaR64Effect 0x101e54 6 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101e54 6 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x101e54 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e59 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x101e59) (movR64R64Effect 0x101e59 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101e59 7 14).toInstrSpec (mov_r64_r64_effect_step 0x101e59 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101e5c [0xFF, 0x15, 0x6E, 0x1F, 0x10, 0x00] (GoesTo (CallMemPre 0x101e5c (.rip 0x101f6e)) (callEffect (callMemPtr 0x101e5c (.rip 0x101f6e)) (0x101e5c + BitVec.ofNat 64 (callMemLen (.rip 0x101f6e)))) 0x12a820) (callEffect (callMemPtr 0x101e5c (.rip 0x101f6e)) (0x101e5c + BitVec.ofNat 64 (callMemLen (.rip 0x101f6e))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x101e5c (.rip 0x101f6e)).toInstrSpec (call_m64_effect_step 0x101e5c (.rip 0x101f6e) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e54) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e59) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e5c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 59), (5, 5), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101e4c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e4c :=
  Rest.liftedBlock (rest_l101e4c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e4c x hx)

theorem rest_l101e62 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e62 bytes_l101e62) (entryMap (live .l101e62))
      5 0x101e62 bytes_l101e62 b_l101e62 := by
  have f0 : InstrSpec 0x101e62 [0x89, 0xD8] (fun s => s.RIP = 0x101e62) (movR32R32Effect 0x101e62 2 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x101e62 2 0 3).toInstrSpec (mov_r32_r32_effect_step 0x101e62 0xd8 (by decide)) pre_rip
  have f1 : InstrSpec 0x101e64 [0x48, 0x81, 0xC4, 0xE8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101e64) (addR64Imm32Effect 0x101e64 4 0xe8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x101e64 4 0xe8).toInstrSpec (add_r64_imm32_effect_step 0x101e64 0x48 0xc4 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e6b [0x5B] (PopPre 0x101e6b) (popR64Effect 0x101e6b 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101e6b 1 3).toInstrSpec (pop_r64_effect_step 0x101e6b 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101e6c [0x41, 0x5E] (PopPre 0x101e6c) (popR64Effect 0x101e6c 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101e6c 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101e6c 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101e6e [0xC3] (RetPre 0x101e6e) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101e6e).toInstrSpec (ret_effect_step 0x101e6e) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e64) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e6b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e6c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e6e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l101e62 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e62 :=
  Rest.liftedBlock (rest_l101e62 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e62 x hx)

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

theorem_by block_l100ea0_eval :
    program.runBlock (dialect code) ⟨.l100ea0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100f18_eval :
    program.runBlock (dialect code) ⟨.l100f18, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100f75_eval :
    program.runBlock (dialect code) ⟨.l100f75, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100f82_eval :
    program.runBlock (dialect code) ⟨.l100f82, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101003_eval :
    program.runBlock (dialect code) ⟨.l101003, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101011_eval :
    program.runBlock (dialect code) ⟨.l101011, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101023_eval :
    program.runBlock (dialect code) ⟨.l101023, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101026_eval :
    program.runBlock (dialect code) ⟨.l101026, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10106a_eval :
    program.runBlock (dialect code) ⟨.l10106a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101072_eval :
    program.runBlock (dialect code) ⟨.l101072, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1010ae_eval :
    program.runBlock (dialect code) ⟨.l1010ae, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10126c_eval :
    program.runBlock (dialect code) ⟨.l10126c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101295_eval :
    program.runBlock (dialect code) ⟨.l101295, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10132a_eval :
    program.runBlock (dialect code) ⟨.l10132a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10138a_eval :
    program.runBlock (dialect code) ⟨.l10138a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1013a0_eval :
    program.runBlock (dialect code) ⟨.l1013a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1013b8_eval :
    program.runBlock (dialect code) ⟨.l1013b8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1013c9_eval :
    program.runBlock (dialect code) ⟨.l1013c9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101409_eval :
    program.runBlock (dialect code) ⟨.l101409, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101432_eval :
    program.runBlock (dialect code) ⟨.l101432, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10143c_eval :
    program.runBlock (dialect code) ⟨.l10143c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101480_eval :
    program.runBlock (dialect code) ⟨.l101480, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10148e_eval :
    program.runBlock (dialect code) ⟨.l10148e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1014ab_eval :
    program.runBlock (dialect code) ⟨.l1014ab, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1014b5_eval :
    program.runBlock (dialect code) ⟨.l1014b5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1014e1_eval :
    program.runBlock (dialect code) ⟨.l1014e1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1014eb_eval :
    program.runBlock (dialect code) ⟨.l1014eb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101502_eval :
    program.runBlock (dialect code) ⟨.l101502, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101510_eval :
    program.runBlock (dialect code) ⟨.l101510, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10151b_eval :
    program.runBlock (dialect code) ⟨.l10151b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101529_eval :
    program.runBlock (dialect code) ⟨.l101529, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10154f_eval :
    program.runBlock (dialect code) ⟨.l10154f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101560_eval :
    program.runBlock (dialect code) ⟨.l101560, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101569_eval :
    program.runBlock (dialect code) ⟨.l101569, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10157a_eval :
    program.runBlock (dialect code) ⟨.l10157a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101583_eval :
    program.runBlock (dialect code) ⟨.l101583, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10158c_eval :
    program.runBlock (dialect code) ⟨.l10158c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1015e7_eval :
    program.runBlock (dialect code) ⟨.l1015e7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1015fc_eval :
    program.runBlock (dialect code) ⟨.l1015fc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10160b_eval :
    program.runBlock (dialect code) ⟨.l10160b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101624_eval :
    program.runBlock (dialect code) ⟨.l101624, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101633_eval :
    program.runBlock (dialect code) ⟨.l101633, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101648_eval :
    program.runBlock (dialect code) ⟨.l101648, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10165e_eval :
    program.runBlock (dialect code) ⟨.l10165e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1016be_eval :
    program.runBlock (dialect code) ⟨.l1016be, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101712_eval :
    program.runBlock (dialect code) ⟨.l101712, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101752_eval :
    program.runBlock (dialect code) ⟨.l101752, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10175e_eval :
    program.runBlock (dialect code) ⟨.l10175e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1017a9_eval :
    program.runBlock (dialect code) ⟨.l1017a9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1017b1_eval :
    program.runBlock (dialect code) ⟨.l1017b1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101823_eval :
    program.runBlock (dialect code) ⟨.l101823, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101831_eval :
    program.runBlock (dialect code) ⟨.l101831, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10185f_eval :
    program.runBlock (dialect code) ⟨.l10185f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1018b0_eval :
    program.runBlock (dialect code) ⟨.l1018b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101a3c_eval :
    program.runBlock (dialect code) ⟨.l101a3c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101a4f_eval :
    program.runBlock (dialect code) ⟨.l101a4f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101a65_eval :
    program.runBlock (dialect code) ⟨.l101a65, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101afa_eval :
    program.runBlock (dialect code) ⟨.l101afa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101b0d_eval :
    program.runBlock (dialect code) ⟨.l101b0d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101b1d_eval :
    program.runBlock (dialect code) ⟨.l101b1d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101c5e_eval :
    program.runBlock (dialect code) ⟨.l101c5e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101c63_eval :
    program.runBlock (dialect code) ⟨.l101c63, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101cca_eval :
    program.runBlock (dialect code) ⟨.l101cca, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101cd5_eval :
    program.runBlock (dialect code) ⟨.l101cd5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101d33_eval :
    program.runBlock (dialect code) ⟨.l101d33, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101d3e_eval :
    program.runBlock (dialect code) ⟨.l101d3e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101d75_eval :
    program.runBlock (dialect code) ⟨.l101d75, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101d96_eval :
    program.runBlock (dialect code) ⟨.l101d96, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101dcb_eval :
    program.runBlock (dialect code) ⟨.l101dcb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101dd0_eval :
    program.runBlock (dialect code) ⟨.l101dd0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101dea_eval :
    program.runBlock (dialect code) ⟨.l101dea, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101df8_eval :
    program.runBlock (dialect code) ⟨.l101df8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e0c_eval :
    program.runBlock (dialect code) ⟨.l101e0c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e20_eval :
    program.runBlock (dialect code) ⟨.l101e20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e4c_eval :
    program.runBlock (dialect code) ⟨.l101e4c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e62_eval :
    program.runBlock (dialect code) ⟨.l101e62, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
