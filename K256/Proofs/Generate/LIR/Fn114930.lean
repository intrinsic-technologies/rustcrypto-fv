import K256.Proofs.Generate.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Generate.LIR.Generated.Values

namespace K256.Proofs.Generate.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR

theorem rest_l114930_2 [Bindings] (code : CodeMap) :
    Rest (n := 129) code lifted (codeRange 0x114930 bytes_l114930) [(0, 127), (1, 118), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]
      20 0x1149c8 bytes_l114930_2 b_l114930_2 := by
  have f40 : InstrSpec 0x1149c8 [0x4C, 0x21, 0xF8] (fun s => s.RIP = 0x1149c8) (andR64R64Effect 0x1149c8 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1149c8 0 15).toInstrSpec (and_r64_r64_effect_step 0x1149c8 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x1149cb [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x1149cb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1149cb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1149cb 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1149cb 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1149cb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x1149d0 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1149d0) (movR64R64Effect 0x1149d0 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1149d0 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1149d0 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x1149d3 [0x48, 0x21, 0xD0] (fun s => s.RIP = 0x1149d3) (andR64R64Effect 0x1149d3 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1149d3 0 2).toInstrSpec (and_r64_r64_effect_step 0x1149d3 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x1149d6 [0x48, 0x21, 0xE8] (fun s => s.RIP = 0x1149d6) (andR64R64Effect 0x1149d6 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1149d6 0 5).toInstrSpec (and_r64_r64_effect_step 0x1149d6 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x1149d9 [0x4C, 0x89, 0xE1] (fun s => s.RIP = 0x1149d9) (movR64R64Effect 0x1149d9 1 12)
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1149d9 1 12).toInstrSpec (mov_r64_r64_effect_step 0x1149d9 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x1149dc [0x48, 0xC1, 0xE9, 0x30] (fun s => s.RIP = 0x1149dc) (shrR64Effect 0x1149dc 4 1 48)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1149dc 4 1 48).toInstrSpec (shr_r64_imm8_effect_step 0x1149dc 0x48 0xe9 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x1149e0 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x1149e0) (movR64R64Effect 0x1149e0 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1149e0 2 12).toInstrSpec (mov_r64_r64_effect_step 0x1149e0 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x1149e3 [0x4C, 0x31, 0xC2] (fun s => s.RIP = 0x1149e3) (xorR64R64Effect 0x1149e3 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1149e3 2 8).toInstrSpec (xor_r64_r64_effect_step 0x1149e3 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x1149e6 [0x4C, 0x31, 0xF8] (fun s => s.RIP = 0x1149e6) (xorR64R64Effect 0x1149e6 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1149e6 0 15).toInstrSpec (xor_r64_r64_effect_step 0x1149e6 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x1149e9 [0x48, 0x09, 0xD0] (fun s => s.RIP = 0x1149e9) (orR64R64Effect 0x1149e9 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1149e9 0 2).toInstrSpec (or_r64_r64_effect_step 0x1149e9 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x1149ec [0x0F, 0x94, 0xC0] (fun s => s.RIP = 0x1149ec) (atFlags (condHolds 4) (setccR8Effect 0x1149ec 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x1149ec 3 0 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1149ec 4 0xc0 (by decide) (by decide) c)) pre_rip
  have f52 : InstrSpec 0x1149ef [0x48, 0xBA, 0x2E, 0xFC, 0xFF, 0xFF, 0xFE, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x1149ef) (movR64Imm64Effect 0x1149ef 2 0xffffefffffc2e)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x1149ef 2 0xffffefffffc2e).toInstrSpec (mov_r64_imm64_effect_step 0x1149ef 0x48 0xba (by decide) (by decide) 0xffffefffffc2e) pre_rip
  have f53 : InstrSpec 0x1149f9 [0x49, 0x39, 0xD1] (fun s => s.RIP = 0x1149f9) (cmpR64R64Effect 0x1149f9 9 2)
      [.gpr 9, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1149f9 9 2).toInstrSpec (cmp_r64_r64_effect_step 0x1149f9 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x1149fc [0x0F, 0x97, 0xC2] (fun s => s.RIP = 0x1149fc) (atFlags (condHolds 7) (setccR8Effect 0x1149fc 3 2))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 2, .rip] :=
    (setccR8Effect_footprint 0x1149fc 3 2 7).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1149fc 7 0xc2 (by decide) (by decide) c)) pre_rip
  have f55 : InstrSpec 0x1149ff [0x48, 0x89, 0x7C, 0x24, 0x28] (StorePre 0x1149ff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1149ff + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1149ff 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1149ff 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1149ff 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x114a04 [0x20, 0xC2] (fun s => s.RIP = 0x114a04) (andR8R8Effect 0x114a04 2 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (andR8R8Effect_footprint 0x114a04 2 2 0).toInstrSpec (and_r8_r8_effect_step 0x114a04 0xc2 (by decide) (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x114a06 [0x08, 0xCA] (fun s => s.RIP = 0x114a06) (orR8R8Effect 0x114a06 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (orR8R8Effect_footprint 0x114a06 2 2 1).toInstrSpec (or_r8_r8_effect_step 0x114a06 0xca (by decide) (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x114a08 [0x0F, 0xB6, 0xFA] (fun s => s.RIP = 0x114a08) (movzxR32R8Effect 0x114a08 3 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x114a08 3 7 2).toInstrSpec (movzx_r32_r8_effect_step 0x114a08 0xfa (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x114a0b [0xE8, 0x40, 0x33, 0x01, 0x00] (PushPre 0x114a0b 5) (callEffect (fun _ => 0x127d50) 0x114a10)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x114a0b 0x127d50 0x114a10).toInstrSpec (call_rel32_effect_step 0x114a0b 0x13340 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f40 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 129), (1, 118), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149cb) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.exec (n := 131) (ρ' := [(0, 129), (1, 118), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149d0) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f42 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 132), (1, 118), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149d3) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f43 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 134), (1, 118), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149d6) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f44 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 136), (1, 118), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149d9) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f45 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 136), (1, 138), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149dc) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 136), (1, 140), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149e0) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f47 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 136), (1, 140), (2, 142), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149e3) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f48 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 136), (1, 140), (2, 144), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149e6) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f49 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 146), (1, 140), (2, 144), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149e9) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f50 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 149) f50 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 150) (ρ' := [(0, 148), (1, 140), (2, 144), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (19, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149ec) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f51 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 151), (1, 140), (2, 144), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (19, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149ef) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f52 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 151), (1, 140), (2, 153), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (19, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149f9) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f53 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 156) f53 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 157) (ρ' := [(0, 151), (1, 140), (2, 153), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (16, 155), (19, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149fc) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f54 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 151), (1, 140), (2, 158), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (16, 155), (19, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149ff) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.exec (n := 160) (ρ' := [(0, 151), (1, 140), (2, 158), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (16, 155), (19, 156), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a04) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f56 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 151), (1, 140), (2, 161), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a06) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f57 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 151), (1, 140), (2, 163), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a08) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f58 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 151), (1, 140), (2, 163), (3, 98), (4, 65), (5, 114), (6, 6), (7, 165), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a0b) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f59 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 151), (1, 140), (2, 163), (3, 98), (4, 167), (5, 114), (6, 6), (7, 165), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f59 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 169) (by decide) (by decide) rfl rfl

theorem rest_l114930_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x114930 bytes_l114930) [(0, 75), (1, 87), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]
      40 0x114981 bytes_l114930_1 b_l114930_1 := by
  have f20 : InstrSpec 0x114981 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x114981) (movR64R64Effect 0x114981 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x114981 2 13).toInstrSpec (mov_r64_r64_effect_step 0x114981 0x4c 0xea (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x114984 [0x48, 0x89, 0xCB] (fun s => s.RIP = 0x114984) (movR64R64Effect 0x114984 3 1)
      [.gpr 1] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x114984 3 1).toInstrSpec (mov_r64_r64_effect_step 0x114984 0x48 0xcb (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x114987 [0x48, 0xC1, 0xEB, 0x34] (fun s => s.RIP = 0x114987) (shrR64Effect 0x114987 4 3 52)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x114987 4 3 52).toInstrSpec (shr_r64_imm8_effect_step 0x114987 0x48 0xeb 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x11498b [0x48, 0x03, 0x5E, 0x10] (LoadPre 0x11498b (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x11498b + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x11498b 3 (.base 6 (.d8 0x10)))
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (addR64M64Effect_footprint 0x11498b 3 (.base 6 (.d8 0x10))).toInstrSpec (add_r64_m64_effect_step 0x11498b 0x48 (by decide) 3 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x11498f [0x4C, 0x21, 0xFA] (fun s => s.RIP = 0x11498f) (andR64R64Effect 0x11498f 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11498f 2 15).toInstrSpec (and_r64_r64_effect_step 0x11498f 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x114992 [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x114992) (movR64R64Effect 0x114992 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x114992 9 2).toInstrSpec (mov_r64_r64_effect_step 0x114992 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x114995 [0x48, 0x89, 0x54, 0x24, 0x10] (StorePre 0x114995 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x114995 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x114995 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x114995 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x114995 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x11499a [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x11499a) (movR64R64Effect 0x11499a 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11499a 2 1).toInstrSpec (mov_r64_r64_effect_step 0x11499a 0x48 0xca (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x11499d [0x4C, 0x21, 0xFA] (fun s => s.RIP = 0x11499d) (andR64R64Effect 0x11499d 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11499d 2 15).toInstrSpec (and_r64_r64_effect_step 0x11499d 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x1149a0 [0x48, 0x89, 0x54, 0x24, 0x18] (StorePre 0x1149a0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1149a0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1149a0 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1149a0 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1149a0 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x1149a5 [0x48, 0x89, 0xDD] (fun s => s.RIP = 0x1149a5) (movR64R64Effect 0x1149a5 5 3)
      [.gpr 3] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1149a5 5 3).toInstrSpec (mov_r64_r64_effect_step 0x1149a5 0x48 0xdd (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x1149a8 [0x48, 0xC1, 0xED, 0x34] (fun s => s.RIP = 0x1149a8) (shrR64Effect 0x1149a8 4 5 52)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR64Effect_footprint 0x1149a8 4 5 52).toInstrSpec (shr_r64_imm8_effect_step 0x1149a8 0x48 0xed 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x1149ac [0x48, 0x03, 0x6E, 0x18] (LoadPre 0x1149ac (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1149ac + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x1149ac 5 (.base 6 (.d8 0x18)))
      [.gpr 5, .gpr 6] [] [.reg 5, .flags, .rip] :=
    (addR64M64Effect_footprint 0x1149ac 5 (.base 6 (.d8 0x18))).toInstrSpec (add_r64_m64_effect_step 0x1149ac 0x48 (by decide) 5 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x1149b0 [0x48, 0x89, 0xD9] (fun s => s.RIP = 0x1149b0) (movR64R64Effect 0x1149b0 1 3)
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1149b0 1 3).toInstrSpec (mov_r64_r64_effect_step 0x1149b0 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x1149b3 [0x4C, 0x21, 0xF9] (fun s => s.RIP = 0x1149b3) (andR64R64Effect 0x1149b3 1 15)
      [.gpr 1, .gpr 15] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1149b3 1 15).toInstrSpec (and_r64_r64_effect_step 0x1149b3 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x1149b6 [0x48, 0x89, 0x4C, 0x24, 0x20] (StorePre 0x1149b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1149b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1149b6 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1149b6 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1149b6 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x1149bb [0x49, 0x89, 0xEC] (fun s => s.RIP = 0x1149bb) (movR64R64Effect 0x1149bb 12 5)
      [.gpr 5] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1149bb 12 5).toInstrSpec (mov_r64_r64_effect_step 0x1149bb 0x49 0xec (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x1149be [0x49, 0xC1, 0xEC, 0x34] (fun s => s.RIP = 0x1149be) (shrR64Effect 0x1149be 4 12 52)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR64Effect_footprint 0x1149be 4 12 52).toInstrSpec (shr_r64_imm8_effect_step 0x1149be 0x49 0xec 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x1149c2 [0x49, 0x01, 0xC4] (fun s => s.RIP = 0x1149c2) (addR64R64Effect 0x1149c2 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1149c2 12 0).toInstrSpec (add_r64_r64_effect_step 0x1149c2 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x1149c5 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x1149c5) (movR64R64Effect 0x1149c5 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1149c5 0 5).toInstrSpec (mov_r64_r64_effect_step 0x1149c5 0x48 0xe8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 75), (1, 87), (2, 92), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114984) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f21 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 75), (1, 87), (2, 92), (3, 94), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114987) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f22 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 75), (1, 87), (2, 92), (3, 96), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11498b) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f23 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 75), (1, 87), (2, 92), (3, 98), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11498f) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 75), (1, 87), (2, 100), (3, 98), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114992) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f25 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 75), (1, 87), (2, 100), (3, 98), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114995) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 75), (1, 87), (2, 100), (3, 98), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11499a) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 75), (1, 87), (2, 105), (3, 98), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11499d) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 75), (1, 87), (2, 107), (3, 98), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149a0) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.exec (n := 109) (ρ' := [(0, 75), (1, 87), (2, 107), (3, 98), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149a5) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f30 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 75), (1, 87), (2, 107), (3, 98), (4, 65), (5, 110), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149a8) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f31 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 75), (1, 87), (2, 107), (3, 98), (4, 65), (5, 112), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149ac) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f32 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 75), (1, 87), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149b0) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f33 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 75), (1, 116), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149b3) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 75), (1, 118), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149b6) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.exec (n := 120) (ρ' := [(0, 75), (1, 118), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149bb) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 75), (1, 118), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 121), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149be) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 75), (1, 118), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 123), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149c2) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 75), (1, 118), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149c5) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f39 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 127), (1, 118), (2, 107), (3, 98), (4, 65), (5, 114), (6, 6), (7, 7), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1149c8) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l114930_2 code

theorem rest_l114930 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x114930 bytes_l114930) (entryMap (live .l114930))
      60 0x114930 bytes_l114930 b_l114930 := by
  have f0 : InstrSpec 0x114930 [0x55] (PushPre 0x114930 1) (pushR64Effect 0x114930 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x114930 1 5).toInstrSpec (push_r64_effect_step 0x114930 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x114931 [0x41, 0x57] (PushPre 0x114931 2) (pushR64Effect 0x114931 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x114931 2 15).toInstrSpec (push_r64_rex_effect_step 0x114931 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x114933 [0x41, 0x56] (PushPre 0x114933 2) (pushR64Effect 0x114933 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x114933 2 14).toInstrSpec (push_r64_rex_effect_step 0x114933 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x114935 [0x41, 0x55] (PushPre 0x114935 2) (pushR64Effect 0x114935 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x114935 2 13).toInstrSpec (push_r64_rex_effect_step 0x114935 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x114937 [0x41, 0x54] (PushPre 0x114937 2) (pushR64Effect 0x114937 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x114937 2 12).toInstrSpec (push_r64_rex_effect_step 0x114937 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x114939 [0x53] (PushPre 0x114939 1) (pushR64Effect 0x114939 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x114939 1 3).toInstrSpec (push_r64_effect_step 0x114939 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x11493a [0x48, 0x83, 0xEC, 0x38] (fun s => s.RIP = 0x11493a) (subR64Imm8Effect 0x11493a 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x11493a 4 0x38).toInstrSpec (sub_r64_imm8_effect_step 0x11493a 0x48 0xec 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11493e [0x48, 0x8B, 0x46, 0x20] (LoadPre 0x11493e (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x11493e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11493e 0 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11493e 0 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x11493e 0x48 (by decide) 0 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x114942 [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x114942) (movR64R64Effect 0x114942 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x114942 13 0).toInstrSpec (mov_r64_r64_effect_step 0x114942 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x114945 [0x49, 0xC1, 0xED, 0x30] (fun s => s.RIP = 0x114945) (shrR64Effect 0x114945 4 13 48)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR64Effect_footprint 0x114945 4 13 48).toInstrSpec (shr_r64_imm8_effect_step 0x114945 0x49 0xed 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x114949 [0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x114949) (movR64Imm64Effect 0x114949 8 0xffffffffffff)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x114949 8 0xffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x114949 0x49 0xb8 (by decide) (by decide) 0xffffffffffff) pre_rip
  have f11 : InstrSpec 0x114953 [0x4C, 0x21, 0xC0] (fun s => s.RIP = 0x114953) (andR64R64Effect 0x114953 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x114953 0 8).toInstrSpec (and_r64_r64_effect_step 0x114953 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x114956 [0x49, 0xBE, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x114956) (movR64Imm64Effect 0x114956 14 0x1000003d1)
      [] [] [.reg 14, .rip] :=
    (movR64Imm64Effect_footprint 0x114956 14 0x1000003d1).toInstrSpec (mov_r64_imm64_effect_step 0x114956 0x49 0xbe (by decide) (by decide) 0x1000003d1) pre_rip
  have f13 : InstrSpec 0x114960 [0x4D, 0x0F, 0xAF, 0xEE] (fun s => s.RIP = 0x114960) (imulR64R64Effect 0x114960 4 13 14)
      [.gpr 13, .gpr 14] [] [.reg 13, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x114960 4 13 14).toInstrSpec (imul_r64_r64_effect_step 0x114960 0x4d (by decide) 0xee (by decide)) pre_rip
  have f14 : InstrSpec 0x114964 [0x4C, 0x03, 0x2E] (LoadPre 0x114964 (fun s => AddrMode.addr (.base 6 .none) s (0x114964 + BitVec.ofNat 64 3)) 8) (addR64M64Effect 0x114964 13 (.base 6 .none))
      [.gpr 13, .gpr 6] [] [.reg 13, .flags, .rip] :=
    (addR64M64Effect_footprint 0x114964 13 (.base 6 .none)).toInstrSpec (add_r64_m64_effect_step 0x114964 0x4c (by decide) 5 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x114967 [0x4C, 0x89, 0xE9] (fun s => s.RIP = 0x114967) (movR64R64Effect 0x114967 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x114967 1 13).toInstrSpec (mov_r64_r64_effect_step 0x114967 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11496a [0x48, 0xC1, 0xE9, 0x34] (fun s => s.RIP = 0x11496a) (shrR64Effect 0x11496a 4 1 52)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x11496a 4 1 52).toInstrSpec (shr_r64_imm8_effect_step 0x11496a 0x48 0xe9 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x11496e [0x48, 0x03, 0x4E, 0x08] (LoadPre 0x11496e (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x11496e + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x11496e 1 (.base 6 (.d8 0x8)))
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (addR64M64Effect_footprint 0x11496e 1 (.base 6 (.d8 0x8))).toInstrSpec (add_r64_m64_effect_step 0x11496e 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x114972 [0x48, 0x89, 0x4C, 0x24, 0x30] (StorePre 0x114972 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x114972 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x114972 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x114972 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x114972 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x114977 [0x49, 0xBF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x114977) (movR64Imm64Effect 0x114977 15 0xfffffffffffff)
      [] [] [.reg 15, .rip] :=
    (movR64Imm64Effect_footprint 0x114977 15 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x114977 0x49 0xbf (by decide) (by decide) 0xfffffffffffff) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114931) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114933) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114935) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114937) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114939) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11493a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11493e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114942) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 69), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114945) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 67), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114949) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 67), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114953) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114956) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 75), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 71), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114960) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 75), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 79), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114964) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 75), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114967) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 75), (1, 83), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11496a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 75), (1, 85), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11496e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 75), (1, 87), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114972) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 75), (1, 87), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114977) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 75), (1, 87), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 73), (10, 10), (11, 11), (12, 12), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114981) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l114930_1 code

theorem block_l114930 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l114930 :=
  Rest.liftedBlock (rest_l114930 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l114930 x hx)

theorem rest_l114a10_2 [Bindings] (code : CodeMap) :
    Rest (n := 130) code lifted (codeRange 0x114a10 bytes_l114a10) [(0, 125), (1, 105), (2, 111), (3, 3), (4, 4), (5, 5), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]
      10 0x114aa3 bytes_l114a10_2 b_l114a10_2 := by
  have f40 : InstrSpec 0x114aa3 [0x48, 0x89, 0x70, 0x18] (StorePre 0x114aa3 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x114aa3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114aa3 6 (.base 0 (.d8 0x18)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x114aa3 6 (.base 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x114aa3 0x48 (by decide) 6 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f41 : InstrSpec 0x114aa7 [0x48, 0x89, 0x78, 0x20] (StorePre 0x114aa7 4 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x114aa7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114aa7 7 (.base 0 (.d8 0x20)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x114aa7 7 (.base 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x114aa7 0x48 (by decide) 7 (.base 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x114aab [0x48, 0x83, 0xC4, 0x38] (fun s => s.RIP = 0x114aab) (addR64Imm8Effect 0x114aab 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x114aab 4 0x38).toInstrSpec (add_r64_imm8_effect_step 0x114aab 0x48 0xc4 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x114aaf [0x5B] (PopPre 0x114aaf) (popR64Effect 0x114aaf 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x114aaf 1 3).toInstrSpec (pop_r64_effect_step 0x114aaf 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f44 : InstrSpec 0x114ab0 [0x41, 0x5C] (PopPre 0x114ab0) (popR64Effect 0x114ab0 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x114ab0 2 12).toInstrSpec (pop_r64_rex_effect_step 0x114ab0 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f45 : InstrSpec 0x114ab2 [0x41, 0x5D] (PopPre 0x114ab2) (popR64Effect 0x114ab2 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x114ab2 2 13).toInstrSpec (pop_r64_rex_effect_step 0x114ab2 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f46 : InstrSpec 0x114ab4 [0x41, 0x5E] (PopPre 0x114ab4) (popR64Effect 0x114ab4 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x114ab4 2 14).toInstrSpec (pop_r64_rex_effect_step 0x114ab4 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f47 : InstrSpec 0x114ab6 [0x41, 0x5F] (PopPre 0x114ab6) (popR64Effect 0x114ab6 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x114ab6 2 15).toInstrSpec (pop_r64_rex_effect_step 0x114ab6 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f48 : InstrSpec 0x114ab8 [0x5D] (PopPre 0x114ab8) (popR64Effect 0x114ab8 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x114ab8 1 5).toInstrSpec (pop_r64_effect_step 0x114ab8 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f49 : InstrSpec 0x114ab9 [0xC3] (RetPre 0x114ab9) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x114ab9).toInstrSpec (ret_effect_step 0x114ab9) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 130) (RestInside.exec (n := 130) (ρ' := [(0, 125), (1, 105), (2, 111), (3, 3), (4, 4), (5, 5), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114aa7) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 131) (RestInside.exec (n := 131) (ρ' := [(0, 125), (1, 105), (2, 111), (3, 3), (4, 4), (5, 5), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114aab) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f42 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 125), (1, 105), (2, 111), (3, 3), (4, 132), (5, 5), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114aaf) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f43 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 135) f43 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 136) (ρ' := [(0, 125), (1, 105), (2, 111), (3, 134), (4, 135), (5, 5), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114ab0) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f44 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 138) f44 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 139) (ρ' := [(0, 125), (1, 105), (2, 111), (3, 134), (4, 138), (5, 5), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 137), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114ab2) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f45 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 141) f45 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 142) (ρ' := [(0, 125), (1, 105), (2, 111), (3, 134), (4, 141), (5, 5), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 137), (13, 140), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114ab4) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f46 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 144) f46 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 145) (ρ' := [(0, 125), (1, 105), (2, 111), (3, 134), (4, 144), (5, 5), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 137), (13, 140), (14, 143), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114ab6) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f47 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 147) f47 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 148) (ρ' := [(0, 125), (1, 105), (2, 111), (3, 134), (4, 147), (5, 5), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 137), (13, 140), (14, 143), (15, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114ab8) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f48 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 150) f48 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 151) (ρ' := [(0, 125), (1, 105), (2, 111), (3, 134), (4, 150), (5, 149), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 137), (13, 140), (14, 143), (15, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114ab9) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f49 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 153) f49 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 154) (ρ' := [(0, 125), (1, 105), (2, 111), (3, 134), (4, 153), (5, 149), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 137), (13, 140), (14, 143), (15, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) f49 (by decide) rfl rfl rfl (by decide)

theorem rest_l114a10_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x114a10 bytes_l114a10) [(0, 91), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 89), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      30 0x114a5f bytes_l114a10_1 b_l114a10_1 := by
  have f20 : InstrSpec 0x114a5f [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x114a5f) (negR64Effect 0x114a5f 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x114a5f 0).toInstrSpec (neg_r64_effect_step 0x114a5f 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x114a62 [0x49, 0x21, 0xC7] (fun s => s.RIP = 0x114a62) (andR64R64Effect 0x114a62 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x114a62 15 0).toInstrSpec (and_r64_r64_effect_step 0x114a62 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x114a65 [0x4D, 0x21, 0xFE] (fun s => s.RIP = 0x114a65) (andR64R64Effect 0x114a65 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x114a65 14 15).toInstrSpec (and_r64_r64_effect_step 0x114a65 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x114a68 [0x4D, 0x31, 0xDE] (fun s => s.RIP = 0x114a68) (xorR64R64Effect 0x114a68 14 11)
      [.gpr 14, .gpr 11] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x114a68 14 11).toInstrSpec (xor_r64_r64_effect_step 0x114a68 0x4d 0xde (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x114a6b [0x48, 0x33, 0x4C, 0x24, 0x30] (LoadPre 0x114a6b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x114a6b + BitVec.ofNat 64 5)) 8) (xorR64M64Effect 0x114a6b 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x114a6b 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (xor_r64_m64_effect_step 0x114a6b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x114a70 [0x4C, 0x21, 0xF9] (fun s => s.RIP = 0x114a70) (andR64R64Effect 0x114a70 1 15)
      [.gpr 1, .gpr 15] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x114a70 1 15).toInstrSpec (and_r64_r64_effect_step 0x114a70 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x114a73 [0x4C, 0x31, 0xD1] (fun s => s.RIP = 0x114a73) (xorR64R64Effect 0x114a73 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x114a73 1 10).toInstrSpec (xor_r64_r64_effect_step 0x114a73 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x114a76 [0x48, 0x31, 0xDA] (fun s => s.RIP = 0x114a76) (xorR64R64Effect 0x114a76 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x114a76 2 3).toInstrSpec (xor_r64_r64_effect_step 0x114a76 0x48 0xda (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x114a79 [0x4C, 0x21, 0xFA] (fun s => s.RIP = 0x114a79) (andR64R64Effect 0x114a79 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x114a79 2 15).toInstrSpec (and_r64_r64_effect_step 0x114a79 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x114a7c [0x4C, 0x31, 0xC2] (fun s => s.RIP = 0x114a7c) (xorR64R64Effect 0x114a7c 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x114a7c 2 8).toInstrSpec (xor_r64_r64_effect_step 0x114a7c 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x114a7f [0x48, 0x31, 0xEE] (fun s => s.RIP = 0x114a7f) (xorR64R64Effect 0x114a7f 6 5)
      [.gpr 6, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x114a7f 6 5).toInstrSpec (xor_r64_r64_effect_step 0x114a7f 0x48 0xee (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x114a82 [0x4C, 0x21, 0xFE] (fun s => s.RIP = 0x114a82) (andR64R64Effect 0x114a82 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x114a82 6 15).toInstrSpec (and_r64_r64_effect_step 0x114a82 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x114a85 [0x48, 0x33, 0x74, 0x24, 0x08] (LoadPre 0x114a85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x114a85 + BitVec.ofNat 64 5)) 8) (xorR64M64Effect 0x114a85 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x114a85 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (xor_r64_m64_effect_step 0x114a85 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x114a8a [0x4C, 0x31, 0xE7] (fun s => s.RIP = 0x114a8a) (xorR64R64Effect 0x114a8a 7 12)
      [.gpr 7, .gpr 12] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x114a8a 7 12).toInstrSpec (xor_r64_r64_effect_step 0x114a8a 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x114a8d [0x48, 0x21, 0xC7] (fun s => s.RIP = 0x114a8d) (andR64R64Effect 0x114a8d 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x114a8d 7 0).toInstrSpec (and_r64_r64_effect_step 0x114a8d 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x114a90 [0x4C, 0x31, 0xE7] (fun s => s.RIP = 0x114a90) (xorR64R64Effect 0x114a90 7 12)
      [.gpr 7, .gpr 12] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x114a90 7 12).toInstrSpec (xor_r64_r64_effect_step 0x114a90 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x114a93 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x114a93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x114a93 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x114a93 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x114a93 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x114a93 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x114a98 [0x4C, 0x89, 0x30] (StorePre 0x114a98 3 (fun s => AddrMode.addr (.base 0 .none) s (0x114a98 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x114a98 14 (.base 0 .none))
      [.gpr 14, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x114a98 14 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x114a98 0x4c (by decide) 6 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x114a9b [0x48, 0x89, 0x48, 0x08] (StorePre 0x114a9b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x114a9b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114a9b 1 (.base 0 (.d8 0x8)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x114a9b 1 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x114a9b 0x48 (by decide) 1 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x114a9f [0x48, 0x89, 0x50, 0x10] (StorePre 0x114a9f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x114a9f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114a9f 2 (.base 0 (.d8 0x10)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x114a9f 2 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x114a9f 0x48 (by decide) 2 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 89), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a62) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 93), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 89), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a65) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 93), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 97), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a68) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 93), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a6b) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 93), (1, 101), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a70) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 93), (1, 103), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a73) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 93), (1, 105), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a76) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 93), (1, 105), (2, 107), (3, 3), (4, 4), (5, 5), (6, 77), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a79) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 93), (1, 105), (2, 109), (3, 3), (4, 4), (5, 5), (6, 77), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a7c) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 93), (1, 105), (2, 111), (3, 3), (4, 4), (5, 5), (6, 77), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a7f) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 93), (1, 105), (2, 111), (3, 3), (4, 4), (5, 5), (6, 113), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a82) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 93), (1, 105), (2, 111), (3, 3), (4, 4), (5, 5), (6, 115), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a85) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 93), (1, 105), (2, 111), (3, 3), (4, 4), (5, 5), (6, 117), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a8a) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 93), (1, 105), (2, 111), (3, 3), (4, 4), (5, 5), (6, 117), (7, 119), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a8d) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f34 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 93), (1, 105), (2, 111), (3, 3), (4, 4), (5, 5), (6, 117), (7, 121), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a90) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f35 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 93), (1, 105), (2, 111), (3, 3), (4, 4), (5, 5), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a93) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f36 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 125), (1, 105), (2, 111), (3, 3), (4, 4), (5, 5), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a98) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.exec (n := 127) (ρ' := [(0, 125), (1, 105), (2, 111), (3, 3), (4, 4), (5, 5), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a9b) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 128) (RestInside.exec (n := 128) (ρ' := [(0, 125), (1, 105), (2, 111), (3, 3), (4, 4), (5, 5), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a9f) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 129) (RestInside.exec (n := 129) (ρ' := [(0, 125), (1, 105), (2, 111), (3, 3), (4, 4), (5, 5), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 99), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114aa3) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l114a10_2 code

theorem rest_l114a10 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x114a10 bytes_l114a10) (entryMap (live .l114a10))
      50 0x114a10 bytes_l114a10 b_l114a10 := by
  have f0 : InstrSpec 0x114a10 [0x4C, 0x8B, 0x5C, 0x24, 0x10] (LoadPre 0x114a10 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x114a10 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x114a10 11 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x114a10 11 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x114a10 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x114a15 [0x4D, 0x01, 0xDE] (fun s => s.RIP = 0x114a15) (addR64R64Effect 0x114a15 14 11)
      [.gpr 14, .gpr 11] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114a15 14 11).toInstrSpec (add_r64_r64_effect_step 0x114a15 0x4d 0xde (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x114a18 [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x114a18) (movR64R64Effect 0x114a18 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x114a18 1 14).toInstrSpec (mov_r64_r64_effect_step 0x114a18 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x114a1b [0x48, 0xC1, 0xE9, 0x34] (fun s => s.RIP = 0x114a1b) (shrR64Effect 0x114a1b 4 1 52)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x114a1b 4 1 52).toInstrSpec (shr_r64_imm8_effect_step 0x114a1b 0x48 0xe9 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x114a1f [0x4C, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x114a1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x114a1f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x114a1f 10 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x114a1f 10 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x114a1f 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x114a24 [0x4C, 0x01, 0xD1] (fun s => s.RIP = 0x114a24) (addR64R64Effect 0x114a24 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114a24 1 10).toInstrSpec (add_r64_r64_effect_step 0x114a24 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x114a27 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x114a27) (movR64R64Effect 0x114a27 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x114a27 2 1).toInstrSpec (mov_r64_r64_effect_step 0x114a27 0x48 0xca (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x114a2a [0x48, 0xC1, 0xEA, 0x34] (fun s => s.RIP = 0x114a2a) (shrR64Effect 0x114a2a 4 2 52)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x114a2a 4 2 52).toInstrSpec (shr_r64_imm8_effect_step 0x114a2a 0x48 0xea 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x114a2e [0x4C, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x114a2e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x114a2e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x114a2e 8 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x114a2e 8 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x114a2e 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x114a33 [0x4C, 0x01, 0xC2] (fun s => s.RIP = 0x114a33) (addR64R64Effect 0x114a33 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114a33 2 8).toInstrSpec (add_r64_r64_effect_step 0x114a33 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x114a36 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x114a36) (movR64R64Effect 0x114a36 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x114a36 6 2).toInstrSpec (mov_r64_r64_effect_step 0x114a36 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x114a39 [0x48, 0xC1, 0xEE, 0x34] (fun s => s.RIP = 0x114a39) (shrR64Effect 0x114a39 4 6 52)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x114a39 4 6 52).toInstrSpec (shr_r64_imm8_effect_step 0x114a39 0x48 0xee 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x114a3d [0x48, 0x03, 0x74, 0x24, 0x08] (LoadPre 0x114a3d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x114a3d + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x114a3d 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (addR64M64Effect_footprint 0x114a3d 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (add_r64_m64_effect_step 0x114a3d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x114a42 [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x114a42) (movR64R64Effect 0x114a42 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x114a42 7 6).toInstrSpec (mov_r64_r64_effect_step 0x114a42 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x114a45 [0x48, 0xC1, 0xEF, 0x34] (fun s => s.RIP = 0x114a45) (shrR64Effect 0x114a45 4 7 52)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x114a45 4 7 52).toInstrSpec (shr_r64_imm8_effect_step 0x114a45 0x48 0xef 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x114a49 [0x4C, 0x01, 0xE7] (fun s => s.RIP = 0x114a49) (addR64R64Effect 0x114a49 7 12)
      [.gpr 7, .gpr 12] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x114a49 7 12).toInstrSpec (add_r64_r64_effect_step 0x114a49 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x114a4c [0x49, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x114a4c) (movR64Imm64Effect 0x114a4c 9 0xffffffffffff)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x114a4c 9 0xffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x114a4c 0x49 0xb9 (by decide) (by decide) 0xffffffffffff) pre_rip
  have f17 : InstrSpec 0x114a56 [0x4C, 0x21, 0xCF] (fun s => s.RIP = 0x114a56) (andR64R64Effect 0x114a56 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x114a56 7 9).toInstrSpec (and_r64_r64_effect_step 0x114a56 0x4c 0xcf (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x114a59 [0x4D, 0x31, 0xEE] (fun s => s.RIP = 0x114a59) (xorR64R64Effect 0x114a59 14 13)
      [.gpr 14, .gpr 13] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x114a59 14 13).toInstrSpec (xor_r64_r64_effect_step 0x114a59 0x4d 0xee (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x114a5c [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x114a5c) (movzxR32R8Effect 0x114a5c 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x114a5c 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x114a5c 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a15) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a18) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (3, 3), (4, 4), (5, 5), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a1b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (5, 5), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a1f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (5, 5), (10, 61), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a24) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (3, 3), (4, 4), (5, 5), (10, 61), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a27) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 63), (2, 65), (3, 3), (4, 4), (5, 5), (10, 61), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a2a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 63), (2, 67), (3, 3), (4, 4), (5, 5), (10, 61), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a2e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 63), (2, 67), (3, 3), (4, 4), (5, 5), (8, 69), (10, 61), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a33) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (8, 69), (10, 61), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a36) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 73), (8, 69), (10, 61), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a39) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 75), (8, 69), (10, 61), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a3d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (8, 69), (10, 61), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a42) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 79), (8, 69), (10, 61), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a45) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 81), (8, 69), (10, 61), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a49) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 83), (8, 69), (10, 61), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a4c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 83), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a56) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a59) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 89), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a5c) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 91), (1, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 77), (7, 87), (8, 69), (9, 85), (10, 61), (11, 53), (12, 12), (13, 13), (14, 89), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114a5f) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l114a10_1 code

theorem block_l114a10 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l114a10 :=
  Rest.liftedBlock (rest_l114a10 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l114a10 x hx)

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

theorem_by block_l114930_eval :
    program.runBlock (dialect code) ⟨.l114930, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l114a10_eval :
    program.runBlock (dialect code) ⟨.l114a10, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Generate.LIR
