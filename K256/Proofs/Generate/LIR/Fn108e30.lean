import K256.Proofs.Generate.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Generate.LIR.Generated.Values

namespace K256.Proofs.Generate.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR

theorem rest_l108e30_2 [Bindings] (code : CodeMap) :
    Rest (n := 112) code lifted (codeRange 0x108e30 bytes_l108e30) [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      14 0x108f23 bytes_l108e30_2 b_l108e30_2 := by
  have f40 : InstrSpec 0x108f23 [0x48, 0xC7, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108f23 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x108f23 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x108f23 (.sib 4 none 0 (.d32 0xd0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108f23 (.sib 4 none 0 (.d32 0xd0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108f23 0x48 (by decide) (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f41 : InstrSpec 0x108f2f [0x49, 0x8B, 0x40, 0x18] (LoadPre 0x108f2f (fun s => AddrMode.addr (.base 8 (.d8 0x18)) s (0x108f2f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108f2f 0 (.base 8 (.d8 0x18)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108f2f 0 (.base 8 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x108f2f 0x49 (by decide) 0 (.base 8 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f42 : InstrSpec 0x108f33 [0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x108f33 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x108f33 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108f33 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108f33 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m64_r64_effect_step 0x108f33 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f43 : InstrSpec 0x108f3b [0x49, 0x8B, 0x40, 0x10] (LoadPre 0x108f3b (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x108f3b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108f3b 0 (.base 8 (.d8 0x10)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108f3b 0 (.base 8 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x108f3b 0x49 (by decide) 0 (.base 8 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f44 : InstrSpec 0x108f3f [0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x108f3f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x108f3f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108f3f 0 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108f3f 0 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m64_r64_effect_step 0x108f3f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x108f47 [0x49, 0x8B, 0x00] (LoadPre 0x108f47 (fun s => AddrMode.addr (.base 8 .none) s (0x108f47 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108f47 0 (.base 8 .none))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108f47 0 (.base 8 .none)).toInstrSpec (mov_r64_m64_effect_step 0x108f47 0x49 (by decide) 0 (.base 8 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f46 : InstrSpec 0x108f4a [0x49, 0x8B, 0x48, 0x08] (LoadPre 0x108f4a (fun s => AddrMode.addr (.base 8 (.d8 0x8)) s (0x108f4a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108f4a 1 (.base 8 (.d8 0x8)))
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x108f4a 1 (.base 8 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x108f4a 0x49 (by decide) 1 (.base 8 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f47 : InstrSpec 0x108f4e [0x48, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x108f4e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x108f4e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108f4e 1 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108f4e 1 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m64_r64_effect_step 0x108f4e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x108f56 [0x48, 0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x108f56 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x108f56 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108f56 0 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108f56 0 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x108f56 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x108f5e [0xC6, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x00] (StorePre 0x108f5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x108f5e + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x108f5e (.sib 4 none 0 (.d32 0x118)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x108f5e (.sib 4 none 0 (.d32 0x118)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x108f5e (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x108f66 [0xBD, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108f66) (movR32Imm32Effect 0x108f66 5 5 0x1)
      [] [] [.reg 5, .rip] :=
    (movR32Imm32Effect_footprint 0x108f66 5 5 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x108f66 0xbd (by decide) 0x1) pre_rip
  have f51 : InstrSpec 0x108f6b [0xBA, 0x4F, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x108f6b) (movR32Imm32Effect 0x108f6b 5 2 0x24f)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x108f6b 5 2 0x24f).toInstrSpec (mov_r32_imm32_effect_step 0x108f6b 0xba (by decide) 0x24f) pre_rip
  have f52 : InstrSpec 0x108f70 [0x4C, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x108f70) (leaR64Effect 0x108f70 14 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x108f70 14 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x108f70 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f2f) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f41 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 113), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f33) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 113), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f3b) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f43 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 116), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f3f) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.exec (n := 118) (ρ' := [(0, 116), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f47) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f45 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 119), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f4a) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f4e) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.exec (n := 123) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f56) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 124) (RestInside.exec (n := 124) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f5e) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 125) (RestInside.exec (n := 125) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f66) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f50 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 119), (1, 121), (2, 2), (3, 3), (4, 65), (5, 126), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f6b) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f51 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 119), (1, 121), (2, 128), (3, 3), (4, 65), (5, 126), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f70) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f52 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 119), (1, 121), (2, 128), (3, 3), (4, 65), (5, 126), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 130), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f75) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 132) (jmp_rel32_effect_step 0x108f75 0x26a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l108e30_1 [Bindings] (code : CodeMap) :
    Rest (n := 86) code lifted (codeRange 0x108e30 bytes_l108e30) [(0, 84), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      34 0x108e90 bytes_l108e30_1 b_l108e30_1 := by
  have f20 : InstrSpec 0x108e90 [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x108e90 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x108e90 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e90 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108e90 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x108e90 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x108e98 [0x48, 0x8B, 0x02] (LoadPre 0x108e98 (fun s => AddrMode.addr (.base 2 .none) s (0x108e98 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108e98 0 (.base 2 .none))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108e98 0 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x108e98 0x48 (by decide) 0 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x108e9b [0x48, 0x89, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x108e9b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x108e9b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e9b 2 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108e9b 2 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x108e9b 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x108ea3 [0x48, 0x8B, 0x4A, 0x08] (LoadPre 0x108ea3 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x108ea3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108ea3 1 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x108ea3 1 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x108ea3 0x48 (by decide) 1 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x108ea7 [0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x108ea7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x108ea7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108ea7 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108ea7 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x108ea7 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x108eaf [0x48, 0x89, 0x44, 0x24, 0x78] (StorePre 0x108eaf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x108eaf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108eaf 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108eaf 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x108eaf 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x108eb4 [0xC6, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108eb4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x108eb4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x108eb4 (.sib 4 none 0 (.d32 0x98)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x108eb4 (.sib 4 none 0 (.d32 0x98)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x108eb4 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x108ebc [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x108ebc (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x108ebc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108ebc 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108ebc 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x108ebc 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x108ec0 [0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x108ec0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x108ec0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108ec0 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108ec0 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x108ec0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x108ec8 [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x108ec8 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x108ec8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108ec8 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108ec8 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x108ec8 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x108ecc [0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x108ecc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x108ecc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108ecc 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108ecc 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x108ecc 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x108ed4 [0x48, 0x8B, 0x06] (LoadPre 0x108ed4 (fun s => AddrMode.addr (.base 6 .none) s (0x108ed4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108ed4 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108ed4 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x108ed4 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x108ed7 [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x108ed7 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x108ed7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108ed7 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x108ed7 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x108ed7 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x108edb [0x48, 0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x108edb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x108edb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108edb 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108edb 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x108edb 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x108ee3 [0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x108ee3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x108ee3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108ee3 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108ee3 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x108ee3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x108eeb [0xC6, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108eeb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x108eeb + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x108eeb (.sib 4 none 0 (.d32 0xc8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x108eeb (.sib 4 none 0 (.d32 0xc8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x108eeb (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x108ef3 [0x48, 0xC7, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108ef3 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x108ef3 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x108ef3 (.sib 4 none 0 (.d32 0xf0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108ef3 (.sib 4 none 0 (.d32 0xf0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108ef3 0x48 (by decide) (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x108eff [0x48, 0xC7, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108eff 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x108eff + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x108eff (.sib 4 none 0 (.d32 0xe8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108eff (.sib 4 none 0 (.d32 0xe8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108eff 0x48 (by decide) (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x108f0b [0x48, 0xC7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108f0b 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x108f0b + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x108f0b (.sib 4 none 0 (.d32 0xe0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108f0b (.sib 4 none 0 (.d32 0xe0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108f0b 0x48 (by decide) (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x108f17 [0x48, 0xC7, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108f17 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x108f17 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x108f17 (.sib 4 none 0 (.d32 0xd8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108f17 (.sib 4 none 0 (.d32 0xd8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108f17 0x48 (by decide) (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 84), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e98) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e9b) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 87), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ea3) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 87), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ea7) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 87), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108eaf) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 87), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108eb4) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 87), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ebc) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ec0) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 95), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ec8) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 98), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ecc) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 98), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ed4) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 101), (1, 90), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ed7) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108edb) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.exec (n := 105) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ee3) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108eeb) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ef3) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.exec (n := 108) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108eff) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 109) (RestInside.exec (n := 109) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f0b) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f17) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.exec (n := 111) (ρ' := [(0, 101), (1, 103), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f23) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l108e30_2 code

theorem rest_l108e30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108e30 bytes_l108e30) (entryMap (live .l108e30))
      54 0x108e30 bytes_l108e30 b_l108e30 := by
  have f0 : InstrSpec 0x108e30 [0x55] (PushPre 0x108e30 1) (pushR64Effect 0x108e30 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108e30 1 5).toInstrSpec (push_r64_effect_step 0x108e30 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x108e31 [0x41, 0x57] (PushPre 0x108e31 2) (pushR64Effect 0x108e31 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108e31 2 15).toInstrSpec (push_r64_rex_effect_step 0x108e31 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x108e33 [0x41, 0x56] (PushPre 0x108e33 2) (pushR64Effect 0x108e33 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108e33 2 14).toInstrSpec (push_r64_rex_effect_step 0x108e33 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x108e35 [0x41, 0x55] (PushPre 0x108e35 2) (pushR64Effect 0x108e35 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108e35 2 13).toInstrSpec (push_r64_rex_effect_step 0x108e35 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x108e37 [0x41, 0x54] (PushPre 0x108e37 2) (pushR64Effect 0x108e37 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108e37 2 12).toInstrSpec (push_r64_rex_effect_step 0x108e37 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x108e39 [0x53] (PushPre 0x108e39 1) (pushR64Effect 0x108e39 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108e39 1 3).toInstrSpec (push_r64_effect_step 0x108e39 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x108e3a [0x48, 0x81, 0xEC, 0x68, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x108e3a) (subR64Imm32Effect 0x108e3a 4 0x168)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x108e3a 4 0x168).toInstrSpec (sub_r64_imm32_effect_step 0x108e3a 0x48 0xec 0x168 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x108e41 [0x48, 0x89, 0x8C, 0x24, 0x48, 0x01, 0x00, 0x00] (StorePre 0x108e41 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x108e41 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e41 1 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108e41 1 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (mov_m64_r64_effect_step 0x108e41 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x108e49 [0x48, 0x89, 0xBC, 0x24, 0x40, 0x01, 0x00, 0x00] (StorePre 0x108e49 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x108e49 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e49 7 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108e49 7 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_m64_r64_effect_step 0x108e49 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x108e51 [0x48, 0x8B, 0x06] (LoadPre 0x108e51 (fun s => AddrMode.addr (.base 6 .none) s (0x108e51 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108e51 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108e51 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x108e51 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x108e54 [0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00] (StorePre 0x108e54 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x108e54 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e54 0 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108e54 0 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_m64_r64_effect_step 0x108e54 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x108e5c [0x48, 0x8B, 0x46, 0x08] (LoadPre 0x108e5c (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x108e5c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108e5c 0 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108e5c 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x108e5c 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x108e60 [0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00] (StorePre 0x108e60 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x108e60 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e60 0 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108e60 0 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_m64_r64_effect_step 0x108e60 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x108e68 [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x108e68 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x108e68 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108e68 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108e68 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x108e68 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x108e6c [0x48, 0x89, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00] (StorePre 0x108e6c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x108e6c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e6c 0 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108e6c 0 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_m64_r64_effect_step 0x108e6c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x108e74 [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x108e74 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x108e74 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108e74 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108e74 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x108e74 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x108e78 [0x48, 0x89, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00] (StorePre 0x108e78 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x108e78 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e78 0 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108e78 0 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_m64_r64_effect_step 0x108e78 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x108e80 [0x48, 0x8B, 0x42, 0x18] (LoadPre 0x108e80 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x108e80 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108e80 0 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108e80 0 (.base 2 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x108e80 0x48 (by decide) 0 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x108e84 [0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x108e84 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x108e84 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e84 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108e84 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x108e84 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x108e8c [0x48, 0x8B, 0x42, 0x10] (LoadPre 0x108e8c (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x108e8c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108e8c 0 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108e8c 0 (.base 2 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x108e8c 0x48 (by decide) 0 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e31) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e33) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e35) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e37) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e39) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e3a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e41) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e49) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e51) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e54) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e5c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e60) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e68) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e6c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e74) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e78) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e80) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e84) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e8c) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 84), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e90) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l108e30_1 code

theorem block_l108e30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108e30 :=
  Rest.liftedBlock (rest_l108e30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108e30 x hx)

theorem rest_l108f80 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108f80 bytes_l108f80) (entryMap (live .l108f80))
      4 0x108f80 bytes_l108f80 b_l108f80 := by
  have f0 : InstrSpec 0x108f80 [0x41, 0xBC, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108f80) (movR32Imm32Effect 0x108f80 6 12 0x1)
      [] [] [.reg 12, .rip] :=
    (movR32Imm32Effect_footprint 0x108f80 6 12 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x108f80 0x41 0xbc (by decide) (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x108f86 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x108f86 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108f86 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f86 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x108f86 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x108f86 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x108f8f [0x31, 0xDB] (fun s => s.RIP = 0x108f8f) (xorR32R32Effect 0x108f8f 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x108f8f 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x108f8f 0xdb (by decide)) pre_rip
  have f3 : InstrSpec 0x108f91 [0x41, 0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108f91) (movR32Imm32Effect 0x108f91 6 15 0x1)
      [] [] [.reg 15, .rip] :=
    (movR32Imm32Effect_footprint 0x108f91 6 15 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x108f91 0x41 0xbf (by decide) (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f86) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f8f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(3, 56), (4, 4), (5, 5), (12, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f91) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(3, 56), (4, 4), (5, 5), (12, 53), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f97) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l108f80 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108f80 :=
  Rest.liftedBlock (rest_l108f80 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108f80 x hx)

theorem rest_l108f97 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108f97 bytes_l108f97) (entryMap (live .l108f97))
      17 0x108f97 bytes_l108f97 b_l108f97 := by
  have f0 : InstrSpec 0x108f97 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x108f97) (movR64R64Effect 0x108f97 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x108f97 0 15).toInstrSpec (mov_r64_r64_effect_step 0x108f97 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x108f9a [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x108f9a) (shrR64Effect 0x108f9a 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x108f9a 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x108f9a 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x108f9e [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x108f9e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x108f9e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108f9e 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108f9e 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x108f9e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x108fa3 [0x88, 0x44, 0x24, 0x07] (StorePre 0x108fa3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x108fa3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108fa3 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108fa3 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x108fa3 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x108fa7 [0x4C, 0x8D, 0x6C, 0x24, 0x07] (fun s => s.RIP = 0x108fa7) (leaR64Effect 0x108fa7 13 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x108fa7 13 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x108fa7 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x108fac [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x108fac) (movR64R64Effect 0x108fac 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x108fac 0 3).toInstrSpec (mov_r64_r64_effect_step 0x108fac 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x108faf [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x108faf) (shrR64Effect 0x108faf 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x108faf 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x108faf 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x108fb3 [0x48, 0x89, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00] (StorePre 0x108fb3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x108fb3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108fb3 0 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108fb3 0 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (mov_m64_r64_effect_step 0x108fb3 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x108fbb [0x88, 0x44, 0x24, 0x07] (StorePre 0x108fbb 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x108fbb + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108fbb 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108fbb 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x108fbb 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x108fbf [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x108fbf) (movR64R64Effect 0x108fbf 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x108fbf 7 14).toInstrSpec (mov_r64_r64_effect_step 0x108fbf 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x108fc2 [0x48, 0x8D, 0x74, 0x24, 0x78] (fun s => s.RIP = 0x108fc2) (leaR64Effect 0x108fc2 6 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x108fc2 6 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x108fc2 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x108fc7 [0x48, 0x8D, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108fc7) (leaR64Effect 0x108fc7 2 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x108fc7 2 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (lea_r64_effect_step 0x108fc7 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x108fcf [0x4C, 0x89, 0xF9] (fun s => s.RIP = 0x108fcf) (movR64R64Effect 0x108fcf 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x108fcf 1 15).toInstrSpec (mov_r64_r64_effect_step 0x108fcf 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x108fd2 [0x49, 0x89, 0xD8] (fun s => s.RIP = 0x108fd2) (movR64R64Effect 0x108fd2 8 3)
      [.gpr 3] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x108fd2 8 3).toInstrSpec (mov_r64_r64_effect_step 0x108fd2 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x108fd5 [0x44, 0x8B, 0x74, 0x24, 0x74] (LoadPre 0x108fd5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x108fd5 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x108fd5 14 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR32M32Effect_footprint 0x108fd5 14 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (mov_r32_m32_effect_step 0x108fd5 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x108fda [0x45, 0x89, 0xF1] (fun s => s.RIP = 0x108fda) (movR32R32Effect 0x108fda 3 9 14)
      [.gpr 14] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x108fda 3 9 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x108fda 0x45 0xf1 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x108fdd [0xE8, 0xAE, 0xF8, 0xFF, 0xFF] (PushPre 0x108fdd 5) (callEffect (fun _ => 0x108890) 0x108fe2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x108fdd 0x108890 0x108fe2).toInstrSpec (call_rel32_effect_step 0x108fdd 0xfffff8ae (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f9a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108f9e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fa3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fa7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fac) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108faf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fb3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fbb) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fbf) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (7, 67), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fc2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (6, 69), (7, 67), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fc7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 63), (2, 71), (3, 3), (4, 4), (5, 5), (6, 69), (7, 67), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fcf) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 63), (1, 73), (2, 71), (3, 3), (4, 4), (5, 5), (6, 69), (7, 67), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fd2) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 63), (1, 73), (2, 71), (3, 3), (4, 4), (5, 5), (6, 69), (7, 67), (8, 75), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fd5) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 63), (1, 73), (2, 71), (3, 3), (4, 4), (5, 5), (6, 69), (7, 67), (8, 75), (12, 12), (13, 59), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fda) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 63), (1, 73), (2, 71), (3, 3), (4, 4), (5, 5), (6, 69), (7, 67), (8, 75), (9, 79), (12, 12), (13, 59), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fdd) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 63), (1, 73), (2, 71), (3, 3), (4, 81), (5, 5), (6, 69), (7, 67), (8, 75), (9, 79), (12, 12), (13, 59), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108890) f16 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 83) (by decide) (by decide) rfl rfl

theorem block_l108f97 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108f97 :=
  Rest.liftedBlock (rest_l108f97 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108f97 x hx)

theorem rest_l108fe2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108fe2 bytes_l108fe2) (entryMap (live .l108fe2))
      19 0x108fe2 bytes_l108fe2 b_l108fe2 := by
  have f0 : InstrSpec 0x108fe2 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x108fe2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108fe2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108fe2 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108fe2 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x108fe2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x108fe7 [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x108fe7) (movR64R64Effect 0x108fe7 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x108fe7 2 0).toInstrSpec (mov_r64_r64_effect_step 0x108fe7 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x108fea [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x108fea) (movR64R64Effect 0x108fea 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x108fea 1 0).toInstrSpec (mov_r64_r64_effect_step 0x108fea 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x108fed [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x108fed 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108fed + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108fed 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108fed 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x108fed 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x108ff2 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x108ff2) (shrR64Effect 0x108ff2 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x108ff2 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x108ff2 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x108ff6 [0x48, 0x89, 0x94, 0x24, 0x58, 0x01, 0x00, 0x00] (StorePre 0x108ff6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x108ff6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108ff6 2 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108ff6 2 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (mov_m64_r64_effect_step 0x108ff6 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x108ffe [0x88, 0x54, 0x24, 0x07] (StorePre 0x108ffe 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x108ffe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108ffe 4 2 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108ffe 4 2 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x108ffe 2 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x109002 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x109002) (movR64R64Effect 0x109002 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109002 0 13).toInstrSpec (mov_r64_r64_effect_step 0x109002 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x109005 [0x4D, 0x89, 0xE5] (fun s => s.RIP = 0x109005) (movR64R64Effect 0x109005 13 12)
      [.gpr 12] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x109005 13 12).toInstrSpec (mov_r64_r64_effect_step 0x109005 0x4d 0xe5 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x109008 [0x4D, 0x89, 0xE0] (fun s => s.RIP = 0x109008) (movR64R64Effect 0x109008 8 12)
      [.gpr 12] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x109008 8 12).toInstrSpec (mov_r64_r64_effect_step 0x109008 0x4d 0xe0 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10900b [0x4C, 0x89, 0x64, 0x24, 0x68] (StorePre 0x10900b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10900b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10900b 12 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10900b 12 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x10900b 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x109010 [0x49, 0xC1, 0xED, 0x3F] (fun s => s.RIP = 0x109010) (shrR64Effect 0x109010 4 13 63)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR64Effect_footprint 0x109010 4 13 63).toInstrSpec (shr_r64_imm8_effect_step 0x109010 0x49 0xed 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x109014 [0x44, 0x88, 0x6C, 0x24, 0x07] (StorePre 0x109014 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109014 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x109014 5 13 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109014 5 13 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_rex_effect_step 0x109014 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x109019 [0x4C, 0x8D, 0x64, 0x24, 0x38] (fun s => s.RIP = 0x109019) (leaR64Effect 0x109019 12 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x109019 12 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x109019 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10901e [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x10901e) (movR64R64Effect 0x10901e 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10901e 7 12).toInstrSpec (mov_r64_r64_effect_step 0x10901e 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x109021 [0x48, 0x8D, 0x74, 0x24, 0x78] (fun s => s.RIP = 0x109021) (leaR64Effect 0x109021 6 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x109021 6 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x109021 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x109026 [0x48, 0x8D, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109026) (leaR64Effect 0x109026 2 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x109026 2 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (lea_r64_effect_step 0x109026 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10902e [0x45, 0x89, 0xF1] (fun s => s.RIP = 0x10902e) (movR32R32Effect 0x10902e 3 9 14)
      [.gpr 14] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x10902e 3 9 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x10902e 0x45 0xf1 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x109031 [0xE8, 0x5A, 0xF8, 0xFF, 0xFF] (PushPre 0x109031 5) (callEffect (fun _ => 0x108890) 0x109036)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109031 0x108890 0x109036).toInstrSpec (call_rel32_effect_step 0x109031 0xfffff85a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fe7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fea) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108fed) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ff2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 57), (2, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ff6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 57), (2, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ffe) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 57), (2, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109002) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(1, 57), (2, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109005) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 57), (2, 60), (3, 3), (4, 4), (5, 5), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109008) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 57), (2, 60), (3, 3), (4, 4), (5, 5), (8, 67), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10900b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(1, 57), (2, 60), (3, 3), (4, 4), (5, 5), (8, 67), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109010) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(1, 57), (2, 60), (3, 3), (4, 4), (5, 5), (8, 67), (12, 12), (13, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109014) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(1, 57), (2, 60), (3, 3), (4, 4), (5, 5), (8, 67), (12, 12), (13, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109019) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 57), (2, 60), (3, 3), (4, 4), (5, 5), (8, 67), (12, 73), (13, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10901e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 57), (2, 60), (3, 3), (4, 4), (5, 5), (7, 75), (8, 67), (12, 73), (13, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109021) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 57), (2, 60), (3, 3), (4, 4), (5, 5), (6, 77), (7, 75), (8, 67), (12, 73), (13, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109026) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 57), (2, 79), (3, 3), (4, 4), (5, 5), (6, 77), (7, 75), (8, 67), (12, 73), (13, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10902e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(1, 57), (2, 79), (3, 3), (4, 4), (5, 5), (6, 77), (7, 75), (8, 67), (9, 81), (12, 73), (13, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109031) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(1, 57), (2, 79), (3, 3), (4, 83), (5, 5), (6, 77), (7, 75), (8, 67), (9, 81), (12, 73), (13, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108890) f18 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l108fe2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108fe2 :=
  Rest.liftedBlock (rest_l108fe2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108fe2 x hx)

theorem rest_l109036_1 [Bindings] (code : CodeMap) :
    Rest (n := 83) code lifted (codeRange 0x109036 bytes_l109036) [(0, 80), (1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      17 0x1090b4 bytes_l109036_1 b_l109036_1 := by
  have f20 : InstrSpec 0x1090b4 [0x48, 0x8B, 0x44, 0x24, 0x60] (LoadPre 0x1090b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1090b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090b4 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1090b4 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x1090b4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x1090b9 [0x88, 0x44, 0x24, 0x07] (StorePre 0x1090b9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1090b9 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1090b9 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1090b9 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x1090b9 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x1090bd [0x48, 0x8D, 0x44, 0x24, 0x07] (fun s => s.RIP = 0x1090bd) (leaR64Effect 0x1090bd 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1090bd 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x1090bd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x1090c2 [0x48, 0x8B, 0x8C, 0x24, 0x50, 0x01, 0x00, 0x00] (LoadPre 0x1090c2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1090c2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1090c2 1 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1090c2 1 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (mov_r64_m64_effect_step 0x1090c2 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x1090ca [0x88, 0x4C, 0x24, 0x07] (StorePre 0x1090ca 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1090ca + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1090ca 4 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1090ca 4 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x1090ca 1 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x1090ce [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x1090ce) (leaR64Effect 0x1090ce 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1090ce 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1090ce 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x1090d3 [0x48, 0x8D, 0xB4, 0x24, 0xD0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1090d3) (leaR64Effect 0x1090d3 6 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1090d3 6 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (lea_r64_effect_step 0x1090d3 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x1090db [0x48, 0x8D, 0x94, 0x24, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1090db) (leaR64Effect 0x1090db 2 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1090db 2 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (lea_r64_effect_step 0x1090db 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x1090e3 [0x4C, 0x89, 0xF9] (fun s => s.RIP = 0x1090e3) (movR64R64Effect 0x1090e3 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1090e3 1 15).toInstrSpec (mov_r64_r64_effect_step 0x1090e3 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x1090e6 [0x49, 0x89, 0xD8] (fun s => s.RIP = 0x1090e6) (movR64R64Effect 0x1090e6 8 3)
      [.gpr 3] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1090e6 8 3).toInstrSpec (mov_r64_r64_effect_step 0x1090e6 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x1090e9 [0x45, 0x89, 0xF7] (fun s => s.RIP = 0x1090e9) (movR32R32Effect 0x1090e9 3 15 14)
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x1090e9 3 15 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x1090e9 0x45 0xf7 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x1090ec [0x45, 0x89, 0xF1] (fun s => s.RIP = 0x1090ec) (movR32R32Effect 0x1090ec 3 9 14)
      [.gpr 14] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x1090ec 3 9 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x1090ec 0x45 0xf1 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x1090ef [0x4C, 0x8B, 0xB4, 0x24, 0x48, 0x01, 0x00, 0x00] (LoadPre 0x1090ef (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x1090ef + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1090ef 14 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1090ef 14 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (mov_r64_m64_effect_step 0x1090ef 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x1090f7 [0x41, 0x56] (PushPre 0x1090f7 2) (pushR64Effect 0x1090f7 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1090f7 2 14).toInstrSpec (push_r64_rex_effect_step 0x1090f7 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f34 : InstrSpec 0x1090f9 [0x48, 0x8B, 0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x1090f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1090f9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1090f9 3 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1090f9 3 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x1090f9 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x109101 [0x53] (PushPre 0x109101 1) (pushR64Effect 0x109101 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109101 1 3).toInstrSpec (push_r64_effect_step 0x109101 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f36 : InstrSpec 0x109102 [0xE8, 0x79, 0xF8, 0xFF, 0xFF] (PushPre 0x109102 5) (callEffect (fun _ => 0x108980) 0x109107)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109102 0x108980 0x109107).toInstrSpec (call_rel32_effect_step 0x109102 0xfffff879 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090b9) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 83), (1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090bd) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090c2) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(1, 87), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090ca) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(1, 87), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090ce) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f25 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(1, 87), (3, 3), (4, 4), (5, 5), (7, 90), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090d3) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f26 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(1, 87), (3, 3), (4, 4), (5, 5), (6, 92), (7, 90), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090db) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(1, 87), (2, 94), (3, 3), (4, 4), (5, 5), (6, 92), (7, 90), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090e3) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(1, 96), (2, 94), (3, 3), (4, 4), (5, 5), (6, 92), (7, 90), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090e6) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f29 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(1, 96), (2, 94), (3, 3), (4, 4), (5, 5), (6, 92), (7, 90), (8, 98), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090e9) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f30 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(1, 96), (2, 94), (3, 3), (4, 4), (5, 5), (6, 92), (7, 90), (8, 98), (12, 12), (13, 13), (14, 14), (15, 100), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090ec) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f31 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(1, 96), (2, 94), (3, 3), (4, 4), (5, 5), (6, 92), (7, 90), (8, 98), (9, 102), (12, 12), (13, 13), (14, 14), (15, 100), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090ef) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f32 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(1, 96), (2, 94), (3, 3), (4, 4), (5, 5), (6, 92), (7, 90), (8, 98), (9, 102), (12, 12), (13, 13), (14, 104), (15, 100), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090f7) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f33 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(1, 96), (2, 94), (3, 3), (4, 106), (5, 5), (6, 92), (7, 90), (8, 98), (9, 102), (12, 12), (13, 13), (14, 104), (15, 100), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090f9) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f34 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(1, 96), (2, 94), (3, 108), (4, 106), (5, 5), (6, 92), (7, 90), (8, 98), (9, 102), (12, 12), (13, 13), (14, 104), (15, 100), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109101) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f35 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(1, 96), (2, 94), (3, 108), (4, 110), (5, 5), (6, 92), (7, 90), (8, 98), (9, 102), (12, 12), (13, 13), (14, 104), (15, 100), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109102) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f36 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(1, 96), (2, 94), (3, 108), (4, 112), (5, 5), (6, 92), (7, 90), (8, 98), (9, 102), (12, 12), (13, 13), (14, 104), (15, 100), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108980) f36 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 114) (by decide) (by decide) rfl rfl

theorem rest_l109036 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109036 bytes_l109036) (entryMap (live .l109036))
      37 0x109036 bytes_l109036 b_l109036 := by
  have f0 : InstrSpec 0x109036 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x109036 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109036 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109036 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109036 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x109036 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10903b [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x10903b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10903b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10903b 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10903b 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x10903b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x109043 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x109043 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109043 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109043 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109043 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x109043 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109048 [0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x109048 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x109048 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109048 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109048 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x109048 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x109050 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x109050 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109050 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109050 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109050 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x109050 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x109055 [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x109055 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x109055 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109055 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109055 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x109055 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10905d [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x10905d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10905d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10905d 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10905d 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10905d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x109062 [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x109062 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109062 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109062 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109062 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x109062 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x109067 [0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x109067 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109067 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109067 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109067 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x109067 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10906f [0x48, 0x89, 0x44, 0x24, 0x78] (StorePre 0x10906f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10906f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10906f 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10906f 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x10906f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x109074 [0x49, 0x8B, 0x04, 0x24] (LoadPre 0x109074 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x109074 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109074 0 (.sib 12 none 0 .none))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109074 0 (.sib 12 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x109074 0x49 (by decide) 0 (.sib 12 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x109078 [0x49, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x109078 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x109078 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109078 1 (.sib 12 none 0 (.d8 0x8)))
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109078 1 (.sib 12 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109078 0x49 (by decide) 1 (.sib 12 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x10907d [0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x10907d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10907d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10907d 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10907d 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x10907d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x109085 [0x48, 0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x109085 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x109085 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109085 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109085 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x109085 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x10908d [0x49, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x10908d (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x10908d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10908d 0 (.sib 12 none 0 (.d8 0x10)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10908d 0 (.sib 12 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10908d 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x109092 [0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x109092 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x109092 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109092 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109092 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x109092 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10909a [0x49, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x10909a (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x10909a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10909a 0 (.sib 12 none 0 (.d8 0x18)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10909a 0 (.sib 12 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10909a 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10909f [0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x10909f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10909f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10909f 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10909f 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x10909f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1090a7 [0x49, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x1090a7 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x20)) s (0x1090a7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090a7 0 (.sib 12 none 0 (.d8 0x20)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1090a7 0 (.sib 12 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1090a7 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x1090ac [0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x1090ac 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1090ac + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1090ac 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1090ac 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x1090ac 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10903b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109043) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109048) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109050) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109055) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10905d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109062) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109067) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10906f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109074) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109078) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 68), (1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10907d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 68), (1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109085) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 68), (1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10908d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109092) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10909a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10909f) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090a7) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090ac) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 70), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1090b4) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l109036_1 code

theorem block_l109036 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109036 :=
  Rest.liftedBlock (rest_l109036 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109036 x hx)

theorem rest_l109107 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109107 bytes_l109107) (entryMap (live .l109107))
      15 0x109107 bytes_l109107 b_l109107 := by
  have f0 : InstrSpec 0x109107 [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x109107) (addR64Imm8Effect 0x109107 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x109107 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x109107 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10910b [0x48, 0x8B, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00] (LoadPre 0x10910b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10910b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10910b 0 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10910b 0 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (mov_r64_m64_effect_step 0x10910b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x109113 [0x88, 0x44, 0x24, 0x07] (StorePre 0x109113 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109113 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109113 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109113 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x109113 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x109117 [0x48, 0x8D, 0x44, 0x24, 0x07] (fun s => s.RIP = 0x109117) (leaR64Effect 0x109117 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x109117 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x109117 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10911c [0x44, 0x88, 0x6C, 0x24, 0x07] (StorePre 0x10911c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10911c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10911c 5 13 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10911c 5 13 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10911c 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x109121 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x109121) (movR64R64Effect 0x109121 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x109121 7 12).toInstrSpec (mov_r64_r64_effect_step 0x109121 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x109124 [0x48, 0x8D, 0xB4, 0x24, 0xD0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109124) (leaR64Effect 0x109124 6 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x109124 6 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (lea_r64_effect_step 0x109124 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10912c [0x48, 0x8D, 0x94, 0x24, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10912c) (leaR64Effect 0x10912c 2 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x10912c 2 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (lea_r64_effect_step 0x10912c 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x109134 [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x109134 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109134 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109134 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109134 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109134 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x109139 [0x4C, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x109139 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x109139 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109139 8 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x109139 8 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x109139 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x10913e [0x45, 0x89, 0xF9] (fun s => s.RIP = 0x10913e) (movR32R32Effect 0x10913e 3 9 15)
      [.gpr 15] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x10913e 3 9 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x10913e 0x45 0xf9 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x109141 [0x41, 0x56] (PushPre 0x109141 2) (pushR64Effect 0x109141 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109141 2 14).toInstrSpec (push_r64_rex_effect_step 0x109141 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x109143 [0x4C, 0x8D, 0x74, 0x24, 0x18] (fun s => s.RIP = 0x109143) (leaR64Effect 0x109143 14 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x109143 14 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (lea_r64_effect_step 0x109143 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x109148 [0x53] (PushPre 0x109148 1) (pushR64Effect 0x109148 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109148 1 3).toInstrSpec (push_r64_effect_step 0x109148 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f14 : InstrSpec 0x109149 [0xE8, 0x32, 0xF8, 0xFF, 0xFF] (PushPre 0x109149 5) (callEffect (fun _ => 0x108980) 0x10914e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109149 0x108980 0x10914e).toInstrSpec (call_rel32_effect_step 0x109149 0xfffff832 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10910b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109113) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109117) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10911c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109121) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 53), (5, 5), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109124) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10912c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 64), (3, 3), (4, 53), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109134) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 53), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109139) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 53), (5, 5), (6, 62), (7, 60), (8, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10913e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 53), (5, 5), (6, 62), (7, 60), (8, 68), (9, 70), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109141) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 72), (5, 5), (6, 62), (7, 60), (8, 68), (9, 70), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109143) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 72), (5, 5), (6, 62), (7, 60), (8, 68), (9, 70), (12, 12), (13, 13), (14, 74), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109148) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 76), (5, 5), (6, 62), (7, 60), (8, 68), (9, 70), (12, 12), (13, 13), (14, 74), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109149) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(1, 66), (2, 64), (3, 3), (4, 78), (5, 5), (6, 62), (7, 60), (8, 68), (9, 70), (12, 12), (13, 13), (14, 74), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108980) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 80) (by decide) (by decide) rfl rfl

theorem block_l109107 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109107 :=
  Rest.liftedBlock (rest_l109107 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109107 x hx)

theorem rest_l10914e_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x10914e bytes_l10914e) [(0, 82), (1, 72), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x1091cb bytes_l10914e_1 b_l10914e_1 := by
  have f20 : InstrSpec 0x1091cb [0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x1091cb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1091cb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091cb 0 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1091cb 0 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m64_r64_effect_step 0x1091cb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x1091d3 [0x48, 0x8B, 0x94, 0x24, 0x60, 0x01, 0x00, 0x00] (LoadPre 0x1091d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x1091d3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1091d3 2 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1091d3 2 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (mov_r64_m64_effect_step 0x1091d3 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x1091db [0x44, 0x29, 0xFA] (fun s => s.RIP = 0x1091db) (subR32R32Effect 0x1091db 3 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (subR32R32Effect_footprint 0x1091db 3 2 15).toInstrSpec (sub_r32_r32_rex_effect_step 0x1091db 0x44 0xfa (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 82), (1, 72), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091d3) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f21 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 82), (1, 72), (2, 85), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091db) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 88) f22 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 89) (ρ' := [(0, 82), (1, 72), (2, 87), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091de) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 90) (jcc_rel32_effect_step 0x1091de 4 0x21a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l10914e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10914e bytes_l10914e) (entryMap (live .l10914e))
      24 0x10914e bytes_l10914e b_l10914e := by
  have f0 : InstrSpec 0x10914e [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x10914e) (addR64Imm8Effect 0x10914e 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10914e 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x10914e 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x109152 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x109152 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109152 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109152 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109152 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x109152 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x109157 [0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] (StorePre 0x109157 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x109157 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109157 0 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109157 0 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x109157 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10915f [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x10915f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10915f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10915f 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10915f 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10915f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x109164 [0x48, 0x89, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00] (StorePre 0x109164 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x109164 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109164 0 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109164 0 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x109164 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10916c [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x10916c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10916c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10916c 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10916c 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10916c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x109171 [0x48, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x109171 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x109171 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109171 0 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109171 0 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x109171 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x109179 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x109179 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109179 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109179 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109179 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x109179 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10917e [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x10917e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10917e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10917e 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10917e 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10917e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x109183 [0x48, 0x89, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x109183 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x109183 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109183 1 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109183 1 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x109183 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10918b [0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x10918b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10918b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10918b 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10918b 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x10918b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x109193 [0x49, 0x8B, 0x04, 0x24] (LoadPre 0x109193 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x109193 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109193 0 (.sib 12 none 0 .none))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109193 0 (.sib 12 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x109193 0x49 (by decide) 0 (.sib 12 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x109197 [0x49, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x109197 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x109197 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109197 1 (.sib 12 none 0 (.d8 0x8)))
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109197 1 (.sib 12 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109197 0x49 (by decide) 1 (.sib 12 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10919c [0x48, 0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x10919c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10919c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10919c 0 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10919c 0 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x10919c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1091a4 [0x48, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x1091a4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1091a4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091a4 1 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1091a4 1 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m64_r64_effect_step 0x1091a4 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1091ac [0x49, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1091ac (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x1091ac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1091ac 0 (.sib 12 none 0 (.d8 0x10)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1091ac 0 (.sib 12 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1091ac 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1091b1 [0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x1091b1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1091b1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091b1 0 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1091b1 0 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m64_r64_effect_step 0x1091b1 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1091b9 [0x49, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x1091b9 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x1091b9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1091b9 0 (.sib 12 none 0 (.d8 0x18)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1091b9 0 (.sib 12 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1091b9 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x1091be [0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x1091be 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1091be + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091be 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1091be 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m64_r64_effect_step 0x1091be 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1091c6 [0x49, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x1091c6 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x20)) s (0x1091c6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1091c6 0 (.sib 12 none 0 (.d8 0x20)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1091c6 0 (.sib 12 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1091c6 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109152) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109157) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10915f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109164) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10916c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109171) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109179) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10917e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109183) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10918b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109193) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (1, 66), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109197) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 70), (1, 72), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10919c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 70), (1, 72), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091a4) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 70), (1, 72), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091ac) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 72), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091b1) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 76), (1, 72), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091b9) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 72), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091be) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 72), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091c6) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 72), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091cb) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10914e_1 code

theorem block_l10914e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10914e :=
  Rest.liftedBlock (rest_l10914e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10914e x hx)

theorem rest_l1091e4_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x1091e4 bytes_l1091e4) [(0, 83), (1, 87), (2, 78), (3, 3), (4, 4), (5, 5), (6, 85), (9, 75), (14, 14), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x10923b bytes_l1091e4_1 b_l1091e4_1 := by
  have f20 : InstrSpec 0x10923b [0x44, 0x89, 0x4C, 0x24, 0x74] (StorePre 0x10923b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x10923b + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10923b 9 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x10923b 9 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (mov_m32_r32_effect_step 0x10923b 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 83), (1, 87), (2, 78), (3, 3), (4, 4), (5, 5), (6, 85), (9, 75), (14, 14), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109240) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 91) (jcc_rel32_effect_step 0x109240 4 0xfffffd3a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l1091e4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1091e4 bytes_l1091e4) (entryMap (live .l1091e4))
      22 0x1091e4 bytes_l1091e4 b_l1091e4 := by
  have f0 : InstrSpec 0x1091e4 [0x89, 0xD0] (fun s => s.RIP = 0x1091e4) (movR32R32Effect 0x1091e4 2 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1091e4 2 0 2).toInstrSpec (mov_r32_r32_effect_step 0x1091e4 0xd0 (by decide)) pre_rip
  have f1 : InstrSpec 0x1091e6 [0xF7, 0xD0] (fun s => s.RIP = 0x1091e6) (notR32Effect 0x1091e6 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR32Effect_footprint 0x1091e6 2 0).toInstrSpec (not_r32_effect_step 0x1091e6 0xd0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1091e8 [0x8D, 0x4A, 0xC2] (fun s => s.RIP = 0x1091e8) (leaR32Effect 0x1091e8 3 1 (.base 2 (.d8 0xc2)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x1091e8 3 1 (.base 2 (.d8 0xc2))).toInstrSpec (lea_r32_effect_step 0x1091e8 1 (.base 2 (.d8 0xc2)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1091eb [0x21, 0xC1] (fun s => s.RIP = 0x1091eb) (andR32R32Effect 0x1091eb 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR32R32Effect_footprint 0x1091eb 2 1 0).toInstrSpec (and_r32_r32_effect_step 0x1091eb 0xc1 (by decide)) pre_rip
  have f4 : InstrSpec 0x1091ed [0xC1, 0xE9, 0x1F] (fun s => s.RIP = 0x1091ed) (shrR32Effect 0x1091ed 3 1 31)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1091ed 3 1 31).toInstrSpec (shr_r32_imm8_effect_step 0x1091ed 0xe9 0x1f (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1091f0 [0x88, 0x4C, 0x24, 0x10] (StorePre 0x1091f0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1091f0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1091f0 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1091f0 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x1091f0 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1091f4 [0x0F, 0xB6, 0x44, 0x24, 0x10] (LoadPre 0x1091f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1091f4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1091f4 5 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1091f4 5 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x1091f4 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1091f9 [0xF7, 0xD8] (fun s => s.RIP = 0x1091f9) (negR32Effect 0x1091f9 2 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR32Effect_footprint 0x1091f9 2 0).toInstrSpec (neg_r32_effect_step 0x1091f9 0xd8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1091fb [0x48, 0x89, 0x94, 0x24, 0x60, 0x01, 0x00, 0x00] (StorePre 0x1091fb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x1091fb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091fb 2 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1091fb 2 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (mov_m64_r64_effect_step 0x1091fb 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x109203 [0x41, 0x89, 0xD1] (fun s => s.RIP = 0x109203) (movR32R32Effect 0x109203 3 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x109203 3 9 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x109203 0x41 0xd1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x109206 [0x41, 0x83, 0xF1, 0x3E] (fun s => s.RIP = 0x109206) (xorR32Imm8Effect 0x109206 4 9 0x3e)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x109206 4 9 0x3e).toInstrSpec (xor_r32_imm8_rex_effect_step 0x109206 0x41 0xf1 0x3e (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10920a [0x41, 0x21, 0xC1] (fun s => s.RIP = 0x10920a) (andR32R32Effect 0x10920a 3 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (andR32R32Effect_footprint 0x10920a 3 9 0).toInstrSpec (and_r32_r32_rex_effect_step 0x10920a 0x41 0xc1 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10920d [0x41, 0x83, 0xF1, 0x3E] (fun s => s.RIP = 0x10920d) (xorR32Imm8Effect 0x10920d 4 9 0x3e)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x10920d 4 9 0x3e).toInstrSpec (xor_r32_imm8_rex_effect_step 0x10920d 0x41 0xf1 0x3e (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x109211 [0x48, 0x8B, 0x54, 0x24, 0x78] (LoadPre 0x109211 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109211 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109211 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x109211 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x109211 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x109216 [0x0F, 0xB6, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x109216 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x109216 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x109216 8 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109216 8 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (movzx_r32_m8_effect_step 0x109216 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10921e [0x88, 0x44, 0x24, 0x10] (StorePre 0x10921e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10921e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10921e 4 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10921e 4 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x10921e 0 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x109222 [0x0F, 0xB6, 0x44, 0x24, 0x10] (LoadPre 0x109222 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109222 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109222 5 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109222 5 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x109222 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x109227 [0x48, 0x8B, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x109227 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x109227 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109227 6 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x109227 6 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x109227 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x10922f [0x0F, 0xB6, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x10922f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10922f + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10922f 8 1 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10922f 8 1 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (movzx_r32_m8_effect_step 0x10922f 1 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x109237 [0x88, 0x4C, 0x24, 0x10] (StorePre 0x109237 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109237 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109237 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109237 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x109237 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091e6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091e8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091eb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091ed) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091f0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091f4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091f9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1091fb) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109203) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 66), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (9, 69), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109206) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 66), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (9, 71), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10920a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 66), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (9, 73), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10920d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f12 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 77) (ρ' := [(0, 66), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (9, 75), (14, 14), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109211) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 66), (1, 61), (2, 78), (3, 3), (4, 4), (5, 5), (9, 75), (14, 14), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109216) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 61), (2, 78), (3, 3), (4, 4), (5, 5), (9, 75), (14, 14), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10921e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 61), (2, 78), (3, 3), (4, 4), (5, 5), (9, 75), (14, 14), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109222) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 61), (2, 78), (3, 3), (4, 4), (5, 5), (9, 75), (14, 14), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109227) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 83), (1, 61), (2, 78), (3, 3), (4, 4), (5, 5), (6, 85), (9, 75), (14, 14), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10922f) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 83), (1, 87), (2, 78), (3, 3), (4, 4), (5, 5), (6, 85), (9, 75), (14, 14), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109237) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 83), (1, 87), (2, 78), (3, 3), (4, 4), (5, 5), (6, 85), (9, 75), (14, 14), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10923b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1091e4_1 code

theorem block_l1091e4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1091e4 :=
  Rest.liftedBlock (rest_l1091e4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1091e4 x hx)

theorem rest_l109246_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x109246 bytes_l109246) [(0, 83), (1, 69), (2, 71), (4, 4), (5, 5), (6, 87), (7, 85), (8, 55), (9, 9), (12, 90), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x109295 bytes_l109246_1 b_l109246_1 := by
  have f20 : InstrSpec 0x109295 [0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109295) (fun _ => nopEffect 0x109295 11)
      [] [] [.rip] :=
    (nopEffect_footprint 0x109295 11).toInstrSpec (nop_m_effect_step 0x109295 [0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 83), (1, 69), (2, 71), (4, 4), (5, 5), (6, 87), (7, 85), (8, 55), (9, 9), (12, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092a0) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 93) (by decide) rfl

theorem rest_l109246 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109246 bytes_l109246) (entryMap (live .l109246))
      21 0x109246 bytes_l109246 b_l109246 := by
  have f0 : InstrSpec 0x109246 [0x0F, 0xB6, 0x4C, 0x24, 0x10] (LoadPre 0x109246 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109246 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109246 5 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109246 5 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x109246 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10924b [0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x10924b) (movR64Imm64Effect 0x10924b 8 0x7fffffffffffffff)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x10924b 8 0x7fffffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10924b 0x49 0xb8 (by decide) (by decide) 0x7fffffffffffffff) pre_rip
  have f2 : InstrSpec 0x109255 [0x4C, 0x21, 0xC6] (fun s => s.RIP = 0x109255) (andR64R64Effect 0x109255 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109255 6 8).toInstrSpec (and_r64_r64_effect_step 0x109255 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x109258 [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x109258) (movR64R64Effect 0x109258 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x109258 7 6).toInstrSpec (mov_r64_r64_effect_step 0x109258 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10925b [0x48, 0xF7, 0xDF] (fun s => s.RIP = 0x10925b) (negR64Effect 0x10925b 7)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (negR64Effect_footprint 0x10925b 7).toInstrSpec (neg_r64_effect_step 0x10925b 0x48 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10925e [0x48, 0x31, 0xF7] (fun s => s.RIP = 0x10925e) (xorR64R64Effect 0x10925e 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10925e 7 6).toInstrSpec (xor_r64_r64_effect_step 0x10925e 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x109261 [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x109261) (negR64Effect 0x109261 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x109261 1).toInstrSpec (neg_r64_effect_step 0x109261 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x109264 [0x48, 0x21, 0xF9] (fun s => s.RIP = 0x109264) (andR64R64Effect 0x109264 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109264 1 7).toInstrSpec (and_r64_r64_effect_step 0x109264 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x109267 [0x48, 0x31, 0xF1] (fun s => s.RIP = 0x109267) (xorR64R64Effect 0x109267 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109267 1 6).toInstrSpec (xor_r64_r64_effect_step 0x109267 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10926a [0x4C, 0x21, 0xC2] (fun s => s.RIP = 0x10926a) (andR64R64Effect 0x10926a 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10926a 2 8).toInstrSpec (and_r64_r64_effect_step 0x10926a 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10926d [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x10926d) (movR64R64Effect 0x10926d 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10926d 6 2).toInstrSpec (mov_r64_r64_effect_step 0x10926d 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x109270 [0x48, 0xF7, 0xDE] (fun s => s.RIP = 0x109270) (negR64Effect 0x109270 6)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (negR64Effect_footprint 0x109270 6).toInstrSpec (neg_r64_effect_step 0x109270 0x48 0xde (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x109273 [0x48, 0x31, 0xD6] (fun s => s.RIP = 0x109273) (xorR64R64Effect 0x109273 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109273 6 2).toInstrSpec (xor_r64_r64_effect_step 0x109273 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x109276 [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x109276) (negR64Effect 0x109276 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x109276 0).toInstrSpec (neg_r64_effect_step 0x109276 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x109279 [0x48, 0x21, 0xF0] (fun s => s.RIP = 0x109279) (andR64R64Effect 0x109279 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109279 0 6).toInstrSpec (and_r64_r64_effect_step 0x109279 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10927c [0x48, 0x31, 0xD0] (fun s => s.RIP = 0x10927c) (xorR64R64Effect 0x10927c 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10927c 0 2).toInstrSpec (xor_r64_r64_effect_step 0x10927c 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10927f [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10927f) (movR32Imm32Effect 0x10927f 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x10927f 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10927f 0xbf (by decide) 0x1) pre_rip
  have f17 : InstrSpec 0x109284 [0x31, 0xF6] (fun s => s.RIP = 0x109284) (xorR32R32Effect 0x109284 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109284 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x109284 0xf6 (by decide)) pre_rip
  have f18 : InstrSpec 0x109286 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x109286 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109286 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109286 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x109286 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x109286 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x10928f [0x41, 0xBC, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10928f) (movR32Imm32Effect 0x10928f 6 12 0x1)
      [] [] [.reg 12, .rip] :=
    (movR32Imm32Effect_footprint 0x10928f 6 12 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x10928f 0x41 0xbc (by decide) (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10924b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109255) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 57), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109258) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 57), (7, 59), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10925b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 57), (7, 61), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10925e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 57), (7, 63), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109261) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 2), (4, 4), (5, 5), (6, 57), (7, 63), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109264) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 2), (4, 4), (5, 5), (6, 57), (7, 63), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109267) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (2, 2), (4, 4), (5, 5), (6, 57), (7, 63), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10926a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 69), (2, 71), (4, 4), (5, 5), (6, 57), (7, 63), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10926d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 69), (2, 71), (4, 4), (5, 5), (6, 73), (7, 63), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109270) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 69), (2, 71), (4, 4), (5, 5), (6, 75), (7, 63), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109273) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 69), (2, 71), (4, 4), (5, 5), (6, 77), (7, 63), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109276) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 69), (2, 71), (4, 4), (5, 5), (6, 77), (7, 63), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109279) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 69), (2, 71), (4, 4), (5, 5), (6, 77), (7, 63), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10927c) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 69), (2, 71), (4, 4), (5, 5), (6, 77), (7, 63), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10927f) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 83), (1, 69), (2, 71), (4, 4), (5, 5), (6, 77), (7, 85), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109284) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 83), (1, 69), (2, 71), (4, 4), (5, 5), (6, 87), (7, 85), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109286) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 83), (1, 69), (2, 71), (4, 4), (5, 5), (6, 87), (7, 85), (8, 55), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10928f) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 83), (1, 69), (2, 71), (4, 4), (5, 5), (6, 87), (7, 85), (8, 55), (9, 9), (12, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109295) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109246_1 code

theorem block_l109246 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109246 :=
  Rest.liftedBlock (rest_l109246 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109246 x hx)

theorem rest_l1092a0_4 [Bindings] (code : CodeMap) :
    Rest (n := 204) code lifted (codeRange 0x1092a0 bytes_l1092a0) [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 6), (7, 188), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 200), (22, 22), (39, 39), (50, 50), (51, 51)]
      11 0x1093cf bytes_l1092a0_4 b_l1092a0_4 := by
  have f80 : InstrSpec 0x1093cf [0x44, 0x88, 0x44, 0x24, 0x10] (StorePre 0x1093cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1093cf + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1093cf 5 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1093cf 5 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1093cf 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f81 : InstrSpec 0x1093d4 [0x4D, 0x89, 0xCE] (fun s => s.RIP = 0x1093d4) (movR64R64Effect 0x1093d4 14 9)
      [.gpr 9] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1093d4 14 9).toInstrSpec (mov_r64_r64_effect_step 0x1093d4 0x4d 0xce (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x1093d7 [0x0F, 0xB6, 0x74, 0x24, 0x10] (LoadPre 0x1093d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1093d7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1093d7 5 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1093d7 5 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x1093d7 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f83 : InstrSpec 0x1093dc [0x48, 0xF7, 0xDE] (fun s => s.RIP = 0x1093dc) (negR64Effect 0x1093dc 6)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (negR64Effect_footprint 0x1093dc 6).toInstrSpec (neg_r64_effect_step 0x1093dc 0x48 0xde (by decide) (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x1093df [0x48, 0x21, 0xD6] (fun s => s.RIP = 0x1093df) (andR64R64Effect 0x1093df 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1093df 6 2).toInstrSpec (and_r64_r64_effect_step 0x1093df 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x1093e2 [0x44, 0x8B, 0x4C, 0x24, 0x60] (LoadPre 0x1093e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1093e2 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1093e2 9 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x1093e2 9 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r32_m32_effect_step 0x1093e2 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f86 : InstrSpec 0x1093e7 [0x49, 0x01, 0xF4] (fun s => s.RIP = 0x1093e7) (addR64R64Effect 0x1093e7 12 6)
      [.gpr 12, .gpr 6] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1093e7 12 6).toInstrSpec (add_r64_r64_effect_step 0x1093e7 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x1093ea [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x1093ea) (movR64R64Effect 0x1093ea 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1093ea 7 15).toInstrSpec (mov_r64_r64_effect_step 0x1093ea 0x4c 0xff (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x1093ed [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x1093ed) (movR64R64Effect 0x1093ed 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1093ed 6 3).toInstrSpec (mov_r64_r64_effect_step 0x1093ed 0x48 0xde (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x1093f0 [0x41, 0xFF, 0xC9] (fun s => s.RIP = 0x1093f0) (decR32Effect 0x1093f0 3 9)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (decR32Effect_footprint 0x1093f0 3 9).toInstrSpec (dec_r32_rex_effect_step 0x1093f0 0x41 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 204) (RestInside.exec (n := 204) (ρ' := [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 6), (7, 188), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 200), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093d4) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 205) (RestInside.out (n := 205) f81 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 206) (ρ' := [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 6), (7, 188), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 205), (15, 200), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093d7) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f82 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 208) (ρ' := [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 207), (7, 188), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 205), (15, 200), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093dc) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f83 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 209), (7, 188), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 205), (15, 200), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093df) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 211) (RestInside.out (n := 211) f84 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 212) (ρ' := [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 211), (7, 188), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 205), (15, 200), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093e2) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 213) (RestInside.out (n := 213) f85 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 214) (ρ' := [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 211), (7, 188), (8, 65), (9, 213), (10, 163), (11, 151), (12, 149), (13, 139), (14, 205), (15, 200), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093e7) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 215) (RestInside.out (n := 215) f86 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 216) (ρ' := [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 211), (7, 188), (8, 65), (9, 213), (10, 163), (11, 151), (12, 215), (13, 139), (14, 205), (15, 200), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093ea) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f87 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 218) (ρ' := [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 211), (7, 217), (8, 65), (9, 213), (10, 163), (11, 151), (12, 215), (13, 139), (14, 205), (15, 200), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093ed) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f88 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 219), (7, 217), (8, 65), (9, 213), (10, 163), (11, 151), (12, 215), (13, 139), (14, 205), (15, 200), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093f0) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f89 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 222) f89 .ZF (fun _ => rfl) (decR32Effect_fresh 0x1093f0 3 9 _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 223) (ρ' := [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 219), (7, 217), (8, 65), (9, 221), (10, 163), (11, 151), (12, 215), (13, 139), (14, 205), (15, 200), (19, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093f3) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 224) (jcc_rel32_effect_step 0x1093f3 5 0xfffffea7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l1092a0_3 [Bindings] (code : CodeMap) :
    Rest (n := 165) code lifted (codeRange 0x1092a0 bytes_l1092a0) [(0, 125), (1, 137), (2, 161), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 163), (11, 151), (12, 149), (13, 139), (14, 141), (15, 147), (22, 22), (39, 39), (50, 50), (51, 51)]
      31 0x10938d bytes_l1092a0_3 b_l1092a0_3 := by
  have f60 : InstrSpec 0x10938d [0x48, 0x31, 0xFA] (fun s => s.RIP = 0x10938d) (xorR64R64Effect 0x10938d 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10938d 2 7).toInstrSpec (xor_r64_r64_effect_step 0x10938d 0x48 0xfa (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x109390 [0x4C, 0x21, 0xD2] (fun s => s.RIP = 0x109390) (andR64R64Effect 0x109390 2 10)
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109390 2 10).toInstrSpec (and_r64_r64_effect_step 0x109390 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x109393 [0x49, 0x31, 0xFF] (fun s => s.RIP = 0x109393) (xorR64R64Effect 0x109393 15 7)
      [.gpr 15, .gpr 7] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109393 15 7).toInstrSpec (xor_r64_r64_effect_step 0x109393 0x49 0xff (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x109396 [0x48, 0x31, 0xFA] (fun s => s.RIP = 0x109396) (xorR64R64Effect 0x109396 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109396 2 7).toInstrSpec (xor_r64_r64_effect_step 0x109396 0x48 0xfa (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x109399 [0x49, 0xF7, 0xD9] (fun s => s.RIP = 0x109399) (negR64Effect 0x109399 9)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (negR64Effect_footprint 0x109399 9).toInstrSpec (neg_r64_effect_step 0x109399 0x49 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x10939c [0x49, 0x21, 0xD1] (fun s => s.RIP = 0x10939c) (andR64R64Effect 0x10939c 9 2)
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10939c 9 2).toInstrSpec (and_r64_r64_effect_step 0x10939c 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x10939f [0x4D, 0x01, 0xCE] (fun s => s.RIP = 0x10939f) (addR64R64Effect 0x10939f 14 9)
      [.gpr 14, .gpr 9] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10939f 14 9).toInstrSpec (add_r64_r64_effect_step 0x10939f 0x4d 0xce (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x1093a2 [0x4C, 0x89, 0x74, 0x24, 0x08] (StorePre 0x1093a2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1093a2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1093a2 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1093a2 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1093a2 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f68 : InstrSpec 0x1093a7 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x1093a7) (movR64R64Effect 0x1093a7 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1093a7 2 6).toInstrSpec (mov_r64_r64_effect_step 0x1093a7 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x1093aa [0x48, 0xF7, 0xDA] (fun s => s.RIP = 0x1093aa) (negR64Effect 0x1093aa 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR64Effect_footprint 0x1093aa 2).toInstrSpec (neg_r64_effect_step 0x1093aa 0x48 0xda (by decide) (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x1093ad [0x4C, 0x8D, 0x4C, 0x24, 0x10] (fun s => s.RIP = 0x1093ad) (leaR64Effect 0x1093ad 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x1093ad 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1093ad 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x1093b2 [0x0F, 0xB6, 0x7C, 0x24, 0x10] (LoadPre 0x1093b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1093b2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1093b2 5 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1093b2 5 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x1093b2 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f72 : InstrSpec 0x1093b7 [0x48, 0xF7, 0xDF] (fun s => s.RIP = 0x1093b7) (negR64Effect 0x1093b7 7)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (negR64Effect_footprint 0x1093b7 7).toInstrSpec (neg_r64_effect_step 0x1093b7 0x48 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x1093ba [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x1093ba) (xorR64R64Effect 0x1093ba 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1093ba 2 6).toInstrSpec (xor_r64_r64_effect_step 0x1093ba 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x1093bd [0x48, 0x21, 0xFA] (fun s => s.RIP = 0x1093bd) (andR64R64Effect 0x1093bd 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1093bd 2 7).toInstrSpec (and_r64_r64_effect_step 0x1093bd 0x48 0xfa (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x1093c0 [0x48, 0x31, 0xF3] (fun s => s.RIP = 0x1093c0) (xorR64R64Effect 0x1093c0 3 6)
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1093c0 3 6).toInstrSpec (xor_r64_r64_effect_step 0x1093c0 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x1093c3 [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x1093c3) (xorR64R64Effect 0x1093c3 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1093c3 2 6).toInstrSpec (xor_r64_r64_effect_step 0x1093c3 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x1093c6 [0x48, 0xD1, 0xF9] (fun s => s.RIP = 0x1093c6) (sarR64Effect 0x1093c6 3 1 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x1093c6 3 1 1).toInstrSpec (sar_r64_one_effect_step 0x1093c6 0x48 0xf9 (by decide) (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x1093c9 [0x4D, 0x01, 0xFF] (fun s => s.RIP = 0x1093c9) (addR64R64Effect 0x1093c9 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1093c9 15 15).toInstrSpec (add_r64_r64_effect_step 0x1093c9 0x4d 0xff (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x1093cc [0x48, 0x01, 0xDB] (fun s => s.RIP = 0x1093cc) (addR64R64Effect 0x1093cc 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1093cc 3 3).toInstrSpec (add_r64_r64_effect_step 0x1093cc 0x48 0xdb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f60 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 125), (1, 137), (2, 165), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 163), (11, 151), (12, 149), (13, 139), (14, 141), (15, 147), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109390) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f61 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 125), (1, 137), (2, 167), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 163), (11, 151), (12, 149), (13, 139), (14, 141), (15, 147), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109393) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f62 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 125), (1, 137), (2, 167), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 163), (11, 151), (12, 149), (13, 139), (14, 141), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109396) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f63 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 125), (1, 137), (2, 171), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 163), (11, 151), (12, 149), (13, 139), (14, 141), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109399) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f64 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 125), (1, 137), (2, 171), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 173), (10, 163), (11, 151), (12, 149), (13, 139), (14, 141), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10939c) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f65 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 125), (1, 137), (2, 171), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 175), (10, 163), (11, 151), (12, 149), (13, 139), (14, 141), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10939f) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f66 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 125), (1, 137), (2, 171), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 175), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093a2) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.exec (n := 179) (ρ' := [(0, 125), (1, 137), (2, 171), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 175), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093a7) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f68 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 125), (1, 137), (2, 180), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 175), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093aa) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f69 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 125), (1, 137), (2, 182), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 175), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093ad) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f70 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(0, 125), (1, 137), (2, 182), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093b2) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 186) (RestInside.out (n := 186) f71 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 187) (ρ' := [(0, 125), (1, 137), (2, 182), (3, 157), (4, 4), (5, 111), (6, 6), (7, 186), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093b7) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 188) (RestInside.out (n := 188) f72 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 189) (ρ' := [(0, 125), (1, 137), (2, 182), (3, 157), (4, 4), (5, 111), (6, 6), (7, 188), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093ba) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 190) (RestInside.out (n := 190) f73 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 191) (ρ' := [(0, 125), (1, 137), (2, 190), (3, 157), (4, 4), (5, 111), (6, 6), (7, 188), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093bd) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f74 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 193) (ρ' := [(0, 125), (1, 137), (2, 192), (3, 157), (4, 4), (5, 111), (6, 6), (7, 188), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093c0) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f75 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 195) (ρ' := [(0, 125), (1, 137), (2, 192), (3, 194), (4, 4), (5, 111), (6, 6), (7, 188), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093c3) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.out (n := 196) f76 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 197) (ρ' := [(0, 125), (1, 137), (2, 196), (3, 194), (4, 4), (5, 111), (6, 6), (7, 188), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093c6) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f77 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 125), (1, 198), (2, 196), (3, 194), (4, 4), (5, 111), (6, 6), (7, 188), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093c9) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f78 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 125), (1, 198), (2, 196), (3, 194), (4, 4), (5, 111), (6, 6), (7, 188), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 200), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093cc) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f79 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 6), (7, 188), (8, 65), (9, 184), (10, 163), (11, 151), (12, 149), (13, 139), (14, 177), (15, 200), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1093cf) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1092a0_4 code

theorem rest_l1092a0_2 [Bindings] (code : CodeMap) :
    Rest (n := 125) code lifted (codeRange 0x1092a0 bytes_l1092a0) [(0, 119), (1, 1), (2, 107), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 85), (14, 109), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]
      51 0x10934c bytes_l1092a0_2 b_l1092a0_2 := by
  have f40 : InstrSpec 0x10934c [0x4C, 0x31, 0xF0] (fun s => s.RIP = 0x10934c) (xorR64R64Effect 0x10934c 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10934c 0 14).toInstrSpec (xor_r64_r64_effect_step 0x10934c 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x10934f [0x48, 0x8D, 0x14, 0x0B] (fun s => s.RIP = 0x10934f) (leaR64Effect 0x10934f 2 (.sib 3 (some 1) 0 .none))
      [.gpr 3, .gpr 1] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x10934f 2 (.sib 3 (some 1) 0 .none)).toInstrSpec (lea_r64_effect_step 0x10934f 0x48 (by decide) 2 (.sib 3 (some 1) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x109353 [0x48, 0x29, 0xD9] (fun s => s.RIP = 0x109353) (subR64R64Effect 0x109353 1 3)
      [.gpr 1, .gpr 3] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x109353 1 3).toInstrSpec (sub_r64_r64_effect_step 0x109353 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x109356 [0x49, 0xF7, 0xDF] (fun s => s.RIP = 0x109356) (negR64Effect 0x109356 15)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (negR64Effect_footprint 0x109356 15).toInstrSpec (neg_r64_effect_step 0x109356 0x49 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x109359 [0x48, 0x31, 0xD1] (fun s => s.RIP = 0x109359) (xorR64R64Effect 0x109359 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109359 1 2).toInstrSpec (xor_r64_r64_effect_step 0x109359 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x10935c [0x4C, 0x21, 0xF9] (fun s => s.RIP = 0x10935c) (andR64R64Effect 0x10935c 1 15)
      [.gpr 1, .gpr 15] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10935c 1 15).toInstrSpec (and_r64_r64_effect_step 0x10935c 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x10935f [0x48, 0x31, 0xD1] (fun s => s.RIP = 0x10935f) (xorR64R64Effect 0x10935f 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10935f 1 2).toInstrSpec (xor_r64_r64_effect_step 0x10935f 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x109362 [0x49, 0xF7, 0xDD] (fun s => s.RIP = 0x109362) (negR64Effect 0x109362 13)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (negR64Effect_footprint 0x109362 13).toInstrSpec (neg_r64_effect_step 0x109362 0x49 0xdd (by decide) (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x109365 [0x4C, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x109365 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109365 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109365 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x109365 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109365 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f49 : InstrSpec 0x10936a [0x4D, 0x89, 0xF7] (fun s => s.RIP = 0x10936a) (movR64R64Effect 0x10936a 15 14)
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10936a 15 14).toInstrSpec (mov_r64_r64_effect_step 0x10936a 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x10936d [0x49, 0x31, 0xFF] (fun s => s.RIP = 0x10936d) (xorR64R64Effect 0x10936d 15 7)
      [.gpr 15, .gpr 7] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10936d 15 7).toInstrSpec (xor_r64_r64_effect_step 0x10936d 0x49 0xff (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x109370 [0x4D, 0x21, 0xEF] (fun s => s.RIP = 0x109370) (andR64R64Effect 0x109370 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109370 15 13).toInstrSpec (and_r64_r64_effect_step 0x109370 0x4d 0xef (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x109373 [0x4C, 0x8B, 0x64, 0x24, 0x68] (LoadPre 0x109373 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x109373 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109373 12 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x109373 12 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x109373 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f53 : InstrSpec 0x109378 [0x49, 0xF7, 0xDB] (fun s => s.RIP = 0x109378) (negR64Effect 0x109378 11)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (negR64Effect_footprint 0x109378 11).toInstrSpec (neg_r64_effect_step 0x109378 0x49 0xdb (by decide) (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x10937b [0x4C, 0x89, 0xE3] (fun s => s.RIP = 0x10937b) (movR64R64Effect 0x10937b 3 12)
      [.gpr 12] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10937b 3 12).toInstrSpec (mov_r64_r64_effect_step 0x10937b 0x4c 0xe3 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x10937e [0x48, 0x31, 0xF3] (fun s => s.RIP = 0x10937e) (xorR64R64Effect 0x10937e 3 6)
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10937e 3 6).toInstrSpec (xor_r64_r64_effect_step 0x10937e 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x109381 [0x4C, 0x21, 0xDB] (fun s => s.RIP = 0x109381) (andR64R64Effect 0x109381 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109381 3 11).toInstrSpec (and_r64_r64_effect_step 0x109381 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x109384 [0x48, 0x89, 0xFA] (fun s => s.RIP = 0x109384) (movR64R64Effect 0x109384 2 7)
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x109384 2 7).toInstrSpec (mov_r64_r64_effect_step 0x109384 0x48 0xfa (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x109387 [0x48, 0xF7, 0xDA] (fun s => s.RIP = 0x109387) (negR64Effect 0x109387 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR64Effect_footprint 0x109387 2).toInstrSpec (neg_r64_effect_step 0x109387 0x48 0xda (by decide) (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x10938a [0x49, 0xF7, 0xDA] (fun s => s.RIP = 0x10938a) (negR64Effect 0x10938a 10)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (negR64Effect_footprint 0x10938a 10).toInstrSpec (neg_r64_effect_step 0x10938a 0x49 0xda (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f40 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 125), (1, 1), (2, 107), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 85), (14, 109), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10934f) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f41 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 125), (1, 1), (2, 127), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 85), (14, 109), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109353) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f42 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 125), (1, 129), (2, 127), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 85), (14, 109), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109356) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f43 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 125), (1, 129), (2, 127), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 85), (14, 109), (15, 131), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109359) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f44 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 125), (1, 133), (2, 127), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 85), (14, 109), (15, 131), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10935c) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f45 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 125), (1, 135), (2, 127), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 85), (14, 109), (15, 131), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10935f) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 125), (1, 137), (2, 127), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 85), (14, 109), (15, 131), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109362) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f47 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 125), (1, 137), (2, 127), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 139), (14, 109), (15, 131), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109365) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f48 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 125), (1, 137), (2, 127), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 139), (14, 141), (15, 131), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10936a) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f49 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 125), (1, 137), (2, 127), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 139), (14, 141), (15, 143), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10936d) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f50 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 125), (1, 137), (2, 127), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 139), (14, 141), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109370) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f51 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 125), (1, 137), (2, 127), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 139), (14, 141), (15, 147), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109373) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f52 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 125), (1, 137), (2, 127), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 149), (13, 139), (14, 141), (15, 147), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109378) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f53 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 125), (1, 137), (2, 127), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 151), (12, 149), (13, 139), (14, 141), (15, 147), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10937b) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f54 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 125), (1, 137), (2, 127), (3, 153), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 151), (12, 149), (13, 139), (14, 141), (15, 147), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10937e) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f55 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 125), (1, 137), (2, 127), (3, 155), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 151), (12, 149), (13, 139), (14, 141), (15, 147), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109381) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f56 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 125), (1, 137), (2, 127), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 151), (12, 149), (13, 139), (14, 141), (15, 147), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109384) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f57 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 125), (1, 137), (2, 159), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 151), (12, 149), (13, 139), (14, 141), (15, 147), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109387) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f58 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 125), (1, 137), (2, 161), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 151), (12, 149), (13, 139), (14, 141), (15, 147), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10938a) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f59 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 125), (1, 137), (2, 161), (3, 157), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 163), (11, 151), (12, 149), (13, 139), (14, 141), (15, 147), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10938d) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1092a0_3 code

theorem rest_l1092a0_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x1092a0 bytes_l1092a0) [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (12, 79), (13, 85), (14, 75), (15, 82), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]
      71 0x1092fe bytes_l1092a0_1 b_l1092a0_1 := by
  have f20 : InstrSpec 0x1092fe [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x10] (LoadPre 0x1092fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092fe + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1092fe 6 11 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x1092fe 6 11 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1092fe 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x109304 [0x0F, 0x9F, 0x44, 0x24, 0x10] (StorePre 0x109304 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109304 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 15) (setccM8Effect 0x109304 5 (.sib 4 none 0 (.d8 0x10))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF, .SF, .OF] [.rip] :=
    (setccM8Effect_footprint 0x109304 5 (.sib 4 none 0 (.d8 0x10)) 15).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x109304 15 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x109309 [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x10] (LoadPre 0x109309 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109309 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109309 6 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x109309 6 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x109309 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x10930f [0x44, 0x88, 0x44, 0x24, 0x10] (StorePre 0x10930f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10930f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10930f 5 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10930f 5 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10930f 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x109314 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x10] (LoadPre 0x109314 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109314 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109314 6 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x109314 6 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x109314 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x10931a [0x0F, 0x9F, 0x44, 0x24, 0x10] (StorePre 0x10931a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10931a + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 15) (setccM8Effect 0x10931a 5 (.sib 4 none 0 (.d8 0x10))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF, .SF, .OF] [.rip] :=
    (setccM8Effect_footprint 0x10931a 5 (.sib 4 none 0 (.d8 0x10)) 15).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x10931a 15 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x10931f [0xBA, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10931f) (movR32Imm32Effect 0x10931f 5 2 0x2)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10931f 5 2 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x10931f 0xba (by decide) 0x2) pre_rip
  have f27 : InstrSpec 0x109324 [0x48, 0x29, 0xEA] (fun s => s.RIP = 0x109324) (subR64R64Effect 0x109324 2 5)
      [.gpr 2, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x109324 2 5).toInstrSpec (sub_r64_r64_effect_step 0x109324 0x48 0xea (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x109327 [0x48, 0x83, 0xC5, 0x02] (fun s => s.RIP = 0x109327) (addR64Imm8Effect 0x109327 5 0x2)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x109327 5 0x2).toInstrSpec (add_r64_imm8_effect_step 0x109327 0x48 0xc5 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x10932b [0x49, 0xF7, 0xDE] (fun s => s.RIP = 0x10932b) (negR64Effect 0x10932b 14)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (negR64Effect_footprint 0x10932b 14).toInstrSpec (neg_r64_effect_step 0x10932b 0x49 0xde (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10932e [0x48, 0x31, 0xEA] (fun s => s.RIP = 0x10932e) (xorR64R64Effect 0x10932e 2 5)
      [.gpr 2, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10932e 2 5).toInstrSpec (xor_r64_r64_effect_step 0x10932e 0x48 0xea (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x109331 [0x4C, 0x21, 0xF2] (fun s => s.RIP = 0x109331) (andR64R64Effect 0x109331 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109331 2 14).toInstrSpec (and_r64_r64_effect_step 0x109331 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x109334 [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x109334) (movR64R64Effect 0x109334 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x109334 14 0).toInstrSpec (mov_r64_r64_effect_step 0x109334 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x109337 [0x48, 0x31, 0xD5] (fun s => s.RIP = 0x109337) (xorR64R64Effect 0x109337 5 2)
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109337 5 2).toInstrSpec (xor_r64_r64_effect_step 0x109337 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x10933a [0x49, 0xF7, 0xDC] (fun s => s.RIP = 0x10933a) (negR64Effect 0x10933a 12)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (negR64Effect_footprint 0x10933a 12).toInstrSpec (neg_r64_effect_step 0x10933a 0x49 0xdc (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x10933d [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x10933d) (movR64R64Effect 0x10933d 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10933d 0 1).toInstrSpec (mov_r64_r64_effect_step 0x10933d 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x109340 [0x4C, 0x31, 0xF0] (fun s => s.RIP = 0x109340) (xorR64R64Effect 0x109340 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x109340 0 14).toInstrSpec (xor_r64_r64_effect_step 0x109340 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x109343 [0x4C, 0x21, 0xE0] (fun s => s.RIP = 0x109343) (andR64R64Effect 0x109343 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109343 0 12).toInstrSpec (and_r64_r64_effect_step 0x109343 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x109346 [0x48, 0xF7, 0xDB] (fun s => s.RIP = 0x109346) (negR64Effect 0x109346 3)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (negR64Effect_footprint 0x109346 3).toInstrSpec (neg_r64_effect_step 0x109346 0x48 0xdb (by decide) (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x109349 [0x4C, 0x21, 0xF3] (fun s => s.RIP = 0x109349) (andR64R64Effect 0x109349 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x109349 3 14).toInstrSpec (and_r64_r64_effect_step 0x109349 0x4c 0xf3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f20 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (11, 88), (12, 79), (13, 85), (14, 75), (15, 82), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109304) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (11, 88), (12, 79), (13, 85), (14, 75), (15, 82), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109309) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f22 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (10, 91), (11, 88), (12, 79), (13, 85), (14, 75), (15, 82), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10930f) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (10, 91), (11, 88), (12, 79), (13, 85), (14, 75), (15, 82), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109314) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f24 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 79), (13, 85), (14, 75), (15, 82), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10931a) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 79), (13, 85), (14, 75), (15, 82), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10931f) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f26 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 0), (1, 1), (2, 97), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 79), (13, 85), (14, 75), (15, 82), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109324) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 0), (1, 1), (2, 99), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 79), (13, 85), (14, 75), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109327) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f28 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 0), (1, 1), (2, 99), (3, 72), (4, 4), (5, 101), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 79), (13, 85), (14, 75), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10932b) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f29 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 0), (1, 1), (2, 99), (3, 72), (4, 4), (5, 101), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 79), (13, 85), (14, 103), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10932e) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f30 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 0), (1, 1), (2, 105), (3, 72), (4, 4), (5, 101), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 79), (13, 85), (14, 103), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109331) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f31 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 0), (1, 1), (2, 107), (3, 72), (4, 4), (5, 101), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 79), (13, 85), (14, 103), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109334) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f32 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 0), (1, 1), (2, 107), (3, 72), (4, 4), (5, 101), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 79), (13, 85), (14, 109), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109337) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f33 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 0), (1, 1), (2, 107), (3, 72), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 79), (13, 85), (14, 109), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10933a) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f34 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 0), (1, 1), (2, 107), (3, 72), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 85), (14, 109), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10933d) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f35 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 115), (1, 1), (2, 107), (3, 72), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 85), (14, 109), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109340) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f36 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 117), (1, 1), (2, 107), (3, 72), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 85), (14, 109), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109343) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f37 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 119), (1, 1), (2, 107), (3, 72), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 85), (14, 109), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109346) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f38 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 119), (1, 1), (2, 107), (3, 121), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 85), (14, 109), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109349) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f39 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 119), (1, 1), (2, 107), (3, 123), (4, 4), (5, 111), (6, 6), (7, 7), (8, 65), (9, 94), (10, 91), (11, 88), (12, 113), (13, 85), (14, 109), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10934c) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1092a0_2 code

theorem rest_l1092a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1092a0 bytes_l1092a0) (entryMap (live .l1092a0))
      91 0x1092a0 bytes_l1092a0 b_l1092a0 := by
  have f0 : InstrSpec 0x1092a0 [0x44, 0x89, 0x4C, 0x24, 0x60] (StorePre 0x1092a0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1092a0 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1092a0 9 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1092a0 9 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m32_r32_effect_step 0x1092a0 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1092a5 [0x4C, 0x89, 0x64, 0x24, 0x68] (StorePre 0x1092a5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1092a5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1092a5 12 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1092a5 12 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x1092a5 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1092aa [0x48, 0x85, 0xED] (fun s => s.RIP = 0x1092aa) (testR64R64Effect 0x1092aa 5 5)
      [.gpr 5, .gpr 5] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1092aa 5 5).toInstrSpec (test_r64_r64_effect_step 0x1092aa 0x48 0xed (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1092ad [0x41, 0x0F, 0x9F, 0xC1] (fun s => s.RIP = 0x1092ad) (atFlags (condHolds 15) (setccR8Effect 0x1092ad 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF, .SF, .OF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x1092ad 4 9 15).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1092ad 15 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f4 : InstrSpec 0x1092b1 [0x41, 0x20, 0xC9] (fun s => s.RIP = 0x1092b1) (andR8R8Effect 0x1092b1 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (andR8R8Effect_footprint 0x1092b1 3 9 1).toInstrSpec (and_r8_r8_rex_effect_step 0x1092b1 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1092b4 [0x41, 0x89, 0xC8] (fun s => s.RIP = 0x1092b4) (movR32R32Effect 0x1092b4 3 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x1092b4 3 8 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x1092b4 0x41 0xc8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1092b7 [0x41, 0x80, 0xE0, 0x01] (fun s => s.RIP = 0x1092b7) (andR8Imm8Effect 0x1092b7 4 8 0x1)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x1092b7 4 8 0x1).toInstrSpec (and_r8_imm8_rex_effect_step 0x1092b7 0x41 0xe0 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1092bb [0x48, 0x85, 0xED] (fun s => s.RIP = 0x1092bb) (testR64R64Effect 0x1092bb 5 5)
      [.gpr 5, .gpr 5] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1092bb 5 5).toInstrSpec (test_r64_r64_effect_step 0x1092bb 0x48 0xed (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1092be [0x44, 0x88, 0x44, 0x24, 0x10] (StorePre 0x1092be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092be + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092be 5 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1092be 5 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1092be 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1092c3 [0x0F, 0xB6, 0x5C, 0x24, 0x10] (LoadPre 0x1092c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092c3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1092c3 5 3 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x1092c3 5 3 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x1092c3 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1092c8 [0x44, 0x88, 0x4C, 0x24, 0x10] (StorePre 0x1092c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092c8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092c8 5 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1092c8 5 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1092c8 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1092cd [0x44, 0x0F, 0xB6, 0x74, 0x24, 0x10] (LoadPre 0x1092cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092cd + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1092cd 6 14 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x1092cd 6 14 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1092cd 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1092d3 [0x44, 0x88, 0x4C, 0x24, 0x10] (StorePre 0x1092d3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092d3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092d3 5 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1092d3 5 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1092d3 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1092d8 [0x48, 0x8D, 0x54, 0x24, 0x10] (fun s => s.RIP = 0x1092d8) (leaR64Effect 0x1092d8 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1092d8 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1092d8 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1092dd [0x44, 0x0F, 0xB6, 0x64, 0x24, 0x10] (LoadPre 0x1092dd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092dd + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1092dd 6 12 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x1092dd 6 12 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1092dd 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1092e3 [0x44, 0x88, 0x4C, 0x24, 0x10] (StorePre 0x1092e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092e3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092e3 5 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1092e3 5 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1092e3 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1092e8 [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x10] (LoadPre 0x1092e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092e8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1092e8 6 15 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x1092e8 6 15 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1092e8 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x1092ee [0x44, 0x88, 0x4C, 0x24, 0x10] (StorePre 0x1092ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092ee + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092ee 5 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1092ee 5 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1092ee 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1092f3 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x10] (LoadPre 0x1092f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092f3 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1092f3 6 13 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x1092f3 6 13 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1092f3 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x1092f9 [0x44, 0x88, 0x4C, 0x24, 0x10] (StorePre 0x1092f9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092f9 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092f9 5 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1092f9 5 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1092f9 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092a5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092aa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f2 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 57) f2 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (19, 55), (20, 56), (21, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092ad) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (9, 59), (12, 12), (19, 55), (20, 56), (21, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092b1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (9, 61), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092b4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 61), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092b7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092bb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f7 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 69) f7 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (12, 12), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092be) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (12, 12), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092c3) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (12, 12), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092c8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (12, 12), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092cd) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (12, 12), (14, 75), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092d3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (12, 12), (14, 75), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092d8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (12, 12), (14, 75), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092dd) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (12, 79), (14, 75), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092e3) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (12, 79), (14, 75), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092e8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (12, 79), (14, 75), (15, 82), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092ee) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (12, 79), (14, 75), (15, 82), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092f3) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (12, 79), (13, 85), (14, 75), (15, 82), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092f9) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 1), (3, 72), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 61), (12, 79), (13, 85), (14, 75), (15, 82), (19, 67), (20, 68), (21, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1092fe) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1092a0_1 code

theorem block_l1092a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1092a0 :=
  Rest.liftedBlock (rest_l1092a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1092a0 x hx)

theorem rest_l1093f9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1093f9 bytes_l1093f9) (entryMap (live .l1093f9))
      1 0x1093f9 bytes_l1093f9 b_l1093f9 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x1093f9 0xfffffb99 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1093f9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1093f9 :=
  Rest.liftedBlock (rest_l1093f9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1093f9 x hx)

theorem rest_l1093fe [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1093fe bytes_l1093fe) (entryMap (live .l1093fe))
      11 0x1093fe bytes_l1093fe b_l1093fe := by
  have f0 : InstrSpec 0x1093fe [0x48, 0x8B, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00] (LoadPre 0x1093fe (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1093fe + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1093fe 0 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1093fe 0 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_r64_m64_effect_step 0x1093fe 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x109406 [0x48, 0x0B, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00] (LoadPre 0x109406 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x109406 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109406 0 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x109406 0 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (or_r64_m64_effect_step 0x109406 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10940e [0x48, 0x0B, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00] (LoadPre 0x10940e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10940e + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x10940e 0 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x10940e 0 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (or_r64_m64_effect_step 0x10940e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109416 [0x48, 0x0B, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00] (LoadPre 0x109416 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x109416 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109416 0 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x109416 0 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (or_r64_m64_effect_step 0x109416 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10941e [0x0F, 0x95, 0xC3] (fun s => s.RIP = 0x10941e) (atFlags (condHolds 5) (setccR8Effect 0x10941e 3 3))
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 3, .rip] :=
    (setccR8Effect_footprint 0x10941e 3 3 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x10941e 5 0xc3 (by decide) (by decide) c)) pre_rip
  have f5 : InstrSpec 0x109421 [0x8B, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x109421 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x109421 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x109421 2 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x109421 2 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r32_m32_low_effect_step 0x109421 2 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x109428 [0x48, 0x8D, 0xB4, 0x24, 0xD0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109428) (leaR64Effect 0x109428 6 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x109428 6 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (lea_r64_effect_step 0x109428 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x109430 [0x4C, 0x8B, 0xB4, 0x24, 0x40, 0x01, 0x00, 0x00] (LoadPre 0x109430 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x109430 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109430 14 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x109430 14 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_r64_m64_effect_step 0x109430 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x109438 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x109438) (movR64R64Effect 0x109438 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x109438 7 14).toInstrSpec (mov_r64_r64_effect_step 0x109438 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10943b [0x48, 0x8B, 0x8C, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x10943b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10943b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10943b 1 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10943b 1 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x10943b 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x109443 [0xE8, 0xB8, 0x07, 0x00, 0x00] (PushPre 0x109443 5) (callEffect (fun _ => 0x109c00) 0x109448)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109443 0x109c00 0x109448).toInstrSpec (call_rel32_effect_step 0x109443 0x7b8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109406) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10940e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109416) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10941e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 61), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109421) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 63), (3, 61), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109428) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 63), (3, 61), (4, 4), (5, 5), (6, 65), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109430) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 63), (3, 61), (4, 4), (5, 5), (6, 65), (12, 12), (13, 13), (14, 67), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109438) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 63), (3, 61), (4, 4), (5, 5), (6, 65), (7, 69), (12, 12), (13, 13), (14, 67), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10943b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 71), (2, 63), (3, 61), (4, 4), (5, 5), (6, 65), (7, 69), (12, 12), (13, 13), (14, 67), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109443) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 71), (2, 63), (3, 61), (4, 73), (5, 5), (6, 65), (7, 69), (12, 12), (13, 13), (14, 67), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c00) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l1093fe [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1093fe :=
  Rest.liftedBlock (rest_l1093fe code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1093fe x hx)

theorem rest_l109448 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109448 bytes_l109448) (entryMap (live .l109448))
      17 0x109448 bytes_l109448 b_l109448 := by
  have f0 : InstrSpec 0x109448 [0x48, 0x8B, 0x44, 0x24, 0x78] (LoadPre 0x109448 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109448 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109448 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109448 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x109448 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10944d [0x48, 0x83, 0xF0, 0x01] (fun s => s.RIP = 0x10944d) (xorR64Imm8Effect 0x10944d 0 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR64Imm8Effect_footprint 0x10944d 0 0x1).toInstrSpec (xor_r64_imm8_effect_step 0x10944d 0x48 0xf0 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x109451 [0x48, 0x0B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x109451 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109451 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109451 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x109451 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (or_r64_m64_effect_step 0x109451 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109459 [0x48, 0x0B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x109459 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x109459 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109459 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x109459 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (or_r64_m64_effect_step 0x109459 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x109461 [0x48, 0x0B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x109461 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x109461 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109461 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x109461 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (or_r64_m64_effect_step 0x109461 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x109469 [0x0F, 0x94, 0xC0] (fun s => s.RIP = 0x109469) (atFlags (condHolds 4) (setccR8Effect 0x109469 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x109469 3 0 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x109469 4 0xc0 (by decide) (by decide) c)) pre_rip
  have f6 : InstrSpec 0x10946c [0x20, 0xD8] (fun s => s.RIP = 0x10946c) (andR8R8Effect 0x10946c 2 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR8R8Effect_footprint 0x10946c 2 0 3).toInstrSpec (and_r8_r8_effect_step 0x10946c 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10946e [0x41, 0x88, 0x46, 0x20] (StorePre 0x10946e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x10946e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10946e 4 0 (.base 14 (.d8 0x20)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM8R8Effect_footprint 0x10946e 4 0 (.base 14 (.d8 0x20))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10946e 0x41 (by decide) 0 (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x109472 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x109472) (movR64R64Effect 0x109472 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109472 0 14).toInstrSpec (mov_r64_r64_effect_step 0x109472 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x109475 [0x48, 0x81, 0xC4, 0x68, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x109475) (addR64Imm32Effect 0x109475 4 0x168)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x109475 4 0x168).toInstrSpec (add_r64_imm32_effect_step 0x109475 0x48 0xc4 0x168 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10947c [0x5B] (PopPre 0x10947c) (popR64Effect 0x10947c 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10947c 1 3).toInstrSpec (pop_r64_effect_step 0x10947c 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x10947d [0x41, 0x5C] (PopPre 0x10947d) (popR64Effect 0x10947d 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10947d 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10947d 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x10947f [0x41, 0x5D] (PopPre 0x10947f) (popR64Effect 0x10947f 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10947f 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10947f 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f13 : InstrSpec 0x109481 [0x41, 0x5E] (PopPre 0x109481) (popR64Effect 0x109481 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109481 2 14).toInstrSpec (pop_r64_rex_effect_step 0x109481 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f14 : InstrSpec 0x109483 [0x41, 0x5F] (PopPre 0x109483) (popR64Effect 0x109483 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109483 2 15).toInstrSpec (pop_r64_rex_effect_step 0x109483 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f15 : InstrSpec 0x109485 [0x5D] (PopPre 0x109485) (popR64Effect 0x109485 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109485 1 5).toInstrSpec (pop_r64_effect_step 0x109485 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f16 : InstrSpec 0x109486 [0xC3] (RetPre 0x109486) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x109486).toInstrSpec (ret_effect_step 0x109486) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10944d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109451) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109459) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109461) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109469) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10946c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10946e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109472) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109475) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 3), (4, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10947c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 73), (4, 74), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10947d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 73), (4, 77), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10947f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f12 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 80) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 81) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 73), (4, 80), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 79), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109481) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f13 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 73), (4, 83), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 79), (14, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109483) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f14 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 73), (4, 86), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 79), (14, 82), (15, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109485) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f15 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 89) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 90) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 73), (4, 89), (5, 88), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 79), (14, 82), (15, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109486) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f16 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 92) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 93) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 73), (4, 92), (5, 88), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 79), (14, 82), (15, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) f16 (by decide) rfl rfl rfl (by decide)

theorem block_l109448 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109448 :=
  Rest.liftedBlock (rest_l109448 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109448 x hx)

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

theorem_by block_l108e30_eval :
    program.runBlock (dialect code) ⟨.l108e30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108f80_eval :
    program.runBlock (dialect code) ⟨.l108f80, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108f97_eval :
    program.runBlock (dialect code) ⟨.l108f97, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108fe2_eval :
    program.runBlock (dialect code) ⟨.l108fe2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109036_eval :
    program.runBlock (dialect code) ⟨.l109036, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109107_eval :
    program.runBlock (dialect code) ⟨.l109107, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10914e_eval :
    program.runBlock (dialect code) ⟨.l10914e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1091e4_eval :
    program.runBlock (dialect code) ⟨.l1091e4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109246_eval :
    program.runBlock (dialect code) ⟨.l109246, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1092a0_eval :
    program.runBlock (dialect code) ⟨.l1092a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1093f9_eval :
    program.runBlock (dialect code) ⟨.l1093f9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1093fe_eval :
    program.runBlock (dialect code) ⟨.l1093fe, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109448_eval :
    program.runBlock (dialect code) ⟨.l109448, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Generate.LIR
