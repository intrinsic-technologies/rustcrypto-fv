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

theorem rest_l104970_1 [Bindings] (code : CodeMap) :
    Rest (n := 85) code lifted (codeRange 0x104970 bytes_l104970) [(0, 73), (1, 75), (2, 77), (3, 67), (4, 65), (5, 5), (6, 79), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      5 0x1049d7 bytes_l104970_1 b_l104970_1 := by
  have f20 : InstrSpec 0x1049d7 [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1049d7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1049d7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1049d7 (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1049d7 (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1049d7 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x1049e0 [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1049e0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1049e0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1049e0 (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1049e0 (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1049e0 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x1049e9 [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1049e9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1049e9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1049e9 (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1049e9 (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1049e9 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x1049f2 [0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1049f2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1049f2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1049f2 (.sib 4 none 0 (.d8 0x40)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1049f2 (.sib 4 none 0 (.d8 0x40)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1049f2 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x1049fb [0xB8, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1049fb) (movR32Imm32Effect 0x1049fb 5 0 0x3)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1049fb 5 0 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x1049fb 0xb8 (by decide) 0x3) pre_rip
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 73), (1, 75), (2, 77), (3, 67), (4, 65), (5, 5), (6, 79), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049e0) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 73), (1, 75), (2, 77), (3, 67), (4, 65), (5, 5), (6, 79), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049e9) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 73), (1, 75), (2, 77), (3, 67), (4, 65), (5, 5), (6, 79), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049f2) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 73), (1, 75), (2, 77), (3, 67), (4, 65), (5, 5), (6, 79), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049fb) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 75), (2, 77), (3, 67), (4, 65), (5, 5), (6, 79), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a00) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 91) (by decide) rfl

theorem rest_l104970 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104970 bytes_l104970) (entryMap (live .l104970))
      25 0x104970 bytes_l104970 b_l104970 := by
  have f0 : InstrSpec 0x104970 [0x55] (PushPre 0x104970 1) (pushR64Effect 0x104970 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104970 1 5).toInstrSpec (push_r64_effect_step 0x104970 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x104971 [0x41, 0x57] (PushPre 0x104971 2) (pushR64Effect 0x104971 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104971 2 15).toInstrSpec (push_r64_rex_effect_step 0x104971 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x104973 [0x41, 0x56] (PushPre 0x104973 2) (pushR64Effect 0x104973 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104973 2 14).toInstrSpec (push_r64_rex_effect_step 0x104973 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x104975 [0x41, 0x55] (PushPre 0x104975 2) (pushR64Effect 0x104975 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104975 2 13).toInstrSpec (push_r64_rex_effect_step 0x104975 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x104977 [0x41, 0x54] (PushPre 0x104977 2) (pushR64Effect 0x104977 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104977 2 12).toInstrSpec (push_r64_rex_effect_step 0x104977 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x104979 [0x53] (PushPre 0x104979 1) (pushR64Effect 0x104979 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104979 1 3).toInstrSpec (push_r64_effect_step 0x104979 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10497a [0x48, 0x81, 0xEC, 0xB8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10497a) (subR64Imm32Effect 0x10497a 4 0x1b8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10497a 4 0x1b8).toInstrSpec (sub_r64_imm32_effect_step 0x10497a 0x48 0xec 0x1b8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x104981 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x104981) (movR64R64Effect 0x104981 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x104981 3 7).toInstrSpec (mov_r64_r64_effect_step 0x104981 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x104984 [0x48, 0xC7, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104984 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x104984 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x104984 (.sib 4 none 0 (.d32 0x148)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104984 (.sib 4 none 0 (.d32 0x148)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104984 0x48 (by decide) (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x104990 [0x48, 0xC7, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104990 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x104990 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x104990 (.sib 4 none 0 (.d32 0x140)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104990 (.sib 4 none 0 (.d32 0x140)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104990 0x48 (by decide) (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10499c [0x48, 0xC7, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10499c 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x10499c + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10499c (.sib 4 none 0 (.d32 0x138)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10499c (.sib 4 none 0 (.d32 0x138)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10499c 0x48 (by decide) (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1049a8 [0x48, 0xC7, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1049a8 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x1049a8 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1049a8 (.sib 4 none 0 (.d32 0x130)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1049a8 (.sib 4 none 0 (.d32 0x130)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1049a8 0x48 (by decide) (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1049b4 [0x48, 0x8B, 0x47, 0x18] (LoadPre 0x1049b4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x1049b4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1049b4 0 (.base 7 (.d8 0x18)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1049b4 0 (.base 7 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1049b4 0x48 (by decide) 0 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1049b8 [0x48, 0x8B, 0x4F, 0x10] (LoadPre 0x1049b8 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x1049b8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1049b8 1 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1049b8 1 (.base 7 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1049b8 0x48 (by decide) 1 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1049bc [0x48, 0x8B, 0x17] (LoadPre 0x1049bc (fun s => AddrMode.addr (.base 7 .none) s (0x1049bc + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1049bc 2 (.base 7 .none))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1049bc 2 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1049bc 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1049bf [0x48, 0x8B, 0x77, 0x08] (LoadPre 0x1049bf (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1049bf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1049bf 6 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1049bf 6 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1049bf 0x48 (by decide) 6 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1049c3 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x1049c3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1049c3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1049c3 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1049c3 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1049c3 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x1049c8 [0x48, 0x89, 0x74, 0x24, 0x10] (StorePre 0x1049c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1049c8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1049c8 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1049c8 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1049c8 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1049cd [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x1049cd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1049cd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1049cd 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1049cd 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1049cd 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1049d2 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x1049d2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1049d2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1049d2 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1049d2 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1049d2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104971) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104973) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104975) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104977) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104979) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10497a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104981) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(3, 67), (4, 65), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104984) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(3, 67), (4, 65), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104990) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(3, 67), (4, 65), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10499c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(3, 67), (4, 65), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049a8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(3, 67), (4, 65), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049b4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (3, 67), (4, 65), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049b8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 73), (1, 75), (3, 67), (4, 65), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049bc) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 73), (1, 75), (2, 77), (3, 67), (4, 65), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049bf) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 73), (1, 75), (2, 77), (3, 67), (4, 65), (5, 5), (6, 79), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049c3) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 73), (1, 75), (2, 77), (3, 67), (4, 65), (5, 5), (6, 79), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049c8) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 73), (1, 75), (2, 77), (3, 67), (4, 65), (5, 5), (6, 79), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049cd) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 73), (1, 75), (2, 77), (3, 67), (4, 65), (5, 5), (6, 79), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049d2) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 73), (1, 75), (2, 77), (3, 67), (4, 65), (5, 5), (6, 79), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049d7) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l104970_1 code

theorem block_l104970 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104970 :=
  Rest.liftedBlock (rest_l104970 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104970 x hx)

theorem rest_l104a00 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104a00 bytes_l104a00) (entryMap (live .l104a00))
      7 0x104a00 bytes_l104a00 b_l104a00 := by
  have f0 : InstrSpec 0x104a00 [0x80, 0x74, 0x04, 0x05, 0x36] (StorePre 0x104a00 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x5)) s (0x104a00 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104a00 5 (.sib 4 (some 0) 0 (.d8 0x5)) 0x36)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x104a00 5 (.sib 4 (some 0) 0 (.d8 0x5)) 0x36).toInstrSpec (xor_m8_imm8_effect_step 0x104a00 (.sib 4 (some 0) 0 (.d8 0x5)) (by decide) (by decide) (by decide) 0x36) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104a05 [0x80, 0x74, 0x04, 0x06, 0x36] (StorePre 0x104a05 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x6)) s (0x104a05 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104a05 5 (.sib 4 (some 0) 0 (.d8 0x6)) 0x36)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x104a05 5 (.sib 4 (some 0) 0 (.d8 0x6)) 0x36).toInstrSpec (xor_m8_imm8_effect_step 0x104a05 (.sib 4 (some 0) 0 (.d8 0x6)) (by decide) (by decide) (by decide) 0x36) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x104a0a [0x80, 0x74, 0x04, 0x07, 0x36] (StorePre 0x104a0a 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x7)) s (0x104a0a + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104a0a 5 (.sib 4 (some 0) 0 (.d8 0x7)) 0x36)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x104a0a 5 (.sib 4 (some 0) 0 (.d8 0x7)) 0x36).toInstrSpec (xor_m8_imm8_effect_step 0x104a0a (.sib 4 (some 0) 0 (.d8 0x7)) (by decide) (by decide) (by decide) 0x36) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x104a0f [0x80, 0x74, 0x04, 0x08, 0x36] (StorePre 0x104a0f 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x8)) s (0x104a0f + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104a0f 5 (.sib 4 (some 0) 0 (.d8 0x8)) 0x36)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x104a0f 5 (.sib 4 (some 0) 0 (.d8 0x8)) 0x36).toInstrSpec (xor_m8_imm8_effect_step 0x104a0f (.sib 4 (some 0) 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x36) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x104a14 [0x48, 0x83, 0xC0, 0x04] (fun s => s.RIP = 0x104a14) (addR64Imm8Effect 0x104a14 0 0x4)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x104a14 0 0x4).toInstrSpec (add_r64_imm8_effect_step 0x104a14 0x48 0xc0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104a18 [0x48, 0x83, 0xF8, 0x43] (fun s => s.RIP = 0x104a18) (cmpR64Imm8Effect 0x104a18 0 0x43)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x104a18 0 0x43).toInstrSpec (cmp_r64_imm8_effect_step 0x104a18 0x48 0xf8 0x43 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a05) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a0a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a0f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a14) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a18) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a1c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x104a1c 5 0xe2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104a00 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104a00 :=
  Rest.liftedBlock (rest_l104a00 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104a00 x hx)

theorem rest_l104a1e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104a1e bytes_l104a1e) (entryMap (live .l104a1e))
      15 0x104a1e bytes_l104a1e b_l104a1e := by
  have f0 : InstrSpec 0x104a1e [0x4C, 0x8D, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104a1e) (leaR64Effect 0x104a1e 14 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x104a1e 14 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (lea_r64_effect_step 0x104a1e 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104a26 [0x48, 0xB8, 0xAB, 0xD9, 0x83, 0x1F, 0x19, 0xCD, 0xE0, 0x5B] (fun s => s.RIP = 0x104a26) (movR64Imm64Effect 0x104a26 0 0x5be0cd191f83d9ab)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x104a26 0 0x5be0cd191f83d9ab).toInstrSpec (mov_r64_imm64_effect_step 0x104a26 0x48 0xb8 (by decide) (by decide) 0x5be0cd191f83d9ab) pre_rip
  have f2 : InstrSpec 0x104a30 [0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x104a30 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x104a30 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104a30 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104a30 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x104a30 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x104a38 [0x48, 0xB8, 0x7F, 0x52, 0x0E, 0x51, 0x8C, 0x68, 0x05, 0x9B] (fun s => s.RIP = 0x104a38) (movR64Imm64Effect 0x104a38 0 0x9b05688c510e527f)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x104a38 0 0x9b05688c510e527f).toInstrSpec (mov_r64_imm64_effect_step 0x104a38 0x48 0xb8 (by decide) (by decide) 0x9b05688c510e527f) pre_rip
  have f4 : InstrSpec 0x104a42 [0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x104a42 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x104a42 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104a42 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104a42 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x104a42 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x104a4a [0x48, 0xB8, 0x72, 0xF3, 0x6E, 0x3C, 0x3A, 0xF5, 0x4F, 0xA5] (fun s => s.RIP = 0x104a4a) (movR64Imm64Effect 0x104a4a 0 0xa54ff53a3c6ef372)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x104a4a 0 0xa54ff53a3c6ef372).toInstrSpec (mov_r64_imm64_effect_step 0x104a4a 0x48 0xb8 (by decide) (by decide) 0xa54ff53a3c6ef372) pre_rip
  have f6 : InstrSpec 0x104a54 [0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x104a54 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x104a54 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104a54 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104a54 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x104a54 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x104a5c [0x48, 0xB8, 0x67, 0xE6, 0x09, 0x6A, 0x85, 0xAE, 0x67, 0xBB] (fun s => s.RIP = 0x104a5c) (movR64Imm64Effect 0x104a5c 0 0xbb67ae856a09e667)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x104a5c 0 0xbb67ae856a09e667).toInstrSpec (mov_r64_imm64_effect_step 0x104a5c 0x48 0xb8 (by decide) (by decide) 0xbb67ae856a09e667) pre_rip
  have f8 : InstrSpec 0x104a66 [0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x104a66 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x104a66 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104a66 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104a66 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x104a66 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x104a6e [0xC6, 0x84, 0x24, 0xA7, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104a6e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa7)) s (0x104a6e + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x104a6e (.sib 4 none 0 (.d32 0xa7)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x104a6e (.sib 4 none 0 (.d32 0xa7)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x104a6e (.sib 4 none 0 (.d32 0xa7)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x104a76 [0x48, 0xC7, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (StorePre 0x104a76 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x104a76 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x104a76 (.sib 4 none 0 (.d32 0xc8)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104a76 (.sib 4 none 0 (.d32 0xc8)) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x104a76 0x48 (by decide) (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x104a82 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x104a82) (leaR64Effect 0x104a82 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x104a82 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x104a82 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x104a87 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104a87) (movR32Imm32Effect 0x104a87 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x104a87 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x104a87 0xba (by decide) 0x1) pre_rip
  have f13 : InstrSpec 0x104a8c [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x104a8c) (movR64R64Effect 0x104a8c 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104a8c 7 14).toInstrSpec (mov_r64_r64_effect_step 0x104a8c 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x104a8f [0xE8, 0x4C, 0xCE, 0x01, 0x00] (PushPre 0x104a8f 5) (callEffect (fun _ => 0x1218e0) 0x104a94)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104a8f 0x1218e0 0x104a94).toInstrSpec (call_rel32_effect_step 0x104a8f 0x1ce4c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a26) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a30) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a38) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a42) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a4a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a54) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a5c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a66) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a6e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a76) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a82) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 64), (1, 1), (3, 3), (4, 4), (5, 5), (6, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a87) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 64), (1, 1), (2, 71), (3, 3), (4, 4), (5, 5), (6, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a8c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 64), (1, 1), (2, 71), (3, 3), (4, 4), (5, 5), (6, 69), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a8f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 64), (1, 1), (2, 71), (3, 3), (4, 75), (5, 5), (6, 69), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l104a1e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104a1e :=
  Rest.liftedBlock (rest_l104a1e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104a1e x hx)

theorem rest_l104a94 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104a94 bytes_l104a94) (entryMap (live .l104a94))
      3 0x104a94 bytes_l104a94 b_l104a94 := by
  have f0 : InstrSpec 0x104a94 [0xC6, 0x84, 0x24, 0xA7, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104a94 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa7)) s (0x104a94 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x104a94 (.sib 4 none 0 (.d32 0xa7)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x104a94 (.sib 4 none 0 (.d32 0xa7)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x104a94 (.sib 4 none 0 (.d32 0xa7)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104a9c [0xB8, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104a9c) (movR32Imm32Effect 0x104a9c 5 0 0x3)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x104a9c 5 0 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x104a9c 0xb8 (by decide) 0x3) pre_rip
  have f2 : InstrSpec 0x104aa1 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104aa1) (fun _ => nopEffect 0x104aa1 15)
      [] [] [.rip] :=
    (nopEffect_footprint 0x104aa1 15).toInstrSpec (nop_m_effect_step 0x104aa1 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a9c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104aa1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ab0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l104a94 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104a94 :=
  Rest.liftedBlock (rest_l104a94 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104a94 x hx)

theorem rest_l104ab0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104ab0 bytes_l104ab0) (entryMap (live .l104ab0))
      7 0x104ab0 bytes_l104ab0 b_l104ab0 := by
  have f0 : InstrSpec 0x104ab0 [0x80, 0x74, 0x04, 0x05, 0x6A] (StorePre 0x104ab0 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x5)) s (0x104ab0 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104ab0 5 (.sib 4 (some 0) 0 (.d8 0x5)) 0x6a)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x104ab0 5 (.sib 4 (some 0) 0 (.d8 0x5)) 0x6a).toInstrSpec (xor_m8_imm8_effect_step 0x104ab0 (.sib 4 (some 0) 0 (.d8 0x5)) (by decide) (by decide) (by decide) 0x6a) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104ab5 [0x80, 0x74, 0x04, 0x06, 0x6A] (StorePre 0x104ab5 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x6)) s (0x104ab5 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104ab5 5 (.sib 4 (some 0) 0 (.d8 0x6)) 0x6a)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x104ab5 5 (.sib 4 (some 0) 0 (.d8 0x6)) 0x6a).toInstrSpec (xor_m8_imm8_effect_step 0x104ab5 (.sib 4 (some 0) 0 (.d8 0x6)) (by decide) (by decide) (by decide) 0x6a) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x104aba [0x80, 0x74, 0x04, 0x07, 0x6A] (StorePre 0x104aba 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x7)) s (0x104aba + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104aba 5 (.sib 4 (some 0) 0 (.d8 0x7)) 0x6a)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x104aba 5 (.sib 4 (some 0) 0 (.d8 0x7)) 0x6a).toInstrSpec (xor_m8_imm8_effect_step 0x104aba (.sib 4 (some 0) 0 (.d8 0x7)) (by decide) (by decide) (by decide) 0x6a) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x104abf [0x80, 0x74, 0x04, 0x08, 0x6A] (StorePre 0x104abf 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x8)) s (0x104abf + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104abf 5 (.sib 4 (some 0) 0 (.d8 0x8)) 0x6a)
      [.gpr 4, .gpr 0] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x104abf 5 (.sib 4 (some 0) 0 (.d8 0x8)) 0x6a).toInstrSpec (xor_m8_imm8_effect_step 0x104abf (.sib 4 (some 0) 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x6a) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x104ac4 [0x48, 0x83, 0xC0, 0x04] (fun s => s.RIP = 0x104ac4) (addR64Imm8Effect 0x104ac4 0 0x4)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x104ac4 0 0x4).toInstrSpec (add_r64_imm8_effect_step 0x104ac4 0x48 0xc0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104ac8 [0x48, 0x83, 0xF8, 0x43] (fun s => s.RIP = 0x104ac8) (cmpR64Imm8Effect 0x104ac8 0 0x43)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x104ac8 0 0x43).toInstrSpec (cmp_r64_imm8_effect_step 0x104ac8 0x48 0xf8 0x43 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ab5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104aba) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104abf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ac4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ac8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104acc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x104acc 5 0xe2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104ab0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104ab0 :=
  Rest.liftedBlock (rest_l104ab0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104ab0 x hx)

theorem rest_l104ace_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x104ace bytes_l104ace) [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x104b4b bytes_l104ace_1 b_l104ace_1 := by
  have f20 : InstrSpec 0x104b4b [0x48, 0x8D, 0x7C, 0x24, 0x68] (fun s => s.RIP = 0x104b4b) (leaR64Effect 0x104b4b 7 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x104b4b 7 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (lea_r64_effect_step 0x104b4b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x104b50 [0x48, 0x8D, 0xB4, 0x24, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x104b50) (leaR64Effect 0x104b50 6 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x104b50 6 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (lea_r64_effect_step 0x104b50 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x104b58 [0xBA, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104b58) (movR32Imm32Effect 0x104b58 5 2 0xa8)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x104b58 5 2 0xa8).toInstrSpec (mov_r32_imm32_effect_step 0x104b58 0xba (by decide) 0xa8) pre_rip
  have f23 : InstrSpec 0x104b5d [0xFF, 0x15, 0x6D, 0xF2, 0x0F, 0x00] (GoesTo (CallMemPre 0x104b5d (.rip 0xff26d)) (callEffect (callMemPtr 0x104b5d (.rip 0xff26d)) (0x104b5d + BitVec.ofNat 64 (callMemLen (.rip 0xff26d)))) 0x12a820) (callEffect (callMemPtr 0x104b5d (.rip 0xff26d)) (0x104b5d + BitVec.ofNat 64 (callMemLen (.rip 0xff26d))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x104b5d (.rip 0xff26d)).toInstrSpec (call_m64_effect_step 0x104b5d (.rip 0xff26d) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f20 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (7, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b50) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (6, 86), (7, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b58) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 78), (1, 80), (2, 88), (3, 3), (4, 4), (5, 5), (6, 86), (7, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b5d) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f23 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 78), (1, 80), (2, 88), (3, 3), (4, 90), (5, 5), (6, 86), (7, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f23 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 92) (by decide) (by decide) rfl rfl

theorem rest_l104ace [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104ace bytes_l104ace) (entryMap (live .l104ace))
      24 0x104ace bytes_l104ace b_l104ace := by
  have f0 : InstrSpec 0x104ace [0x48, 0x8D, 0xBC, 0x24, 0x50, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x104ace) (leaR64Effect 0x104ace 7 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x104ace 7 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (lea_r64_effect_step 0x104ace 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104ad6 [0x48, 0x8D, 0x74, 0x24, 0x68] (fun s => s.RIP = 0x104ad6) (leaR64Effect 0x104ad6 6 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x104ad6 6 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (lea_r64_effect_step 0x104ad6 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104adb [0xB9, 0x0D, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104adb) (movR32Imm32Effect 0x104adb 5 1 0xd)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x104adb 5 1 0xd).toInstrSpec (mov_r32_imm32_effect_step 0x104adb 0xb9 (by decide) 0xd) pre_rip
  have f3 : InstrSpec 0x104ae0 [0xF3, 0x48, 0xA5] (RepPre 0x104ae0 (RepMovsqPre 0x104ae0)) (repMovsqEffect 0x104ae0)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x104ae0).toInstrSpecOfRuns (rep_movsq_runs hstride 0x104ae0 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x104ae3 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x104ae3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x104ae3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104ae3 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104ae3 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x104ae3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x104ae8 [0x48, 0x89, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00] (StorePre 0x104ae8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x104ae8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104ae8 0 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104ae8 0 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (mov_m64_r64_effect_step 0x104ae8 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x104af0 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x104af0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x104af0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104af0 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104af0 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x104af0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x104af5 [0x48, 0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00] (StorePre 0x104af5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x104af5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104af5 0 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104af5 0 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_m64_r64_effect_step 0x104af5 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x104afd [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x104afd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x104afd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104afd 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104afd 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x104afd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x104b02 [0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00] (StorePre 0x104b02 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x104b02 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104b02 0 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104b02 0 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_m64_r64_effect_step 0x104b02 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x104b0a [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x104b0a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x104b0a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104b0a 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104b0a 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x104b0a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x104b0f [0x48, 0x89, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00] (StorePre 0x104b0f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x104b0f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104b0f 0 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104b0f 0 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_m64_r64_effect_step 0x104b0f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x104b17 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x104b17 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x104b17 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104b17 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104b17 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x104b17 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x104b1c [0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00] (StorePre 0x104b1c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x104b1c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104b1c 0 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104b1c 0 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_m64_r64_effect_step 0x104b1c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x104b24 [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x104b24 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104b24 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104b24 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104b24 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x104b24 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x104b29 [0x48, 0x89, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00] (StorePre 0x104b29 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x104b29 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104b29 0 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104b29 0 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_m64_r64_effect_step 0x104b29 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x104b31 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x104b31 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104b31 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104b31 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104b31 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x104b31 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x104b36 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x104b36 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x104b36 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104b36 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x104b36 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x104b36 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x104b3b [0x48, 0x89, 0x8C, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x104b3b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x104b3b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104b3b 1 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104b3b 1 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m64_r64_effect_step 0x104b3b 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x104b43 [0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x104b43 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x104b43 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104b43 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104b43 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m64_r64_effect_step 0x104b43 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ad6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104adb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ae0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ae3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ae8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104af0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104af5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104afd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b02) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b0a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b0f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b17) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b1c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b24) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b29) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b31) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b36) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b3b) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b43) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 78), (1, 80), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b4b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l104ace_1 code

theorem block_l104ace [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104ace :=
  Rest.liftedBlock (rest_l104ace hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104ace x hx)

theorem rest_l104b63 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104b63 bytes_l104b63) (entryMap (live .l104b63))
      4 0x104b63 bytes_l104b63 b_l104b63 := by
  have f0 : InstrSpec 0x104b63 [0x48, 0x83, 0xC3, 0x20] (fun s => s.RIP = 0x104b63) (addR64Imm8Effect 0x104b63 3 0x20)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x104b63 3 0x20).toInstrSpec (add_r64_imm8_effect_step 0x104b63 0x48 0xc3 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104b67 [0x44, 0x0F, 0xB6, 0xBC, 0x24, 0xE7, 0x00, 0x00, 0x00] (LoadPre 0x104b67 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe7)) s (0x104b67 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x104b67 9 15 (.sib 4 none 0 (.d32 0xe7)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x104b67 9 15 (.sib 4 none 0 (.d32 0xe7))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x104b67 0x44 (by decide) 7 (.sib 4 none 0 (.d32 0xe7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x104b70 [0x49, 0x83, 0xFF, 0x1F] (fun s => s.RIP = 0x104b70) (cmpR64Imm8Effect 0x104b70 15 0x1f)
      [.gpr 15] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x104b70 15 0x1f).toInstrSpec (cmp_r64_imm8_effect_step 0x104b70 0x49 0xff 0x1f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b67) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b70) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(3, 53), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b74) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x104b74 7 0x30) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104b63 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104b63 :=
  Rest.liftedBlock (rest_l104b63 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104b63 x hx)

theorem rest_l104b76 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104b76 bytes_l104b76) (entryMap (live .l104b76))
      11 0x104b76 bytes_l104b76 b_l104b76 := by
  have f0 : InstrSpec 0x104b76 [0x48, 0x8B, 0x43, 0x18] (LoadPre 0x104b76 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x104b76 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104b76 0 (.base 3 (.d8 0x18)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104b76 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x104b76 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x104b7a [0x4B, 0x89, 0x44, 0x3E, 0x18] (StorePre 0x104b7a 5 (fun s => AddrMode.addr (.sib 14 (some 15) 0 (.d8 0x18)) s (0x104b7a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104b7a 0 (.sib 14 (some 15) 0 (.d8 0x18)))
      [.gpr 0, .gpr 14, .gpr 15] [] [.rip] :=
    (movM64R64Effect_footprint 0x104b7a 0 (.sib 14 (some 15) 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x104b7a 0x4b (by decide) 0 (.sib 14 (some 15) 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x104b7f [0x48, 0x8B, 0x43, 0x10] (LoadPre 0x104b7f (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x104b7f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104b7f 0 (.base 3 (.d8 0x10)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104b7f 0 (.base 3 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x104b7f 0x48 (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x104b83 [0x4B, 0x89, 0x44, 0x3E, 0x10] (StorePre 0x104b83 5 (fun s => AddrMode.addr (.sib 14 (some 15) 0 (.d8 0x10)) s (0x104b83 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104b83 0 (.sib 14 (some 15) 0 (.d8 0x10)))
      [.gpr 0, .gpr 14, .gpr 15] [] [.rip] :=
    (movM64R64Effect_footprint 0x104b83 0 (.sib 14 (some 15) 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x104b83 0x4b (by decide) 0 (.sib 14 (some 15) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x104b88 [0x48, 0x8B, 0x03] (LoadPre 0x104b88 (fun s => AddrMode.addr (.base 3 .none) s (0x104b88 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x104b88 0 (.base 3 .none))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104b88 0 (.base 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x104b88 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x104b8b [0x48, 0x8B, 0x4B, 0x08] (LoadPre 0x104b8b (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x104b8b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104b8b 1 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x104b8b 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x104b8b 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x104b8f [0x4B, 0x89, 0x4C, 0x3E, 0x08] (StorePre 0x104b8f 5 (fun s => AddrMode.addr (.sib 14 (some 15) 0 (.d8 0x8)) s (0x104b8f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104b8f 1 (.sib 14 (some 15) 0 (.d8 0x8)))
      [.gpr 1, .gpr 14, .gpr 15] [] [.rip] :=
    (movM64R64Effect_footprint 0x104b8f 1 (.sib 14 (some 15) 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x104b8f 0x4b (by decide) 1 (.sib 14 (some 15) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x104b94 [0x4B, 0x89, 0x04, 0x3E] (StorePre 0x104b94 4 (fun s => AddrMode.addr (.sib 14 (some 15) 0 .none) s (0x104b94 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104b94 0 (.sib 14 (some 15) 0 .none))
      [.gpr 0, .gpr 14, .gpr 15] [] [.rip] :=
    (movM64R64Effect_footprint 0x104b94 0 (.sib 14 (some 15) 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x104b94 0x4b (by decide) 0 (.sib 14 (some 15) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x104b98 [0x41, 0x80, 0xCF, 0x20] (fun s => s.RIP = 0x104b98) (orR8Imm8Effect 0x104b98 4 15 0x20)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (orR8Imm8Effect_footprint 0x104b98 4 15 0x20).toInstrSpec (or_r8_imm8_rex_effect_step 0x104b98 0x41 0xcf 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x104b9c [0x44, 0x88, 0xBC, 0x24, 0xE7, 0x00, 0x00, 0x00] (StorePre 0x104b9c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe7)) s (0x104b9c + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x104b9c 8 15 (.sib 4 none 0 (.d32 0xe7)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x104b9c 8 15 (.sib 4 none 0 (.d32 0xe7))).toInstrSpec (mov_m8_r8_rex_effect_step 0x104b9c 0x44 (by decide) 7 (.sib 4 none 0 (.d32 0xe7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b7a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b7f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b83) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b88) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b8b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b8f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b94) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b98) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b9c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ba4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 68) (jmp_rel8_effect_step 0x104ba4 0x60 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l104b76 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104b76 :=
  Rest.liftedBlock (rest_l104b76 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104b76 x hx)

theorem rest_l104ba6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104ba6 bytes_l104ba6) (entryMap (live .l104ba6))
      9 0x104ba6 bytes_l104ba6 b_l104ba6 := by
  have f0 : InstrSpec 0x104ba6 [0xBA, 0x40, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104ba6) (movR32Imm32Effect 0x104ba6 5 2 0x40)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x104ba6 5 2 0x40).toInstrSpec (mov_r32_imm32_effect_step 0x104ba6 0xba (by decide) 0x40) pre_rip
  have f1 : InstrSpec 0x104bab [0x4C, 0x29, 0xFA] (fun s => s.RIP = 0x104bab) (subR64R64Effect 0x104bab 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x104bab 2 15).toInstrSpec (sub_r64_r64_effect_step 0x104bab 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104bae [0x4C, 0x8D, 0xA4, 0x24, 0xE8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104bae) (leaR64Effect 0x104bae 12 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x104bae 12 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (lea_r64_effect_step 0x104bae 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104bb6 [0x4C, 0x8D, 0x2C, 0x13] (fun s => s.RIP = 0x104bb6) (leaR64Effect 0x104bb6 13 (.sib 3 (some 2) 0 .none))
      [.gpr 3, .gpr 2] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x104bb6 13 (.sib 3 (some 2) 0 .none)).toInstrSpec (lea_r64_effect_step 0x104bb6 0x4c (by decide) 5 (.sib 3 (some 2) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x104bba [0x4B, 0x8D, 0x3C, 0x3E] (fun s => s.RIP = 0x104bba) (leaR64Effect 0x104bba 7 (.sib 14 (some 15) 0 .none))
      [.gpr 14, .gpr 15] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x104bba 7 (.sib 14 (some 15) 0 .none)).toInstrSpec (lea_r64_effect_step 0x104bba 0x4b (by decide) 7 (.sib 14 (some 15) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104bbe [0x49, 0x83, 0xC7, 0xE0] (fun s => s.RIP = 0x104bbe) (addR64Imm8Effect 0x104bbe 15 0xe0)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x104bbe 15 0xe0).toInstrSpec (add_r64_imm8_effect_step 0x104bbe 0x49 0xc7 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104bc2 [0x48, 0x8D, 0x2D, 0x57, 0x5C, 0x02, 0x00] (fun s => s.RIP = 0x104bc2) (leaR64Effect 0x104bc2 5 (.rip 0x25c57))
      [] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x104bc2 5 (.rip 0x25c57)).toInstrSpec (lea_r64_effect_step 0x104bc2 0x48 (by decide) 5 (.rip 0x25c57) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x104bc9 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x104bc9) (movR64R64Effect 0x104bc9 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x104bc9 6 3).toInstrSpec (mov_r64_r64_effect_step 0x104bc9 0x48 0xde (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x104bcc [0xFF, 0xD5] (GoesTo (CallPre 0x104bcc 2 (fun s => (Operand.reg 5 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x104bce) 0x12a820) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x104bce)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x104bcc 5 0x104bce).toInstrSpec (call_r64_effect_step 0x104bcc 0xd5 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 5 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bab) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bae) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (12, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bb6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bba) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 55), (3, 3), (4, 4), (7, 61), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bbe) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 55), (3, 3), (4, 4), (7, 61), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bc2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 65), (7, 61), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bc9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 65), (6, 67), (7, 61), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bcc) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 55), (3, 3), (4, 69), (5, 65), (6, 67), (7, 61), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l104ba6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104ba6 :=
  Rest.liftedBlock (rest_l104ba6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104ba6 x hx)

theorem rest_l104bce [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104bce bytes_l104bce) (entryMap (live .l104bce))
      5 0x104bce bytes_l104bce b_l104bce := by
  have f0 : InstrSpec 0x104bce [0x48, 0xFF, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x104bce 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x104bce + BitVec.ofNat 64 8)) 8) (incMEffect 0x104bce 8 64 (.sib 4 none 0 (.d32 0x108)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (incMEffect64_footprint 0x104bce 8 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (inc_m64_effect_step 0x104bce 0x48 (by decide) (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104bd6 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104bd6) (movR32Imm32Effect 0x104bd6 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x104bd6 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x104bd6 0xba (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x104bdb [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x104bdb) (movR64R64Effect 0x104bdb 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104bdb 7 12).toInstrSpec (mov_r64_r64_effect_step 0x104bdb 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104bde [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x104bde) (movR64R64Effect 0x104bde 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x104bde 6 14).toInstrSpec (mov_r64_r64_effect_step 0x104bde 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x104be1 [0xE8, 0xFA, 0xCC, 0x01, 0x00] (PushPre 0x104be1 5) (callEffect (fun _ => 0x1218e0) 0x104be6)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104be1 0x1218e0 0x104be6).toInstrSpec (call_rel32_effect_step 0x104be1 0x1ccfa (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bd6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bdb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bde) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104be1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l104bce [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104bce :=
  Rest.liftedBlock (rest_l104bce code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104bce x hx)

theorem rest_l104be6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104be6 bytes_l104be6) (entryMap (live .l104be6))
      7 0x104be6 bytes_l104be6 b_l104be6 := by
  have f0 : InstrSpec 0x104be6 [0x48, 0xBE, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x104be6) (movR64Imm64Effect 0x104be6 6 0x7fffffffffffffc0)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x104be6 6 0x7fffffffffffffc0).toInstrSpec (mov_r64_imm64_effect_step 0x104be6 0x48 0xbe (by decide) (by decide) 0x7fffffffffffffc0) pre_rip
  have f1 : InstrSpec 0x104bf0 [0x4C, 0x21, 0xFE] (fun s => s.RIP = 0x104bf0) (andR64R64Effect 0x104bf0 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x104bf0 6 15).toInstrSpec (and_r64_r64_effect_step 0x104bf0 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104bf3 [0x4C, 0x01, 0xEE] (fun s => s.RIP = 0x104bf3) (addR64R64Effect 0x104bf3 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x104bf3 6 13).toInstrSpec (add_r64_r64_effect_step 0x104bf3 0x4c 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104bf6 [0x44, 0x88, 0xBC, 0x24, 0xE7, 0x00, 0x00, 0x00] (StorePre 0x104bf6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe7)) s (0x104bf6 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x104bf6 8 15 (.sib 4 none 0 (.d32 0xe7)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x104bf6 8 15 (.sib 4 none 0 (.d32 0xe7))).toInstrSpec (mov_m8_r8_rex_effect_step 0x104bf6 0x44 (by decide) 7 (.sib 4 none 0 (.d32 0xe7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x104bfe [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x104bfe) (movR64R64Effect 0x104bfe 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104bfe 7 14).toInstrSpec (mov_r64_r64_effect_step 0x104bfe 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104c01 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x104c01) (movR64R64Effect 0x104c01 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x104c01 2 15).toInstrSpec (mov_r64_r64_effect_step 0x104c01 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104c04 [0xFF, 0xD5] (GoesTo (CallPre 0x104c04 2 (fun s => (Operand.reg 5 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x104c06) 0x12a820) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x104c06)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x104c04 5 0x104c06).toInstrSpec (call_r64_effect_step 0x104c04 0xd5 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 5 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bf0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bf3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bf6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bfe) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c01) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 62), (3, 3), (4, 4), (5, 5), (6, 57), (7, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c04) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 62), (3, 3), (4, 64), (5, 5), (6, 57), (7, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f6 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l104be6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104be6 :=
  Rest.liftedBlock (rest_l104be6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104be6 x hx)

theorem rest_l104c06 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104c06 bytes_l104c06) (entryMap (live .l104c06))
      5 0x104c06 bytes_l104c06 b_l104c06 := by
  have f0 : InstrSpec 0x104c06 [0x4C, 0x8D, 0xB4, 0x24, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x104c06) (leaR64Effect 0x104c06 14 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x104c06 14 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (lea_r64_effect_step 0x104c06 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104c0e [0x48, 0x8D, 0x74, 0x24, 0x68] (fun s => s.RIP = 0x104c0e) (leaR64Effect 0x104c0e 6 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x104c0e 6 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (lea_r64_effect_step 0x104c0e 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104c13 [0xBA, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104c13) (movR32Imm32Effect 0x104c13 5 2 0xa8)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x104c13 5 2 0xa8).toInstrSpec (mov_r32_imm32_effect_step 0x104c13 0xba (by decide) 0xa8) pre_rip
  have f3 : InstrSpec 0x104c18 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x104c18) (movR64R64Effect 0x104c18 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104c18 7 14).toInstrSpec (mov_r64_r64_effect_step 0x104c18 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x104c1b [0xFF, 0x15, 0xAF, 0xF1, 0x0F, 0x00] (GoesTo (CallMemPre 0x104c1b (.rip 0xff1af)) (callEffect (callMemPtr 0x104c1b (.rip 0xff1af)) (0x104c1b + BitVec.ofNat 64 (callMemLen (.rip 0xff1af)))) 0x12a820) (callEffect (callMemPtr 0x104c1b (.rip 0xff1af)) (0x104c1b + BitVec.ofNat 64 (callMemLen (.rip 0xff1af))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x104c1b (.rip 0xff1af)).toInstrSpec (call_m64_effect_step 0x104c1b (.rip 0xff1af) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c0e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c13) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c18) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c1b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 57), (3, 3), (4, 61), (5, 5), (6, 55), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l104c06 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104c06 :=
  Rest.liftedBlock (rest_l104c06 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104c06 x hx)

theorem rest_l104c21 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104c21 bytes_l104c21) (entryMap (live .l104c21))
      7 0x104c21 bytes_l104c21 b_l104c21 := by
  have f0 : InstrSpec 0x104c21 [0x48, 0xC7, 0x44, 0x24, 0x48, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104c21 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x104c21 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104c21 (.sib 4 none 0 (.d8 0x48)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104c21 (.sib 4 none 0 (.d8 0x48)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104c21 0x48 (by decide) (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x104c2a [0x48, 0xC7, 0x44, 0x24, 0x50, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104c2a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x104c2a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104c2a (.sib 4 none 0 (.d8 0x50)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104c2a (.sib 4 none 0 (.d8 0x50)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104c2a 0x48 (by decide) (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x104c33 [0x48, 0xC7, 0x44, 0x24, 0x58, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104c33 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x104c33 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104c33 (.sib 4 none 0 (.d8 0x58)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104c33 (.sib 4 none 0 (.d8 0x58)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104c33 0x48 (by decide) (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x104c3c [0x48, 0xC7, 0x44, 0x24, 0x60, 0x00, 0x00, 0x00, 0x00] (StorePre 0x104c3c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x104c3c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104c3c (.sib 4 none 0 (.d8 0x60)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x104c3c (.sib 4 none 0 (.d8 0x60)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x104c3c 0x48 (by decide) (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x104c45 [0x48, 0x8D, 0x74, 0x24, 0x48] (fun s => s.RIP = 0x104c45) (leaR64Effect 0x104c45 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x104c45 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x104c45 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104c4a [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x104c4a) (movR64R64Effect 0x104c4a 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104c4a 7 14).toInstrSpec (mov_r64_r64_effect_step 0x104c4a 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104c4d [0xE8, 0xFE, 0x2D, 0x00, 0x00] (PushPre 0x104c4d 5) (callEffect (fun _ => 0x107a50) 0x104c52)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104c4d 0x107a50 0x104c52).toInstrSpec (call_rel32_effect_step 0x104c4d 0x2dfe (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c2a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c33) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c3c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c45) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c4a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c4d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 3), (4, 61), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107a50) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l104c21 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104c21 :=
  Rest.liftedBlock (rest_l104c21 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104c21 x hx)

theorem rest_l104c52 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104c52 bytes_l104c52) (entryMap (live .l104c52))
      16 0x104c52 bytes_l104c52 b_l104c52 := by
  have f0 : InstrSpec 0x104c52 [0x48, 0x8B, 0x44, 0x24, 0x60] (LoadPre 0x104c52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x104c52 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104c52 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104c52 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x104c52 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x104c57 [0x48, 0x89, 0x43, 0x18] (StorePre 0x104c57 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x104c57 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104c57 0 (.base 3 (.d8 0x18)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x104c57 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x104c57 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x104c5b [0x48, 0x8B, 0x44, 0x24, 0x58] (LoadPre 0x104c5b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x104c5b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104c5b 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104c5b 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x104c5b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x104c60 [0x48, 0x89, 0x43, 0x10] (StorePre 0x104c60 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x104c60 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104c60 0 (.base 3 (.d8 0x10)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x104c60 0 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x104c60 0x48 (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x104c64 [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x104c64 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x104c64 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104c64 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x104c64 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x104c64 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x104c69 [0x48, 0x8B, 0x4C, 0x24, 0x50] (LoadPre 0x104c69 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x104c69 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104c69 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x104c69 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x104c69 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x104c6e [0x48, 0x89, 0x4B, 0x08] (StorePre 0x104c6e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x104c6e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104c6e 1 (.base 3 (.d8 0x8)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x104c6e 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x104c6e 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x104c72 [0x48, 0x89, 0x03] (StorePre 0x104c72 3 (fun s => AddrMode.addr (.base 3 .none) s (0x104c72 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x104c72 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x104c72 0 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x104c72 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x104c75 [0x48, 0x81, 0xC4, 0xB8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x104c75) (addR64Imm32Effect 0x104c75 4 0x1b8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x104c75 4 0x1b8).toInstrSpec (add_r64_imm32_effect_step 0x104c75 0x48 0xc4 0x1b8 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x104c7c [0x5B] (PopPre 0x104c7c) (popR64Effect 0x104c7c 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x104c7c 1 3).toInstrSpec (pop_r64_effect_step 0x104c7c 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x104c7d [0x41, 0x5C] (PopPre 0x104c7d) (popR64Effect 0x104c7d 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x104c7d 2 12).toInstrSpec (pop_r64_rex_effect_step 0x104c7d 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x104c7f [0x41, 0x5D] (PopPre 0x104c7f) (popR64Effect 0x104c7f 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x104c7f 2 13).toInstrSpec (pop_r64_rex_effect_step 0x104c7f 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x104c81 [0x41, 0x5E] (PopPre 0x104c81) (popR64Effect 0x104c81 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x104c81 2 14).toInstrSpec (pop_r64_rex_effect_step 0x104c81 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f13 : InstrSpec 0x104c83 [0x41, 0x5F] (PopPre 0x104c83) (popR64Effect 0x104c83 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x104c83 2 15).toInstrSpec (pop_r64_rex_effect_step 0x104c83 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f14 : InstrSpec 0x104c85 [0x5D] (PopPre 0x104c85) (popR64Effect 0x104c85 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x104c85 1 5).toInstrSpec (pop_r64_effect_step 0x104c85 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f15 : InstrSpec 0x104c86 [0xC3] (RetPre 0x104c86) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x104c86).toInstrSpec (ret_effect_step 0x104c86) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c57) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c5b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c60) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c64) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c69) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c6e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c72) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c75) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c7c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 67), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c7d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 67), (4, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c7f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 67), (4, 74), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c81) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 67), (4, 77), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c83) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 80) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 81) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 67), (4, 80), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (15, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c85) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f14 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 67), (4, 83), (5, 82), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (15, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c86) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f15 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 87) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 67), (4, 86), (5, 82), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (15, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) f15 (by decide) rfl rfl rfl (by decide)

theorem block_l104c52 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104c52 :=
  Rest.liftedBlock (rest_l104c52 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104c52 x hx)

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

theorem_by block_l104970_eval :
    program.runBlock (dialect code) ⟨.l104970, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104a00_eval :
    program.runBlock (dialect code) ⟨.l104a00, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104a1e_eval :
    program.runBlock (dialect code) ⟨.l104a1e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104a94_eval :
    program.runBlock (dialect code) ⟨.l104a94, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104ab0_eval :
    program.runBlock (dialect code) ⟨.l104ab0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104ace_eval :
    program.runBlock (dialect code) ⟨.l104ace, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104b63_eval :
    program.runBlock (dialect code) ⟨.l104b63, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104b76_eval :
    program.runBlock (dialect code) ⟨.l104b76, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104ba6_eval :
    program.runBlock (dialect code) ⟨.l104ba6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104bce_eval :
    program.runBlock (dialect code) ⟨.l104bce, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104be6_eval :
    program.runBlock (dialect code) ⟨.l104be6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104c06_eval :
    program.runBlock (dialect code) ⟨.l104c06, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104c21_eval :
    program.runBlock (dialect code) ⟨.l104c21, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104c52_eval :
    program.runBlock (dialect code) ⟨.l104c52, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
