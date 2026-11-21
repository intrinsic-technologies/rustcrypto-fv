import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117b01 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112021 bytes_l117b01) (entryMap (live .l117b01))
      18 0x112021 bytes_l117b01 b_l117b01 := by
  have f0 : InstrSpec 0x112021 [0x44, 0x88, 0x54, 0x24, 0x08] (StorePre 0x112021 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112021 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x112021 5 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x112021 5 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x112021 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x112026 [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x08] (LoadPre 0x112026 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112026 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x112026 6 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x112026 6 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x112026 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11202c [0x49, 0xF7, 0xDF] (fun s => s.RIP = 0x11202c) (negR64Effect 0x11202c 15)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (negR64Effect_footprint 0x11202c 15).toInstrSpec (neg_r64_effect_step 0x11202c 0x49 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11202f [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x11202f) (movR64R64Effect 0x11202f 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11202f 2 0).toInstrSpec (mov_r64_r64_effect_step 0x11202f 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x112032 [0x4C, 0x31, 0xDA] (fun s => s.RIP = 0x112032) (xorR64R64Effect 0x112032 2 11)
      [.gpr 2, .gpr 11] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x112032 2 11).toInstrSpec (xor_r64_r64_effect_step 0x112032 0x4c 0xda (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112035 [0x4C, 0x21, 0xFA] (fun s => s.RIP = 0x112035) (andR64R64Effect 0x112035 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112035 2 15).toInstrSpec (and_r64_r64_effect_step 0x112035 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112038 [0x4C, 0x31, 0xDA] (fun s => s.RIP = 0x112038) (xorR64R64Effect 0x112038 2 11)
      [.gpr 2, .gpr 11] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x112038 2 11).toInstrSpec (xor_r64_r64_effect_step 0x112038 0x4c 0xda (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11203b [0x4C, 0x8D, 0x1C, 0x03] (fun s => s.RIP = 0x11203b) (leaR64Effect 0x11203b 11 (.sib 3 (some 0) 0 .none))
      [.gpr 3, .gpr 0] [] [.reg 11, .rip] :=
    (leaR64Effect_footprint 0x11203b 11 (.sib 3 (some 0) 0 .none)).toInstrSpec (lea_r64_effect_step 0x11203b 0x4c (by decide) 3 (.sib 3 (some 0) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11203f [0x48, 0x29, 0xD8] (fun s => s.RIP = 0x11203f) (subR64R64Effect 0x11203f 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11203f 0 3).toInstrSpec (sub_r64_r64_effect_step 0x11203f 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112042 [0x44, 0x88, 0x54, 0x24, 0x08] (StorePre 0x112042 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112042 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x112042 5 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x112042 5 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x112042 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x112047 [0x0F, 0xB6, 0x5C, 0x24, 0x08] (LoadPre 0x112047 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112047 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x112047 5 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x112047 5 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x112047 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x11204c [0x48, 0xF7, 0xDB] (fun s => s.RIP = 0x11204c) (negR64Effect 0x11204c 3)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (negR64Effect_footprint 0x11204c 3).toInstrSpec (neg_r64_effect_step 0x11204c 0x48 0xdb (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11204f [0x4C, 0x31, 0xD8] (fun s => s.RIP = 0x11204f) (xorR64R64Effect 0x11204f 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x11204f 0 11).toInstrSpec (xor_r64_r64_effect_step 0x11204f 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x112052 [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x112052) (andR64R64Effect 0x112052 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112052 0 3).toInstrSpec (and_r64_r64_effect_step 0x112052 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x112055 [0x4C, 0x31, 0xD8] (fun s => s.RIP = 0x112055) (xorR64R64Effect 0x112055 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x112055 0 11).toInstrSpec (xor_r64_r64_effect_step 0x112055 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x112058 [0x44, 0x88, 0x54, 0x24, 0x08] (StorePre 0x112058 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112058 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x112058 5 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x112058 5 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x112058 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x11205d [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x08] (LoadPre 0x11205d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11205d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x11205d 6 11 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x11205d 6 11 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x11205d 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x112063 [0x49, 0xF7, 0xDB] (fun s => s.RIP = 0x112063) (negR64Effect 0x112063 11)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (negR64Effect_footprint 0x112063 11).toInstrSpec (neg_r64_effect_step 0x112063 0x49 0xdb (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x112026) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 54), (22, 22), (39, 39), (51, 51)]) (p' := 0x11202c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x11202f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x112032) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 60), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x112035) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x112038) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x11203b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x11203f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 1), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x112042) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 1), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x112047) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 68), (1, 1), (2, 64), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x11204c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 68), (1, 1), (2, 64), (3, 73), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x11204f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 1), (2, 64), (3, 73), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x112052) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 1), (2, 64), (3, 73), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x112055) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 1), (2, 64), (3, 73), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x112058) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 1), (2, 64), (3, 73), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 66), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x11205d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 79), (1, 1), (2, 64), (3, 73), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 82), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x112063) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 79), (1, 1), (2, 64), (3, 73), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 84), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x112066) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 86) (by decide) rfl

theorem block_l117b01 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117b01 :=
  Rest.liftedBlock (rest_l117b01 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117b01 x hx)

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

theorem_by block_l117b01_eval :
    program.runBlock (dialect code) ⟨.l117b01, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
