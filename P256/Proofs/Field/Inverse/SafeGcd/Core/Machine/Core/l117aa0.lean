import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Core.l117aa0_1
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117aa0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111fc0 bytes_l117aa0) (entryMap (live .l117aa0))
      25 0x111fc0 bytes_l117aa0 b_l117aa0 := by
  have f0 : InstrSpec 0x111fc0 [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x111fc0) (movR64R64Effect 0x111fc0 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x111fc0 11 2).toInstrSpec (mov_r64_r64_effect_step 0x111fc0 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x111fc3 [0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x111fc3) (movR64Imm64Effect 0x111fc3 2 0x7fffffffffffffff)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x111fc3 2 0x7fffffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x111fc3 0x48 0xba (by decide) (by decide) 0x7fffffffffffffff) pre_rip
  have f2 : InstrSpec 0x111fcd [0x4C, 0x8D, 0x4A, 0x01] (fun s => s.RIP = 0x111fcd) (leaR64Effect 0x111fcd 9 (.base 2 (.d8 0x1)))
      [.gpr 2] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x111fcd 9 (.base 2 (.d8 0x1))).toInstrSpec (lea_r64_effect_step 0x111fcd 0x4c (by decide) 1 (.base 2 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x111fd1 [0x48, 0x89, 0xEA] (fun s => s.RIP = 0x111fd1) (movR64R64Effect 0x111fd1 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x111fd1 2 5).toInstrSpec (mov_r64_r64_effect_step 0x111fd1 0x48 0xea (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x111fd4 [0x4C, 0x31, 0xCA] (fun s => s.RIP = 0x111fd4) (xorR64R64Effect 0x111fd4 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111fd4 2 9).toInstrSpec (xor_r64_r64_effect_step 0x111fd4 0x4c 0xca (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x111fd7 [0x49, 0x29, 0xD1] (fun s => s.RIP = 0x111fd7) (subR64R64Effect 0x111fd7 9 2)
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x111fd7 9 2).toInstrSpec (sub_r64_r64_effect_step 0x111fd7 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111fda [0x49, 0x21, 0xD1] (fun s => s.RIP = 0x111fda) (andR64R64Effect 0x111fda 9 2)
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111fda 9 2).toInstrSpec (and_r64_r64_effect_step 0x111fda 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111fdd [0x49, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x111fdd) (shrR64Effect 0x111fdd 4 9 63)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x111fdd 4 9 63).toInstrSpec (shr_r64_imm8_effect_step 0x111fdd 0x49 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111fe1 [0x41, 0x89, 0xC0] (fun s => s.RIP = 0x111fe1) (movR32R32Effect 0x111fe1 3 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x111fe1 3 8 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x111fe1 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x111fe4 [0x41, 0x80, 0xE0, 0x01] (fun s => s.RIP = 0x111fe4) (andR8Imm8Effect 0x111fe4 4 8 0x1)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x111fe4 4 8 0x1).toInstrSpec (and_r8_imm8_rex_effect_step 0x111fe4 0x41 0xe0 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x111fe8 [0x44, 0x88, 0x44, 0x24, 0x08] (StorePre 0x111fe8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111fe8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x111fe8 5 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111fe8 5 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x111fe8 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x111fed [0x0F, 0xB6, 0x5C, 0x24, 0x08] (LoadPre 0x111fed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111fed + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111fed 5 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M8Effect_footprint 0x111fed 5 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x111fed 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x111ff2 [0x48, 0xF7, 0xDB] (fun s => s.RIP = 0x111ff2) (negR64Effect 0x111ff2 3)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (negR64Effect_footprint 0x111ff2 3).toInstrSpec (neg_r64_effect_step 0x111ff2 0x48 0xdb (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111ff5 [0x4C, 0x21, 0xDB] (fun s => s.RIP = 0x111ff5) (andR64R64Effect 0x111ff5 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111ff5 3 11).toInstrSpec (and_r64_r64_effect_step 0x111ff5 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x111ff8 [0x45, 0x89, 0xCA] (fun s => s.RIP = 0x111ff8) (movR32R32Effect 0x111ff8 3 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x111ff8 3 10 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x111ff8 0x45 0xca (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x111ffb [0x41, 0x20, 0xC2] (fun s => s.RIP = 0x111ffb) (andR8R8Effect 0x111ffb 3 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (andR8R8Effect_footprint 0x111ffb 3 10 0).toInstrSpec (and_r8_r8_rex_effect_step 0x111ffb 0x41 0xc2 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x111ffe [0xBA, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x111ffe) (movR32Imm32Effect 0x111ffe 5 2 0x2)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x111ffe 5 2 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x111ffe 0xba (by decide) 0x2) pre_rip
  have f17 : InstrSpec 0x112003 [0x48, 0x29, 0xEA] (fun s => s.RIP = 0x112003) (subR64R64Effect 0x112003 2 5)
      [.gpr 2, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x112003 2 5).toInstrSpec (sub_r64_r64_effect_step 0x112003 0x48 0xea (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x112006 [0x48, 0x83, 0xC5, 0x02] (fun s => s.RIP = 0x112006) (addR64Imm8Effect 0x112006 5 0x2)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x112006 5 0x2).toInstrSpec (add_r64_imm8_effect_step 0x112006 0x48 0xc5 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11200a [0x44, 0x88, 0x54, 0x24, 0x08] (StorePre 0x11200a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11200a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11200a 5 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11200a 5 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11200a 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fc3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fcd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (9, 57), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fd1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (9, 57), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fd4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7), (9, 57), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fd7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7), (9, 63), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fda) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7), (9, 65), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fdd) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7), (9, 67), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fe1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7), (8, 69), (9, 67), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fe4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 67), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fe8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 67), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111fed) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 74), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 67), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ff2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 76), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 67), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ff5) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 78), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 67), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ff8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 78), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 67), (10, 80), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ffb) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 78), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 67), (10, 82), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ffe) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 1), (2, 84), (3, 78), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 67), (10, 82), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x112003) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 1), (2, 86), (3, 78), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 67), (10, 82), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x112006) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 1), (2, 86), (3, 78), (4, 4), (5, 88), (6, 6), (7, 7), (8, 71), (9, 67), (10, 82), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11200a) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 86), (3, 78), (4, 4), (5, 88), (6, 6), (7, 7), (8, 71), (9, 67), (10, 82), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11200f) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l117aa0_1 code

theorem block_l117aa0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117aa0 :=
  Rest.liftedBlock (rest_l117aa0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117aa0 x hx)

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

theorem_by block_l117aa0_eval :
    program.runBlock (dialect code) ⟨.l117aa0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
