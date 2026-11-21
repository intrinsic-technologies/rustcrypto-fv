import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117b83 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1120a3 bytes_l117b83) (entryMap (live .l117b83))
      18 0x1120a3 bytes_l117b83 b_l117b83 := by
  have f0 : InstrSpec 0x1120a3 [0x49, 0x31, 0xFA] (fun s => s.RIP = 0x1120a3) (xorR64R64Effect 0x1120a3 10 7)
      [.gpr 10, .gpr 7] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1120a3 10 7).toInstrSpec (xor_r64_r64_effect_step 0x1120a3 0x49 0xfa (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1120a6 [0x44, 0x88, 0x44, 0x24, 0x08] (StorePre 0x1120a6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1120a6 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1120a6 5 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1120a6 5 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1120a6 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1120ab [0x0F, 0xB6, 0x7C, 0x24, 0x08] (LoadPre 0x1120ab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1120ab + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1120ab 5 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1120ab 5 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x1120ab 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1120b0 [0x48, 0xF7, 0xDF] (fun s => s.RIP = 0x1120b0) (negR64Effect 0x1120b0 7)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (negR64Effect_footprint 0x1120b0 7).toInstrSpec (neg_r64_effect_step 0x1120b0 0x48 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1120b3 [0x4C, 0x21, 0xD7] (fun s => s.RIP = 0x1120b3) (andR64R64Effect 0x1120b3 7 10)
      [.gpr 7, .gpr 10] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1120b3 7 10).toInstrSpec (and_r64_r64_effect_step 0x1120b3 0x4c 0xd7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1120b6 [0x49, 0x01, 0xFE] (fun s => s.RIP = 0x1120b6) (addR64R64Effect 0x1120b6 14 7)
      [.gpr 14, .gpr 7] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1120b6 14 7).toInstrSpec (add_r64_r64_effect_step 0x1120b6 0x49 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1120b9 [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x1120b9) (movR64R64Effect 0x1120b9 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1120b9 7 6).toInstrSpec (mov_r64_r64_effect_step 0x1120b9 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1120bc [0x48, 0xF7, 0xDF] (fun s => s.RIP = 0x1120bc) (negR64Effect 0x1120bc 7)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (negR64Effect_footprint 0x1120bc 7).toInstrSpec (neg_r64_effect_step 0x1120bc 0x48 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1120bf [0x44, 0x88, 0x4C, 0x24, 0x08] (StorePre 0x1120bf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1120bf + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1120bf 5 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1120bf 5 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1120bf 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1120c4 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x08] (LoadPre 0x1120c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1120c4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1120c4 6 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x1120c4 6 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1120c4 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1120ca [0x49, 0xF7, 0xD9] (fun s => s.RIP = 0x1120ca) (negR64Effect 0x1120ca 9)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (negR64Effect_footprint 0x1120ca 9).toInstrSpec (neg_r64_effect_step 0x1120ca 0x49 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1120cd [0x48, 0x31, 0xF7] (fun s => s.RIP = 0x1120cd) (xorR64R64Effect 0x1120cd 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1120cd 7 6).toInstrSpec (xor_r64_r64_effect_step 0x1120cd 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1120d0 [0x4C, 0x21, 0xCF] (fun s => s.RIP = 0x1120d0) (andR64R64Effect 0x1120d0 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1120d0 7 9).toInstrSpec (and_r64_r64_effect_step 0x1120d0 0x4c 0xcf (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1120d3 [0x48, 0x31, 0xF3] (fun s => s.RIP = 0x1120d3) (xorR64R64Effect 0x1120d3 3 6)
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1120d3 3 6).toInstrSpec (xor_r64_r64_effect_step 0x1120d3 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1120d6 [0x48, 0x31, 0xF7] (fun s => s.RIP = 0x1120d6) (xorR64R64Effect 0x1120d6 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1120d6 7 6).toInstrSpec (xor_r64_r64_effect_step 0x1120d6 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1120d9 [0x48, 0xD1, 0xF8] (fun s => s.RIP = 0x1120d9) (sarR64Effect 0x1120d9 3 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (sarR64Effect_footprint 0x1120d9 3 0 1).toInstrSpec (sar_r64_one_effect_step 0x1120d9 0x48 0xf8 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1120dc [0x4D, 0x01, 0xFF] (fun s => s.RIP = 0x1120dc) (addR64R64Effect 0x1120dc 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1120dc 15 15).toInstrSpec (add_r64_r64_effect_step 0x1120dc 0x4d 0xff (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1120df [0x48, 0x01, 0xDB] (fun s => s.RIP = 0x1120df) (addR64R64Effect 0x1120df 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1120df 3 3).toInstrSpec (add_r64_r64_effect_step 0x1120df 0x48 0xdb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120a6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120ab) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 56), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120b0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 58), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120b3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 60), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120b6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 60), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120b9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 64), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120bc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 66), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120bf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 66), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120c4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 66), (8, 8), (9, 69), (10, 53), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120ca) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 66), (8, 8), (9, 71), (10, 53), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120cd) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 73), (8, 8), (9, 71), (10, 53), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120d0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 75), (8, 8), (9, 71), (10, 53), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120d3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 77), (4, 4), (5, 5), (6, 6), (7, 75), (8, 8), (9, 71), (10, 53), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120d6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 77), (4, 4), (5, 5), (6, 6), (7, 79), (8, 8), (9, 71), (10, 53), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120d9) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 77), (4, 4), (5, 5), (6, 6), (7, 79), (8, 8), (9, 71), (10, 53), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120dc) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 77), (4, 4), (5, 5), (6, 6), (7, 79), (8, 8), (9, 71), (10, 53), (11, 11), (12, 12), (13, 13), (14, 62), (15, 83), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120df) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 85), (4, 4), (5, 5), (6, 6), (7, 79), (8, 8), (9, 71), (10, 53), (11, 11), (12, 12), (13, 13), (14, 62), (15, 83), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120e2) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 87) (by decide) rfl

theorem block_l117b83 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117b83 :=
  Rest.liftedBlock (rest_l117b83 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117b83 x hx)

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

theorem_by block_l117b83_eval :
    program.runBlock (dialect code) ⟨.l117b83, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
