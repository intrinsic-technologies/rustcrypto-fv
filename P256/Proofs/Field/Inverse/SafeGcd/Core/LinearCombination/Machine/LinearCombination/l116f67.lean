import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.LinearCombination.l116f67_1
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116f67 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111487 bytes_l116f67) (entryMap (live .l116f67))
      25 0x111487 bytes_l116f67 b_l116f67 := by
  have f0 : InstrSpec 0x111487 [0x48, 0x89, 0x1C, 0x24] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111487 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111487 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111487 3 (.sib 4 none 0 .none))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111487 3 (.sib 4 none 0 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111487 0x48 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11148b [0x31, 0xDB] (fun s => s.RIP = 0x11148b) (xorR32R32Effect 0x11148b 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11148b 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x11148b 0xdb (by decide)) pre_rip
  have f2 : InstrSpec 0x11148d [0x48, 0x2B, 0x1C, 0x24] (LoadPre 0x11148d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11148d + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x11148d 3 (.sib 4 none 0 .none))
      [.gpr 3, .gpr 4] [] [.reg 3, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11148d 3 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x11148d 0x48 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x111491 [0x4C, 0x8B, 0x5C, 0x24, 0x38] (LoadPre 0x111491 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x111491 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111491 11 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x111491 11 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x111491 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x111496 [0x41, 0x83, 0xE3, 0x01] (fun s => s.RIP = 0x111496) (andR32Imm8Effect 0x111496 4 11 0x1)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x111496 4 11 0x1).toInstrSpec (and_r32_imm8_rex_effect_step 0x111496 0x41 0xe3 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11149a [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x11149a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11149a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11149a 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11149a 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11149a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x11149f [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x11149f) (movR64R64Effect 0x11149f 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11149f 2 6).toInstrSpec (mov_r64_r64_effect_step 0x11149f 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1114a2 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x1114a2) (notR64Effect 0x1114a2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x1114a2 2).toInstrSpec (not_r64_effect_step 0x1114a2 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1114a5 [0x4C, 0x01, 0xDA] (fun s => s.RIP = 0x1114a5) (addR64R64Effect 0x1114a5 2 11)
      [.gpr 2, .gpr 11] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1114a5 2 11).toInstrSpec (add_r64_r64_effect_step 0x1114a5 0x4c 0xda (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1114a8 [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x1114a8) (xorR64R64Effect 0x1114a8 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1114a8 2 6).toInstrSpec (xor_r64_r64_effect_step 0x1114a8 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1114ab [0x49, 0xF7, 0xDE] (fun s => s.RIP = 0x1114ab) (negR64Effect 0x1114ab 14)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (negR64Effect_footprint 0x1114ab 14).toInstrSpec (neg_r64_effect_step 0x1114ab 0x49 0xde (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1114ae [0x49, 0x21, 0xD6] (fun s => s.RIP = 0x1114ae) (andR64R64Effect 0x1114ae 14 2)
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1114ae 14 2).toInstrSpec (and_r64_r64_effect_step 0x1114ae 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1114b1 [0x49, 0x31, 0xF6] (fun s => s.RIP = 0x1114b1) (xorR64R64Effect 0x1114b1 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1114b1 14 6).toInstrSpec (xor_r64_r64_effect_step 0x1114b1 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1114b4 [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x1114b4) (movR64R64Effect 0x1114b4 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1114b4 2 1).toInstrSpec (mov_r64_r64_effect_step 0x1114b4 0x48 0xca (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1114b7 [0x4C, 0x29, 0xF2] (fun s => s.RIP = 0x1114b7) (subR64R64Effect 0x1114b7 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1114b7 2 14).toInstrSpec (sub_r64_r64_effect_step 0x1114b7 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1114ba [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x1114ba) (notR64Effect 0x1114ba 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x1114ba 1).toInstrSpec (not_r64_effect_step 0x1114ba 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1114bd [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1114bd) (movR64R64Effect 0x1114bd 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1114bd 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1114bd 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1114c0 [0x48, 0x21, 0xCE] (fun s => s.RIP = 0x1114c0) (andR64R64Effect 0x1114c0 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1114c0 6 1).toInstrSpec (and_r64_r64_effect_step 0x1114c0 0x48 0xce (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1114c3 [0x4C, 0x09, 0xF1] (fun s => s.RIP = 0x1114c3) (orR64R64Effect 0x1114c3 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1114c3 1 14).toInstrSpec (or_r64_r64_effect_step 0x1114c3 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1114c6 [0x48, 0xC1, 0xFB, 0x3F] (fun s => s.RIP = 0x1114c6) (sarR64Effect 0x1114c6 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (sarR64Effect_footprint 0x1114c6 4 3 63).toInstrSpec (sar_r64_imm8_effect_step 0x1114c6 0x48 0xfb 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11148b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 54), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11148d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (3, 56), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111491) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (3, 56), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 58), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111496) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (3, 56), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11149a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (3, 56), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11149f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 64), (3, 56), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114a2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 66), (3, 56), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114a5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 56), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114a8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 56), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114ab) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 56), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 72), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114ae) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 56), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 74), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114b1) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 56), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114b4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 78), (3, 56), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114b7) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 80), (3, 56), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114ba) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 82), (2, 80), (3, 56), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114bd) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 82), (2, 80), (3, 56), (4, 4), (6, 84), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114c0) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 82), (2, 80), (3, 56), (4, 4), (6, 86), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114c3) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 88), (2, 80), (3, 56), (4, 4), (6, 86), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114c6) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 88), (2, 80), (3, 90), (4, 4), (6, 86), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114ca) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l116f67_1 code

theorem block_l116f67 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l116f67 :=
  Rest.liftedBlock (rest_l116f67 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l116f67 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
