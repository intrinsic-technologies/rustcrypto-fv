import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Correction.l11821e

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l118251 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112771 bytes_l118251) (entryMap (live .l118251))
      16 0x112771 bytes_l118251 b_l118251 := by
  have f0 : InstrSpec 0x112771 [0x4C, 0x8B, 0x6C, 0x24, 0x08] (LoadPre 0x112771 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112771 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112771 13 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x112771 13 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x112771 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x112776 [0x45, 0x31, 0xFF] (fun s => s.RIP = 0x112776) (xorR32R32Effect 0x112776 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x112776 3 15 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x112776 0x45 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112779 [0x4D, 0x29, 0xEF] (fun s => s.RIP = 0x112779) (subR64R64Effect 0x112779 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (subR64R64Effect_footprint 0x112779 15 13).toInstrSpec (sub_r64_r64_effect_step 0x112779 0x4d 0xef (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11277c [0x48, 0x8B, 0x49, 0x18] (LoadPre 0x11277c (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x11277c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11277c 1 (.base 1 (.d8 0x18)))
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11277c 1 (.base 1 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x11277c 0x48 (by decide) 1 (.base 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x112780 [0x49, 0x89, 0xCD] (fun s => s.RIP = 0x112780) (movR64R64Effect 0x112780 13 1)
      [.gpr 1] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x112780 13 1).toInstrSpec (mov_r64_r64_effect_step 0x112780 0x49 0xcd (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112783 [0x49, 0x29, 0xC5] (fun s => s.RIP = 0x112783) (subR64R64Effect 0x112783 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (subR64R64Effect_footprint 0x112783 13 0).toInstrSpec (sub_r64_r64_effect_step 0x112783 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112786 [0x49, 0xC1, 0xFF, 0x3F] (fun s => s.RIP = 0x112786) (sarR64Effect 0x112786 4 15 63)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (sarR64Effect_footprint 0x112786 4 15 63).toInstrSpec (sar_r64_imm8_effect_step 0x112786 0x49 0xff 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11278a [0x4D, 0x01, 0xEF] (fun s => s.RIP = 0x11278a) (addR64R64Effect 0x11278a 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11278a 15 13).toInstrSpec (add_r64_r64_effect_step 0x11278a 0x4d 0xef (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11278d [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x11278d) (notR64Effect 0x11278d 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x11278d 1).toInstrSpec (not_r64_effect_step 0x11278d 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112790 [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x112790) (movR64R64Effect 0x112790 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x112790 13 0).toInstrSpec (mov_r64_r64_effect_step 0x112790 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x112793 [0x49, 0x21, 0xCD] (fun s => s.RIP = 0x112793) (andR64R64Effect 0x112793 13 1)
      [.gpr 13, .gpr 1] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112793 13 1).toInstrSpec (and_r64_r64_effect_step 0x112793 0x49 0xcd (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x112796 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x112796) (orR64R64Effect 0x112796 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x112796 1 0).toInstrSpec (or_r64_r64_effect_step 0x112796 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x112799 [0x4C, 0x21, 0xF9] (fun s => s.RIP = 0x112799) (andR64R64Effect 0x112799 1 15)
      [.gpr 1, .gpr 15] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112799 1 15).toInstrSpec (and_r64_r64_effect_step 0x112799 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11279c [0x4C, 0x09, 0xE9] (fun s => s.RIP = 0x11279c) (orR64R64Effect 0x11279c 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11279c 1 13).toInstrSpec (or_r64_r64_effect_step 0x11279c 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11279f [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x11279f) (shrR64Effect 0x11279f 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x11279f 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x11279f 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1127a3 [0x48, 0x89, 0x4C, 0x24, 0x08] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1127a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1127a3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1127a3 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1127a3 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1127a3 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112776) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 55), (22, 22), (39, 39), (51, 51)]) (p' := 0x112779) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x11277c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x112780) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 61), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x112783) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 63), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x112786) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 63), (14, 14), (15, 65), (22, 22), (39, 39), (51, 51)]) (p' := 0x11278a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 63), (14, 14), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x11278d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 63), (14, 14), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x112790) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 69), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 71), (14, 14), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x112793) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 69), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 73), (14, 14), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x112796) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 75), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 73), (14, 14), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x112799) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 77), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 73), (14, 14), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x11279c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 73), (14, 14), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x11279f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 81), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 73), (14, 14), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127a3) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 81), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 73), (14, 14), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127a8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 84) (by decide) rfl

theorem block_l118251 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l118251 :=
  Rest.liftedBlock (rest_l118251 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l118251 x hx)

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine
