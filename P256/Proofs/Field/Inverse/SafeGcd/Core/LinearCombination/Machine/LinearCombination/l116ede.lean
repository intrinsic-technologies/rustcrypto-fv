import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116ede [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1113fe bytes_l116ede) (entryMap (live .l116ede))
      14 0x1113fe bytes_l116ede b_l116ede := by
  have f0 : InstrSpec 0x1113fe [0x49, 0x89, 0xE3] (fun s => s.RIP = 0x1113fe) (movR64R64Effect 0x1113fe 11 4)
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1113fe 11 4).toInstrSpec (mov_r64_r64_effect_step 0x1113fe 0x49 0xe3 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x111401 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x111401) (xorR32R32Effect 0x111401 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x111401 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x111401 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x111404 [0x4C, 0x2B, 0x04, 0x24] (LoadPre 0x111404 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111404 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x111404 8 (.sib 4 none 0 .none))
      [.gpr 8, .gpr 4] [] [.reg 8, .flags, .rip] :=
    (subR64M64Effect_footprint 0x111404 8 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x111404 0x4c (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x111408 [0x4C, 0x89, 0xCA] (fun s => s.RIP = 0x111408) (movR64R64Effect 0x111408 2 9)
      [.gpr 9] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x111408 2 9).toInstrSpec (mov_r64_r64_effect_step 0x111408 0x4c 0xca (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11140b [0x4C, 0x29, 0xEA] (fun s => s.RIP = 0x11140b) (subR64R64Effect 0x11140b 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11140b 2 13).toInstrSpec (sub_r64_r64_effect_step 0x11140b 0x4c 0xea (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11140e [0x49, 0xC1, 0xF8, 0x3F] (fun s => s.RIP = 0x11140e) (sarR64Effect 0x11140e 4 8 63)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (sarR64Effect_footprint 0x11140e 4 8 63).toInstrSpec (sar_r64_imm8_effect_step 0x11140e 0x49 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111412 [0x49, 0x01, 0xD0] (fun s => s.RIP = 0x111412) (addR64R64Effect 0x111412 8 2)
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x111412 8 2).toInstrSpec (add_r64_r64_effect_step 0x111412 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111415 [0x49, 0xF7, 0xD1] (fun s => s.RIP = 0x111415) (notR64Effect 0x111415 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (notR64Effect_footprint 0x111415 9).toInstrSpec (not_r64_effect_step 0x111415 0x49 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111418 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x111418) (movR64R64Effect 0x111418 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x111418 2 13).toInstrSpec (mov_r64_r64_effect_step 0x111418 0x4c 0xea (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11141b [0x4C, 0x21, 0xCA] (fun s => s.RIP = 0x11141b) (andR64R64Effect 0x11141b 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11141b 2 9).toInstrSpec (and_r64_r64_effect_step 0x11141b 0x4c 0xca (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11141e [0x4D, 0x09, 0xE9] (fun s => s.RIP = 0x11141e) (orR64R64Effect 0x11141e 9 13)
      [.gpr 9, .gpr 13] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11141e 9 13).toInstrSpec (or_r64_r64_effect_step 0x11141e 0x4d 0xe9 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x111421 [0x4D, 0x21, 0xC1] (fun s => s.RIP = 0x111421) (andR64R64Effect 0x111421 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111421 9 8).toInstrSpec (and_r64_r64_effect_step 0x111421 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x111424 [0x49, 0x09, 0xD1] (fun s => s.RIP = 0x111424) (orR64R64Effect 0x111424 9 2)
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111424 9 2).toInstrSpec (or_r64_r64_effect_step 0x111424 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111427 [0x49, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x111427) (shrR64Effect 0x111427 4 9 63)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x111427 4 9 63).toInstrSpec (shr_r64_imm8_effect_step 0x111427 0x49 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111401) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 54), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111404) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 56), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111408) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (5, 5), (7, 7), (8, 56), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11140b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 60), (3, 3), (4, 4), (5, 5), (7, 7), (8, 56), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11140e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 60), (3, 3), (4, 4), (5, 5), (7, 7), (8, 62), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111412) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 60), (3, 3), (4, 4), (5, 5), (7, 7), (8, 64), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111415) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 60), (3, 3), (4, 4), (5, 5), (7, 7), (8, 64), (9, 66), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111418) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (5, 5), (7, 7), (8, 64), (9, 66), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11141b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 3), (4, 4), (5, 5), (7, 7), (8, 64), (9, 66), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11141e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 3), (4, 4), (5, 5), (7, 7), (8, 64), (9, 72), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111421) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 3), (4, 4), (5, 5), (7, 7), (8, 64), (9, 74), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111424) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 3), (4, 4), (5, 5), (7, 7), (8, 64), (9, 76), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111427) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 3), (4, 4), (5, 5), (7, 7), (8, 64), (9, 78), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11142b) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 80) (by decide) rfl

theorem block_l116ede [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l116ede :=
  Rest.liftedBlock (rest_l116ede code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l116ede x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
