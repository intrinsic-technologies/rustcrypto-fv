import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116eb9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1113d9 bytes_l116eb9) (entryMap (live .l116eb9))
      11 0x1113d9 bytes_l116eb9 b_l116eb9 := by
  have f0 : InstrSpec 0x1113d9 [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x1113d9) (movR64R64Effect 0x1113d9 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1113d9 0 10).toInstrSpec (mov_r64_r64_effect_step 0x1113d9 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1113dc [0x48, 0x29, 0xF0] (fun s => s.RIP = 0x1113dc) (subR64R64Effect 0x1113dc 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1113dc 0 6).toInstrSpec (sub_r64_r64_effect_step 0x1113dc 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1113df [0x49, 0xF7, 0xD2] (fun s => s.RIP = 0x1113df) (notR64Effect 0x1113df 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (notR64Effect_footprint 0x1113df 10).toInstrSpec (not_r64_effect_step 0x1113df 0x49 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1113e2 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x1113e2) (movR64R64Effect 0x1113e2 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1113e2 2 6).toInstrSpec (mov_r64_r64_effect_step 0x1113e2 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1113e5 [0x4C, 0x21, 0xD2] (fun s => s.RIP = 0x1113e5) (andR64R64Effect 0x1113e5 2 10)
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1113e5 2 10).toInstrSpec (and_r64_r64_effect_step 0x1113e5 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1113e8 [0x49, 0x09, 0xF2] (fun s => s.RIP = 0x1113e8) (orR64R64Effect 0x1113e8 10 6)
      [.gpr 10, .gpr 6] [] [.reg 10, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1113e8 10 6).toInstrSpec (or_r64_r64_effect_step 0x1113e8 0x49 0xf2 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1113eb [0x49, 0x21, 0xC2] (fun s => s.RIP = 0x1113eb) (andR64R64Effect 0x1113eb 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1113eb 10 0).toInstrSpec (and_r64_r64_effect_step 0x1113eb 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1113ee [0x49, 0x09, 0xD2] (fun s => s.RIP = 0x1113ee) (orR64R64Effect 0x1113ee 10 2)
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1113ee 10 2).toInstrSpec (or_r64_r64_effect_step 0x1113ee 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1113f1 [0x49, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x1113f1) (shrR64Effect 0x1113f1 4 10 63)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x1113f1 4 10 63).toInstrSpec (shr_r64_imm8_effect_step 0x1113f1 0x49 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1113f5 [0x44, 0x0F, 0xB6, 0x34, 0x24] (LoadPre 0x1113f5 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1113f5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1113f5 5 14 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x1113f5 5 14 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1113f5 0x44 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1113fa [0x4C, 0x89, 0x14, 0x24] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1113fa 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1113fa + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1113fa 10 (.sib 4 none 0 .none))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1113fa 10 (.sib 4 none 0 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1113fa 0x4c (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113dc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113df) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 57), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113e2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 57), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113e5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 57), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113e8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 63), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113eb) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113ee) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113f1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 69), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113f5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 69), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113fa) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 69), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1113fe) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 74) (by decide) rfl

theorem block_l116eb9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l116eb9 :=
  Rest.liftedBlock (rest_l116eb9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l116eb9 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
