import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117256 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111776 bytes_l117256) (entryMap (live .l117256))
      13 0x111776 bytes_l117256 b_l117256 := by
  have f0 : InstrSpec 0x111776 [0x48, 0x89, 0xF5] (fun s => s.RIP = 0x111776) (movR64R64Effect 0x111776 5 6)
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x111776 5 6).toInstrSpec (mov_r64_r64_effect_step 0x111776 0x48 0xf5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x111779 [0x4C, 0x29, 0xF5] (fun s => s.RIP = 0x111779) (subR64R64Effect 0x111779 5 14)
      [.gpr 5, .gpr 14] [] [.reg 5, .flags, .rip] :=
    (subR64R64Effect_footprint 0x111779 5 14).toInstrSpec (sub_r64_r64_effect_step 0x111779 0x4c 0xf5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11177c [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x11177c) (notR64Effect 0x11177c 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x11177c 6).toInstrSpec (not_r64_effect_step 0x11177c 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11177f [0x4D, 0x89, 0xF7] (fun s => s.RIP = 0x11177f) (movR64R64Effect 0x11177f 15 14)
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x11177f 15 14).toInstrSpec (mov_r64_r64_effect_step 0x11177f 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x111782 [0x49, 0x21, 0xF7] (fun s => s.RIP = 0x111782) (andR64R64Effect 0x111782 15 6)
      [.gpr 15, .gpr 6] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111782 15 6).toInstrSpec (and_r64_r64_effect_step 0x111782 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x111785 [0x4C, 0x09, 0xF6] (fun s => s.RIP = 0x111785) (orR64R64Effect 0x111785 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111785 6 14).toInstrSpec (or_r64_r64_effect_step 0x111785 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111788 [0x4C, 0x8B, 0x74, 0x24, 0x30] (LoadPre 0x111788 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x111788 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111788 14 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x111788 14 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x111788 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x11178d [0x48, 0x21, 0xEE] (fun s => s.RIP = 0x11178d) (andR64R64Effect 0x11178d 6 5)
      [.gpr 6, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11178d 6 5).toInstrSpec (and_r64_r64_effect_step 0x11178d 0x48 0xee (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111790 [0x4C, 0x09, 0xFE] (fun s => s.RIP = 0x111790) (orR64R64Effect 0x111790 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111790 6 15).toInstrSpec (or_r64_r64_effect_step 0x111790 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x111793 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x38] (LoadPre 0x111793 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x111793 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x111793 6 9 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x111793 6 9 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x111793 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x111799 [0x44, 0x88, 0x4C, 0x24, 0x0F] (StorePre 0x111799 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x111799 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x111799 5 9 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111799 5 9 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_rex_effect_step 0x111799 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x11179e [0x48, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x11179e) (shrR64Effect 0x11179e 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x11179e 4 6 63).toInstrSpec (shr_r64_imm8_effect_step 0x11179e 0x48 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1117a2 [0x48, 0x89, 0x74, 0x24, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1117a2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1117a2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1117a2 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1117a2 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1117a2 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111779) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11177c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 57), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11177f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 57), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (51, 51)]) (p' := 0x111782) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 57), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x111785) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 63), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x111788) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 63), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x11178d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 67), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x111790) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 69), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x111793) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 69), (7, 7), (8, 8), (9, 71), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x111799) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 69), (7, 7), (8, 8), (9, 71), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x11179e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 74), (7, 7), (8, 8), (9, 71), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117a2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 74), (7, 7), (8, 8), (9, 71), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117a7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l117256 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117256 :=
  Rest.liftedBlock (rest_l117256 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117256 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
