import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1172b7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1117d7 bytes_l1172b7) (entryMap (live .l1172b7))
      14 0x1117d7 bytes_l1172b7 b_l1172b7 := by
  have f0 : InstrSpec 0x1117d7 [0x4C, 0x89, 0x44, 0x24, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1117d7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1117d7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1117d7 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1117d7 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1117d7 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1117dc [0x45, 0x31, 0xDB] (fun s => s.RIP = 0x1117dc) (xorR32R32Effect 0x1117dc 3 11 11)
      [.gpr 11, .gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1117dc 3 11 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x1117dc 0x45 0xdb (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1117df [0x4C, 0x2B, 0x5C, 0x24, 0x10] (LoadPre 0x1117df (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1117df + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1117df 11 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 11, .gpr 4] [] [.reg 11, .flags, .rip] :=
    (subR64M64Effect_footprint 0x1117df 11 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x1117df 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1117e4 [0x49, 0x89, 0xD8] (fun s => s.RIP = 0x1117e4) (movR64R64Effect 0x1117e4 8 3)
      [.gpr 3] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1117e4 8 3).toInstrSpec (mov_r64_r64_effect_step 0x1117e4 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1117e7 [0x4D, 0x29, 0xD0] (fun s => s.RIP = 0x1117e7) (subR64R64Effect 0x1117e7 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1117e7 8 10).toInstrSpec (sub_r64_r64_effect_step 0x1117e7 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1117ea [0x49, 0xC1, 0xFB, 0x3F] (fun s => s.RIP = 0x1117ea) (sarR64Effect 0x1117ea 4 11 63)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (sarR64Effect_footprint 0x1117ea 4 11 63).toInstrSpec (sar_r64_imm8_effect_step 0x1117ea 0x49 0xfb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1117ee [0x4D, 0x01, 0xC3] (fun s => s.RIP = 0x1117ee) (addR64R64Effect 0x1117ee 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1117ee 11 8).toInstrSpec (add_r64_r64_effect_step 0x1117ee 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1117f1 [0x48, 0xF7, 0xD3] (fun s => s.RIP = 0x1117f1) (notR64Effect 0x1117f1 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (notR64Effect_footprint 0x1117f1 3).toInstrSpec (not_r64_effect_step 0x1117f1 0x48 0xd3 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1117f4 [0x4D, 0x89, 0xD0] (fun s => s.RIP = 0x1117f4) (movR64R64Effect 0x1117f4 8 10)
      [.gpr 10] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1117f4 8 10).toInstrSpec (mov_r64_r64_effect_step 0x1117f4 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1117f7 [0x49, 0x21, 0xD8] (fun s => s.RIP = 0x1117f7) (andR64R64Effect 0x1117f7 8 3)
      [.gpr 8, .gpr 3] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1117f7 8 3).toInstrSpec (and_r64_r64_effect_step 0x1117f7 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1117fa [0x4C, 0x09, 0xD3] (fun s => s.RIP = 0x1117fa) (orR64R64Effect 0x1117fa 3 10)
      [.gpr 3, .gpr 10] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1117fa 3 10).toInstrSpec (or_r64_r64_effect_step 0x1117fa 0x4c 0xd3 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1117fd [0x4C, 0x21, 0xDB] (fun s => s.RIP = 0x1117fd) (andR64R64Effect 0x1117fd 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1117fd 3 11).toInstrSpec (and_r64_r64_effect_step 0x1117fd 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x111800 [0x4C, 0x09, 0xC3] (fun s => s.RIP = 0x111800) (orR64R64Effect 0x111800 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111800 3 8).toInstrSpec (or_r64_r64_effect_step 0x111800 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111803 [0x48, 0xC1, 0xEB, 0x3F] (fun s => s.RIP = 0x111803) (shrR64Effect 0x111803 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x111803 4 3 63).toInstrSpec (shr_r64_imm8_effect_step 0x111803 0x48 0xeb 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117dc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (10, 10), (11, 54), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117df) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (10, 10), (11, 56), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117e4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 58), (10, 10), (11, 56), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117e7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 60), (10, 10), (11, 56), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117ea) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 60), (10, 10), (11, 62), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117ee) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 60), (10, 10), (11, 64), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117f1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 66), (4, 4), (5, 5), (7, 7), (8, 60), (10, 10), (11, 64), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117f4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 66), (4, 4), (5, 5), (7, 7), (8, 68), (10, 10), (11, 64), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117f7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 66), (4, 4), (5, 5), (7, 7), (8, 70), (10, 10), (11, 64), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117fa) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 72), (4, 4), (5, 5), (7, 7), (8, 70), (10, 10), (11, 64), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117fd) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 74), (4, 4), (5, 5), (7, 7), (8, 70), (10, 10), (11, 64), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111800) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 76), (4, 4), (5, 5), (7, 7), (8, 70), (10, 10), (11, 64), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111803) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 78), (4, 4), (5, 5), (7, 7), (8, 70), (10, 10), (11, 64), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111807) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 80) (by decide) rfl

theorem block_l1172b7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1172b7 :=
  Rest.liftedBlock (rest_l1172b7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1172b7 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
