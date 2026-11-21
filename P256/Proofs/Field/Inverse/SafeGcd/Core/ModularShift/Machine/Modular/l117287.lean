import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117287 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1117a7 bytes_l117287) (entryMap (live .l117287))
      14 0x1117a7 bytes_l117287 b_l117287 := by
  have f0 : InstrSpec 0x1117a7 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x1117a7) (leaR64Effect 0x1117a7 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1117a7 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1117a7 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1117ac [0x45, 0x31, 0xE4] (fun s => s.RIP = 0x1117ac) (xorR32R32Effect 0x1117ac 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1117ac 3 12 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x1117ac 0x45 0xe4 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1117af [0x4C, 0x2B, 0x64, 0x24, 0x10] (LoadPre 0x1117af (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1117af + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1117af 12 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 12, .gpr 4] [] [.reg 12, .flags, .rip] :=
    (subR64M64Effect_footprint 0x1117af 12 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x1117af 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1117b4 [0x4D, 0x89, 0xC7] (fun s => s.RIP = 0x1117b4) (movR64R64Effect 0x1117b4 15 8)
      [.gpr 8] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1117b4 15 8).toInstrSpec (mov_r64_r64_effect_step 0x1117b4 0x4d 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1117b7 [0x4D, 0x29, 0xDF] (fun s => s.RIP = 0x1117b7) (subR64R64Effect 0x1117b7 15 11)
      [.gpr 15, .gpr 11] [] [.reg 15, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1117b7 15 11).toInstrSpec (sub_r64_r64_effect_step 0x1117b7 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1117ba [0x49, 0xC1, 0xFC, 0x3F] (fun s => s.RIP = 0x1117ba) (sarR64Effect 0x1117ba 4 12 63)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (sarR64Effect_footprint 0x1117ba 4 12 63).toInstrSpec (sar_r64_imm8_effect_step 0x1117ba 0x49 0xfc 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1117be [0x4D, 0x01, 0xFC] (fun s => s.RIP = 0x1117be) (addR64R64Effect 0x1117be 12 15)
      [.gpr 12, .gpr 15] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1117be 12 15).toInstrSpec (add_r64_r64_effect_step 0x1117be 0x4d 0xfc (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1117c1 [0x49, 0xF7, 0xD0] (fun s => s.RIP = 0x1117c1) (notR64Effect 0x1117c1 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (notR64Effect_footprint 0x1117c1 8).toInstrSpec (not_r64_effect_step 0x1117c1 0x49 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1117c4 [0x4D, 0x89, 0xDF] (fun s => s.RIP = 0x1117c4) (movR64R64Effect 0x1117c4 15 11)
      [.gpr 11] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1117c4 15 11).toInstrSpec (mov_r64_r64_effect_step 0x1117c4 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1117c7 [0x4D, 0x21, 0xC7] (fun s => s.RIP = 0x1117c7) (andR64R64Effect 0x1117c7 15 8)
      [.gpr 15, .gpr 8] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1117c7 15 8).toInstrSpec (and_r64_r64_effect_step 0x1117c7 0x4d 0xc7 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1117ca [0x4D, 0x09, 0xD8] (fun s => s.RIP = 0x1117ca) (orR64R64Effect 0x1117ca 8 11)
      [.gpr 8, .gpr 11] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1117ca 8 11).toInstrSpec (or_r64_r64_effect_step 0x1117ca 0x4d 0xd8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1117cd [0x4D, 0x21, 0xE0] (fun s => s.RIP = 0x1117cd) (andR64R64Effect 0x1117cd 8 12)
      [.gpr 8, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1117cd 8 12).toInstrSpec (and_r64_r64_effect_step 0x1117cd 0x4d 0xe0 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1117d0 [0x4D, 0x09, 0xF8] (fun s => s.RIP = 0x1117d0) (orR64R64Effect 0x1117d0 8 15)
      [.gpr 8, .gpr 15] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1117d0 8 15).toInstrSpec (or_r64_r64_effect_step 0x1117d0 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1117d3 [0x49, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x1117d3) (shrR64Effect 0x1117d3 4 8 63)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x1117d3 4 8 63).toInstrSpec (shr_r64_imm8_effect_step 0x1117d3 0x49 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117ac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (10, 10), (11, 11), (12, 54), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117af) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117b4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117b7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117ba) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (10, 10), (11, 11), (12, 62), (13, 13), (14, 14), (15, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117be) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (10, 10), (11, 11), (12, 64), (13, 13), (14, 14), (15, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117c1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 66), (10, 10), (11, 11), (12, 64), (13, 13), (14, 14), (15, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117c4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 66), (10, 10), (11, 11), (12, 64), (13, 13), (14, 14), (15, 68), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117c7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 66), (10, 10), (11, 11), (12, 64), (13, 13), (14, 14), (15, 70), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117ca) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 72), (10, 10), (11, 11), (12, 64), (13, 13), (14, 14), (15, 70), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117cd) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 74), (10, 10), (11, 11), (12, 64), (13, 13), (14, 14), (15, 70), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117d0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 76), (10, 10), (11, 11), (12, 64), (13, 13), (14, 14), (15, 70), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117d3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 78), (10, 10), (11, 11), (12, 64), (13, 13), (14, 14), (15, 70), (22, 22), (39, 39), (51, 51)]) (p' := 0x1117d7) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 80) (by decide) rfl

theorem block_l117287 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117287 :=
  Rest.liftedBlock (rest_l117287 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117287 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
