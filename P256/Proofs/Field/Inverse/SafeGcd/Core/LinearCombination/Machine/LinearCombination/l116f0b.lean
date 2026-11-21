import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116f0b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11142b bytes_l116f0b) (entryMap (live .l116f0b))
      14 0x11142b bytes_l116f0b b_l116f0b := by
  have f0 : InstrSpec 0x11142b [0x4C, 0x89, 0x0C, 0x24] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11142b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11142b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11142b 9 (.sib 4 none 0 .none))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11142b 9 (.sib 4 none 0 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x11142b 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11142f [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x11142f) (xorR32R32Effect 0x11142f 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11142f 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x11142f 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x111432 [0x4C, 0x2B, 0x0C, 0x24] (LoadPre 0x111432 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111432 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x111432 9 (.sib 4 none 0 .none))
      [.gpr 9, .gpr 4] [] [.reg 9, .flags, .rip] :=
    (subR64M64Effect_footprint 0x111432 9 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x111432 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x111436 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x111436) (movR64R64Effect 0x111436 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x111436 2 12).toInstrSpec (mov_r64_r64_effect_step 0x111436 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x111439 [0x48, 0x29, 0xEA] (fun s => s.RIP = 0x111439) (subR64R64Effect 0x111439 2 5)
      [.gpr 2, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x111439 2 5).toInstrSpec (sub_r64_r64_effect_step 0x111439 0x48 0xea (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11143c [0x49, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x11143c) (sarR64Effect 0x11143c 4 9 63)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (sarR64Effect_footprint 0x11143c 4 9 63).toInstrSpec (sar_r64_imm8_effect_step 0x11143c 0x49 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111440 [0x49, 0x01, 0xD1] (fun s => s.RIP = 0x111440) (addR64R64Effect 0x111440 9 2)
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x111440 9 2).toInstrSpec (add_r64_r64_effect_step 0x111440 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111443 [0x49, 0xF7, 0xD4] (fun s => s.RIP = 0x111443) (notR64Effect 0x111443 12)
      [.gpr 12] [] [.reg 12, .rip] :=
    (notR64Effect_footprint 0x111443 12).toInstrSpec (not_r64_effect_step 0x111443 0x49 0xd4 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111446 [0x48, 0x89, 0xEA] (fun s => s.RIP = 0x111446) (movR64R64Effect 0x111446 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x111446 2 5).toInstrSpec (mov_r64_r64_effect_step 0x111446 0x48 0xea (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x111449 [0x4C, 0x21, 0xE2] (fun s => s.RIP = 0x111449) (andR64R64Effect 0x111449 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111449 2 12).toInstrSpec (and_r64_r64_effect_step 0x111449 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11144c [0x49, 0x09, 0xEC] (fun s => s.RIP = 0x11144c) (orR64R64Effect 0x11144c 12 5)
      [.gpr 12, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11144c 12 5).toInstrSpec (or_r64_r64_effect_step 0x11144c 0x49 0xec (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11144f [0x4D, 0x21, 0xCC] (fun s => s.RIP = 0x11144f) (andR64R64Effect 0x11144f 12 9)
      [.gpr 12, .gpr 9] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11144f 12 9).toInstrSpec (and_r64_r64_effect_step 0x11144f 0x4d 0xcc (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x111452 [0x49, 0x09, 0xD4] (fun s => s.RIP = 0x111452) (orR64R64Effect 0x111452 12 2)
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111452 12 2).toInstrSpec (or_r64_r64_effect_step 0x111452 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111455 [0x49, 0xC1, 0xEC, 0x3F] (fun s => s.RIP = 0x111455) (shrR64Effect 0x111455 4 12 63)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR64Effect_footprint 0x111455 4 12 63).toInstrSpec (shr_r64_imm8_effect_step 0x111455 0x49 0xec 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11142f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 54), (10, 10), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111432) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 56), (10, 10), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111436) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 56), (10, 10), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111439) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 60), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 56), (10, 10), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11143c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 60), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 62), (10, 10), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111440) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 60), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 64), (10, 10), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111443) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 60), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 64), (10, 10), (12, 66), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111446) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 64), (10, 10), (12, 66), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111449) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 64), (10, 10), (12, 66), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11144c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 64), (10, 10), (12, 72), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11144f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 64), (10, 10), (12, 74), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111452) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 64), (10, 10), (12, 76), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111455) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 64), (10, 10), (12, 78), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111459) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 80) (by decide) rfl

theorem block_l116f0b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l116f0b :=
  Rest.liftedBlock (rest_l116f0b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l116f0b x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
