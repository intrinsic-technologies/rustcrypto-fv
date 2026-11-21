import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116f39 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111459 bytes_l116f39) (entryMap (live .l116f39))
      14 0x111459 bytes_l116f39 b_l116f39 := by
  have f0 : InstrSpec 0x111459 [0x4C, 0x89, 0x24, 0x24] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111459 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111459 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111459 12 (.sib 4 none 0 .none))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111459 12 (.sib 4 none 0 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111459 0x4c (by decide) 4 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11145d [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x11145d) (xorR32R32Effect 0x11145d 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11145d 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x11145d 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x111460 [0x4C, 0x2B, 0x14, 0x24] (LoadPre 0x111460 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111460 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x111460 10 (.sib 4 none 0 .none))
      [.gpr 10, .gpr 4] [] [.reg 10, .flags, .rip] :=
    (subR64M64Effect_footprint 0x111460 10 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x111460 0x4c (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x111464 [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x111464) (movR64R64Effect 0x111464 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x111464 2 3).toInstrSpec (mov_r64_r64_effect_step 0x111464 0x48 0xda (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x111467 [0x4C, 0x29, 0xFA] (fun s => s.RIP = 0x111467) (subR64R64Effect 0x111467 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x111467 2 15).toInstrSpec (sub_r64_r64_effect_step 0x111467 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11146a [0x49, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x11146a) (sarR64Effect 0x11146a 4 10 63)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (sarR64Effect_footprint 0x11146a 4 10 63).toInstrSpec (sar_r64_imm8_effect_step 0x11146a 0x49 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11146e [0x49, 0x01, 0xD2] (fun s => s.RIP = 0x11146e) (addR64R64Effect 0x11146e 10 2)
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11146e 10 2).toInstrSpec (add_r64_r64_effect_step 0x11146e 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111471 [0x48, 0xF7, 0xD3] (fun s => s.RIP = 0x111471) (notR64Effect 0x111471 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (notR64Effect_footprint 0x111471 3).toInstrSpec (not_r64_effect_step 0x111471 0x48 0xd3 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111474 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x111474) (movR64R64Effect 0x111474 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x111474 2 15).toInstrSpec (mov_r64_r64_effect_step 0x111474 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x111477 [0x48, 0x21, 0xDA] (fun s => s.RIP = 0x111477) (andR64R64Effect 0x111477 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111477 2 3).toInstrSpec (and_r64_r64_effect_step 0x111477 0x48 0xda (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11147a [0x4C, 0x09, 0xFB] (fun s => s.RIP = 0x11147a) (orR64R64Effect 0x11147a 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11147a 3 15).toInstrSpec (or_r64_r64_effect_step 0x11147a 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11147d [0x4C, 0x21, 0xD3] (fun s => s.RIP = 0x11147d) (andR64R64Effect 0x11147d 3 10)
      [.gpr 3, .gpr 10] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11147d 3 10).toInstrSpec (and_r64_r64_effect_step 0x11147d 0x4c 0xd3 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x111480 [0x48, 0x09, 0xD3] (fun s => s.RIP = 0x111480) (orR64R64Effect 0x111480 3 2)
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111480 3 2).toInstrSpec (or_r64_r64_effect_step 0x111480 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111483 [0x48, 0xC1, 0xEB, 0x3F] (fun s => s.RIP = 0x111483) (shrR64Effect 0x111483 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x111483 4 3 63).toInstrSpec (shr_r64_imm8_effect_step 0x111483 0x48 0xeb 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11145d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 54), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111460) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 56), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111464) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 56), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111467) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 60), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 56), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11146a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 60), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 62), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11146e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 60), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 64), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111471) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 60), (3, 66), (4, 4), (7, 7), (8, 8), (9, 9), (10, 64), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111474) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 66), (4, 4), (7, 7), (8, 8), (9, 9), (10, 64), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111477) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 66), (4, 4), (7, 7), (8, 8), (9, 9), (10, 64), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11147a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 72), (4, 4), (7, 7), (8, 8), (9, 9), (10, 64), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11147d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 74), (4, 4), (7, 7), (8, 8), (9, 9), (10, 64), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111480) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 76), (4, 4), (7, 7), (8, 8), (9, 9), (10, 64), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111483) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 78), (4, 4), (7, 7), (8, 8), (9, 9), (10, 64), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111487) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 80) (by decide) rfl

theorem block_l116f39 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l116f39 :=
  Rest.liftedBlock (rest_l116f39 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l116f39 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
