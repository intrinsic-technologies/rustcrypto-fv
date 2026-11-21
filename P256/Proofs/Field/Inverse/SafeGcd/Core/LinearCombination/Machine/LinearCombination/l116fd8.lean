import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116fd8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1114f8 bytes_l116fd8) (entryMap (live .l116fd8))
      14 0x1114f8 bytes_l116fd8 b_l116fd8 := by
  have f0 : InstrSpec 0x1114f8 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x1114f8) (movR64R64Effect 0x1114f8 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1114f8 12 0).toInstrSpec (mov_r64_r64_effect_step 0x1114f8 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1114fb [0x49, 0xF7, 0xDC] (fun s => s.RIP = 0x1114fb) (negR64Effect 0x1114fb 12)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (negR64Effect_footprint 0x1114fb 12).toInstrSpec (neg_r64_effect_step 0x1114fb 0x49 0xdc (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1114fe [0x41, 0xBE, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1114fe) (movR32Imm32Effect 0x1114fe 6 14 0x0)
      [] [] [.reg 14, .rip] :=
    (movR32Imm32Effect_footprint 0x1114fe 6 14 0x0).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1114fe 0x41 0xbe (by decide) (by decide) 0x0) pre_rip
  have f3 : InstrSpec 0x111504 [0x4D, 0x19, 0xC6] (fun s => s.RIP = 0x111504) (atFlags StatusFlags.CF (sbbR64R64Effect 0x111504 14 8))
      [.gpr 14, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x111504 14 8).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x111504 0x4d 0xc6 c (by decide) (by decide))) pre_rip
  have f4 : InstrSpec 0x111507 [0x41, 0xBB, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x111507) (movR32Imm32Effect 0x111507 6 11 0x0)
      [] [] [.reg 11, .rip] :=
    (movR32Imm32Effect_footprint 0x111507 6 11 0x0).toInstrSpec (mov_r32_imm32_rex_effect_step 0x111507 0x41 0xbb (by decide) (by decide) 0x0) pre_rip
  have f5 : InstrSpec 0x11150d [0x4D, 0x19, 0xCB] (fun s => s.RIP = 0x11150d) (atFlags StatusFlags.CF (sbbR64R64Effect 0x11150d 11 9))
      [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x11150d 11 9).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x11150d 0x4d 0xcb c (by decide) (by decide))) pre_rip
  have f6 : InstrSpec 0x111510 [0x4D, 0x19, 0xD5] (fun s => s.RIP = 0x111510) (atFlags StatusFlags.CF (sbbR64R64Effect 0x111510 13 10))
      [.gpr 13, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 13, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x111510 13 10).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x111510 0x4d 0xd5 c (by decide) (by decide))) pre_rip
  have f7 : InstrSpec 0x111513 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x111513) (movR64R64Effect 0x111513 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x111513 6 3).toInstrSpec (mov_r64_r64_effect_step 0x111513 0x48 0xde (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111516 [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x111516) (notR64Effect 0x111516 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x111516 6).toInstrSpec (not_r64_effect_step 0x111516 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x111519 [0x0F, 0x93, 0x04, 0x24] (StorePre 0x111519 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111519 + BitVec.ofNat 64 4)) 1) (atFlags (condHolds 3) (setccM8Effect 0x111519 4 (.sib 4 none 0 .none)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.rip] :=
    (setccM8Effect_footprint 0x111519 4 (.sib 4 none 0 .none) 3).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x111519 3 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x11151d [0x48, 0x89, 0xE2] (fun s => s.RIP = 0x11151d) (movR64R64Effect 0x11151d 2 4)
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11151d 2 4).toInstrSpec (mov_r64_r64_effect_step 0x11151d 0x48 0xe2 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x111520 [0x0F, 0xB6, 0x14, 0x24] (LoadPre 0x111520 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111520 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x111520 4 2 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x111520 4 2 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x111520 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x111524 [0x83, 0xE2, 0x01] (fun s => s.RIP = 0x111524) (andR32Imm8Effect 0x111524 3 2 0x1)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x111524 3 2 0x1).toInstrSpec (and_r32_imm8_effect_step 0x111524 0xe2 0x1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111527 [0x48, 0x01, 0xF2] (fun s => s.RIP = 0x111527) (addR64R64Effect 0x111527 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x111527 2 6).toInstrSpec (add_r64_r64_effect_step 0x111527 0x48 0xf2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (12, 53), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114fb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (12, 55), (13, 13), (16, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x1114fe) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (12, 55), (13, 13), (14, 58), (16, 56), (22, 22), (39, 39), (51, 51)]) (p' := 0x111504) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 61) f3 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x111504 14 8 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (12, 55), (13, 13), (14, 60), (16, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x111507) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 63), (12, 55), (13, 13), (14, 60), (16, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x11150d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 66) f5 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x11150d 11 9 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 65), (12, 55), (13, 13), (14, 60), (16, 66), (22, 22), (39, 39), (51, 51)]) (p' := 0x111510) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 69) f6 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x111510 13 10 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 65), (12, 55), (13, 68), (14, 60), (16, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x111513) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (6, 71), (7, 7), (8, 8), (9, 9), (10, 10), (11, 65), (12, 55), (13, 68), (14, 60), (16, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x111516) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 65), (12, 55), (13, 68), (14, 60), (16, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x111519) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 65), (12, 55), (13, 68), (14, 60), (16, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x11151d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 65), (12, 55), (13, 68), (14, 60), (16, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x111520) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 77), (3, 3), (4, 4), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 65), (12, 55), (13, 68), (14, 60), (16, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x111524) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 79), (3, 3), (4, 4), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 65), (12, 55), (13, 68), (14, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x111527) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 81), (3, 3), (4, 4), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 65), (12, 55), (13, 68), (14, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x11152a) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 83) (by decide) rfl

theorem block_l116fd8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l116fd8 :=
  Rest.liftedBlock (rest_l116fd8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l116fd8 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
