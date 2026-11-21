import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117033 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111553 bytes_l117033) (entryMap (live .l117033))
      19 0x111553 bytes_l117033 b_l117033 := by
  have f0 : InstrSpec 0x111553 [0x88, 0x0C, 0x24] (StorePre 0x111553 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111553 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x111553 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111553 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x111553 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x111556 [0x44, 0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x111556 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111556 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111556 5 8 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x111556 5 8 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x111556 0x44 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11155b [0x4D, 0x31, 0xCB] (fun s => s.RIP = 0x11155b) (xorR64R64Effect 0x11155b 11 9)
      [.gpr 11, .gpr 9] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x11155b 11 9).toInstrSpec (xor_r64_r64_effect_step 0x11155b 0x4d 0xcb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11155e [0x49, 0xF7, 0xD8] (fun s => s.RIP = 0x11155e) (negR64Effect 0x11155e 8)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (negR64Effect_footprint 0x11155e 8).toInstrSpec (neg_r64_effect_step 0x11155e 0x49 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x111561 [0x4D, 0x21, 0xD8] (fun s => s.RIP = 0x111561) (andR64R64Effect 0x111561 8 11)
      [.gpr 8, .gpr 11] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111561 8 11).toInstrSpec (and_r64_r64_effect_step 0x111561 0x4d 0xd8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x111564 [0x4D, 0x31, 0xC8] (fun s => s.RIP = 0x111564) (xorR64R64Effect 0x111564 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111564 8 9).toInstrSpec (xor_r64_r64_effect_step 0x111564 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111567 [0x88, 0x0C, 0x24] (StorePre 0x111567 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111567 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x111567 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111567 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x111567 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x11156a [0x44, 0x0F, 0xB6, 0x0C, 0x24] (LoadPre 0x11156a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11156a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11156a 5 9 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x11156a 5 9 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x11156a 0x44 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x11156f [0x4D, 0x31, 0xD5] (fun s => s.RIP = 0x11156f) (xorR64R64Effect 0x11156f 13 10)
      [.gpr 13, .gpr 10] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x11156f 13 10).toInstrSpec (xor_r64_r64_effect_step 0x11156f 0x4d 0xd5 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x111572 [0x49, 0xF7, 0xD9] (fun s => s.RIP = 0x111572) (negR64Effect 0x111572 9)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (negR64Effect_footprint 0x111572 9).toInstrSpec (neg_r64_effect_step 0x111572 0x49 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x111575 [0x4D, 0x21, 0xE9] (fun s => s.RIP = 0x111575) (andR64R64Effect 0x111575 9 13)
      [.gpr 9, .gpr 13] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111575 9 13).toInstrSpec (and_r64_r64_effect_step 0x111575 0x4d 0xe9 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x111578 [0x4D, 0x31, 0xD1] (fun s => s.RIP = 0x111578) (xorR64R64Effect 0x111578 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111578 9 10).toInstrSpec (xor_r64_r64_effect_step 0x111578 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11157b [0x88, 0x0C, 0x24] (StorePre 0x11157b 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11157b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x11157b 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11157b 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x11157b 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x11157e [0x49, 0x89, 0xE2] (fun s => s.RIP = 0x11157e) (movR64R64Effect 0x11157e 10 4)
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x11157e 10 4).toInstrSpec (mov_r64_r64_effect_step 0x11157e 0x49 0xe2 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x111581 [0x44, 0x0F, 0xB6, 0x14, 0x24] (LoadPre 0x111581 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111581 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111581 5 10 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x111581 5 10 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x111581 0x44 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x111586 [0x48, 0x31, 0xDA] (fun s => s.RIP = 0x111586) (xorR64R64Effect 0x111586 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111586 2 3).toInstrSpec (xor_r64_r64_effect_step 0x111586 0x48 0xda (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x111589 [0x49, 0xF7, 0xDA] (fun s => s.RIP = 0x111589) (negR64Effect 0x111589 10)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (negR64Effect_footprint 0x111589 10).toInstrSpec (neg_r64_effect_step 0x111589 0x49 0xda (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x11158c [0x49, 0x21, 0xD2] (fun s => s.RIP = 0x11158c) (andR64R64Effect 0x11158c 10 2)
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11158c 10 2).toInstrSpec (and_r64_r64_effect_step 0x11158c 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11158f [0x49, 0x31, 0xDA] (fun s => s.RIP = 0x11158f) (xorR64R64Effect 0x11158f 10 3)
      [.gpr 10, .gpr 3] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x11158f 10 3).toInstrSpec (xor_r64_r64_effect_step 0x11158f 0x49 0xda (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x111556) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 54), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x11155b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 54), (9, 9), (10, 10), (11, 56), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x11155e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 58), (9, 9), (10, 10), (11, 56), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x111561) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 56), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x111564) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 9), (10, 10), (11, 56), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x111567) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 9), (10, 10), (11, 56), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x11156a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 65), (10, 10), (11, 56), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x11156f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 65), (10, 10), (11, 56), (13, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x111572) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 69), (10, 10), (11, 56), (13, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x111575) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 71), (10, 10), (11, 56), (13, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x111578) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 73), (10, 10), (11, 56), (13, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x11157b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 73), (10, 10), (11, 56), (13, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x11157e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 73), (11, 56), (13, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x111581) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 73), (10, 77), (11, 56), (13, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x111586) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 79), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 73), (10, 77), (11, 56), (13, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x111589) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 79), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 73), (10, 81), (11, 56), (13, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x11158c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 79), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 73), (10, 83), (11, 56), (13, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x11158f) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 79), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 73), (10, 85), (11, 56), (13, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x111592) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 87) (by decide) rfl

theorem block_l117033 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117033 :=
  Rest.liftedBlock (rest_l117033 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117033 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
