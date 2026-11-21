import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l118782 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112ca2 bytes_l118782) (entryMap (live .l118782))
      16 0x112ca2 bytes_l118782 b_l118782 := by
  have f0 : InstrSpec 0x112ca2 [0x48, 0x89, 0x0C, 0x24] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112ca2 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112ca2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112ca2 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112ca2 1 (.sib 4 none 0 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112ca2 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x112ca6 [0x48, 0x89, 0xE1] (fun s => s.RIP = 0x112ca6) (movR64R64Effect 0x112ca6 1 4)
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x112ca6 1 4).toInstrSpec (mov_r64_r64_effect_step 0x112ca6 0x48 0xe1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112ca9 [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x112ca9) (xorR32R32Effect 0x112ca9 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x112ca9 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x112ca9 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x112cac [0x4C, 0x2B, 0x0C, 0x24] (LoadPre 0x112cac (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112cac + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x112cac 9 (.sib 4 none 0 .none))
      [.gpr 9, .gpr 4] [] [.reg 9, .flags, .rip] :=
    (subR64M64Effect_footprint 0x112cac 9 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x112cac 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x112cb0 [0x4C, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x112cb0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x112cb0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112cb0 8 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x112cb0 8 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x112cb0 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x112cb5 [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x112cb5) (movR64R64Effect 0x112cb5 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x112cb5 1 8).toInstrSpec (mov_r64_r64_effect_step 0x112cb5 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112cb8 [0x4C, 0x29, 0xF1] (fun s => s.RIP = 0x112cb8) (subR64R64Effect 0x112cb8 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x112cb8 1 14).toInstrSpec (sub_r64_r64_effect_step 0x112cb8 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x112cbb [0x49, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x112cbb) (sarR64Effect 0x112cbb 4 9 63)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (sarR64Effect_footprint 0x112cbb 4 9 63).toInstrSpec (sar_r64_imm8_effect_step 0x112cbb 0x49 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x112cbf [0x49, 0x01, 0xC9] (fun s => s.RIP = 0x112cbf) (addR64R64Effect 0x112cbf 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112cbf 9 1).toInstrSpec (add_r64_r64_effect_step 0x112cbf 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112cc2 [0x49, 0xF7, 0xD0] (fun s => s.RIP = 0x112cc2) (notR64Effect 0x112cc2 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (notR64Effect_footprint 0x112cc2 8).toInstrSpec (not_r64_effect_step 0x112cc2 0x49 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x112cc5 [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x112cc5) (movR64R64Effect 0x112cc5 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x112cc5 1 14).toInstrSpec (mov_r64_r64_effect_step 0x112cc5 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x112cc8 [0x4C, 0x21, 0xC1] (fun s => s.RIP = 0x112cc8) (andR64R64Effect 0x112cc8 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112cc8 1 8).toInstrSpec (and_r64_r64_effect_step 0x112cc8 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x112ccb [0x4D, 0x09, 0xF0] (fun s => s.RIP = 0x112ccb) (orR64R64Effect 0x112ccb 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x112ccb 8 14).toInstrSpec (or_r64_r64_effect_step 0x112ccb 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x112cce [0x4D, 0x21, 0xC8] (fun s => s.RIP = 0x112cce) (andR64R64Effect 0x112cce 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112cce 8 9).toInstrSpec (and_r64_r64_effect_step 0x112cce 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x112cd1 [0x49, 0x09, 0xC8] (fun s => s.RIP = 0x112cd1) (orR64R64Effect 0x112cd1 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x112cd1 8 1).toInstrSpec (or_r64_r64_effect_step 0x112cd1 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x112cd4 [0x49, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x112cd4) (shrR64Effect 0x112cd4 4 8 63)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x112cd4 4 8 63).toInstrSpec (shr_r64_imm8_effect_step 0x112cd4 0x49 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ca6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ca9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 55), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cac) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 57), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cb0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 59), (9, 57), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cb5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 59), (9, 57), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cb8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 59), (9, 57), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cbb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 59), (9, 65), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cbf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 59), (9, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cc2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 69), (9, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cc5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 71), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 69), (9, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cc8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 69), (9, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ccb) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 75), (9, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cce) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 77), (9, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cd1) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 79), (9, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cd4) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 81), (9, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cd8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 83) (by decide) rfl

theorem block_l118782 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l118782 :=
  Rest.liftedBlock (rest_l118782 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l118782 x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
