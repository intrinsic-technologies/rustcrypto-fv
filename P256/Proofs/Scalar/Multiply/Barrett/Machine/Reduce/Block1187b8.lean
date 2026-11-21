import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1187b8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112cd8 bytes_l1187b8) (entryMap (live .l1187b8))
      16 0x112cd8 bytes_l1187b8 b_l1187b8 := by
  have f0 : InstrSpec 0x112cd8 [0x4C, 0x89, 0x04, 0x24] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112cd8 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112cd8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112cd8 8 (.sib 4 none 0 .none))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112cd8 8 (.sib 4 none 0 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112cd8 0x4c (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x112cdc [0x48, 0x89, 0xE1] (fun s => s.RIP = 0x112cdc) (movR64R64Effect 0x112cdc 1 4)
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x112cdc 1 4).toInstrSpec (mov_r64_r64_effect_step 0x112cdc 0x48 0xe1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112cdf [0x31, 0xC9] (fun s => s.RIP = 0x112cdf) (xorR32R32Effect 0x112cdf 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x112cdf 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x112cdf 0xc9 (by decide)) pre_rip
  have f3 : InstrSpec 0x112ce1 [0x48, 0x2B, 0x0C, 0x24] (LoadPre 0x112ce1 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112ce1 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x112ce1 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x112ce1 1 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x112ce1 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x112ce5 [0x4C, 0x8B, 0x54, 0x24, 0x30] (LoadPre 0x112ce5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x112ce5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112ce5 10 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x112ce5 10 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x112ce5 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x112cea [0x4D, 0x89, 0xD0] (fun s => s.RIP = 0x112cea) (movR64R64Effect 0x112cea 8 10)
      [.gpr 10] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x112cea 8 10).toInstrSpec (mov_r64_r64_effect_step 0x112cea 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112ced [0x49, 0x29, 0xD8] (fun s => s.RIP = 0x112ced) (subR64R64Effect 0x112ced 8 3)
      [.gpr 8, .gpr 3] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x112ced 8 3).toInstrSpec (sub_r64_r64_effect_step 0x112ced 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x112cf0 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x112cf0) (sarR64Effect 0x112cf0 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x112cf0 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x112cf0 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x112cf4 [0x4C, 0x01, 0xC1] (fun s => s.RIP = 0x112cf4) (addR64R64Effect 0x112cf4 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112cf4 1 8).toInstrSpec (add_r64_r64_effect_step 0x112cf4 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112cf7 [0x49, 0xF7, 0xD2] (fun s => s.RIP = 0x112cf7) (notR64Effect 0x112cf7 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (notR64Effect_footprint 0x112cf7 10).toInstrSpec (not_r64_effect_step 0x112cf7 0x49 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x112cfa [0x49, 0x89, 0xD8] (fun s => s.RIP = 0x112cfa) (movR64R64Effect 0x112cfa 8 3)
      [.gpr 3] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x112cfa 8 3).toInstrSpec (mov_r64_r64_effect_step 0x112cfa 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x112cfd [0x4D, 0x21, 0xD0] (fun s => s.RIP = 0x112cfd) (andR64R64Effect 0x112cfd 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112cfd 8 10).toInstrSpec (and_r64_r64_effect_step 0x112cfd 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x112d00 [0x49, 0x09, 0xDA] (fun s => s.RIP = 0x112d00) (orR64R64Effect 0x112d00 10 3)
      [.gpr 10, .gpr 3] [] [.reg 10, .flags, .rip] :=
    (orR64R64Effect_footprint 0x112d00 10 3).toInstrSpec (or_r64_r64_effect_step 0x112d00 0x49 0xda (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x112d03 [0x49, 0x21, 0xCA] (fun s => s.RIP = 0x112d03) (andR64R64Effect 0x112d03 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112d03 10 1).toInstrSpec (and_r64_r64_effect_step 0x112d03 0x49 0xca (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x112d06 [0x4D, 0x09, 0xC2] (fun s => s.RIP = 0x112d06) (orR64R64Effect 0x112d06 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (orR64R64Effect_footprint 0x112d06 10 8).toInstrSpec (or_r64_r64_effect_step 0x112d06 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x112d09 [0x49, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x112d09) (shrR64Effect 0x112d09 4 10 63)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x112d09 4 10 63).toInstrSpec (shr_r64_imm8_effect_step 0x112d09 0x49 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cdc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cdf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ce1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ce5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 60), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cea) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 9), (10, 60), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112ced) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 64), (9, 9), (10, 60), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cf0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 66), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 64), (9, 9), (10, 60), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cf4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 64), (9, 9), (10, 60), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cf7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 64), (9, 9), (10, 70), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cfa) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 72), (9, 9), (10, 70), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112cfd) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 74), (9, 9), (10, 70), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d00) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 74), (9, 9), (10, 76), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d03) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 74), (9, 9), (10, 78), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d06) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 74), (9, 9), (10, 80), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d09) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 74), (9, 9), (10, 82), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d0d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 84) (by decide) rfl

theorem block_l1187b8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1187b8 :=
  Rest.liftedBlock (rest_l1187b8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1187b8 x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
