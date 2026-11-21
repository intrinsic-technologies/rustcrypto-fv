import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11880b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112d2b bytes_l11880b) (entryMap (live .l11880b))
      11 0x112d2b bytes_l11880b b_l11880b := by
  have f0 : InstrSpec 0x112d2b [0x48, 0x89, 0x04, 0x24] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112d2b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112d2b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112d2b 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112d2b 0 (.sib 4 none 0 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112d2b 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x112d2f [0x48, 0x89, 0xE0] (fun s => s.RIP = 0x112d2f) (movR64R64Effect 0x112d2f 0 4)
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112d2f 0 4).toInstrSpec (mov_r64_r64_effect_step 0x112d2f 0x48 0xe0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112d32 [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x112d32) (xorR32R32Effect 0x112d32 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x112d32 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x112d32 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x112d35 [0x4C, 0x2B, 0x14, 0x24] (LoadPre 0x112d35 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112d35 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x112d35 10 (.sib 4 none 0 .none))
      [.gpr 10, .gpr 4] [] [.reg 10, .flags, .rip] :=
    (subR64M64Effect_footprint 0x112d35 10 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x112d35 0x4c (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x112d39 [0x49, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x112d39) (sarR64Effect 0x112d39 4 10 63)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (sarR64Effect_footprint 0x112d39 4 10 63).toInstrSpec (sar_r64_imm8_effect_step 0x112d39 0x49 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112d3d [0x48, 0xB8, 0x7C, 0x61, 0xE8, 0x58, 0x52, 0x05, 0x19, 0x43] (fun s => s.RIP = 0x112d3d) (movR64Imm64Effect 0x112d3d 0 0x4319055258e8617c)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x112d3d 0 0x4319055258e8617c).toInstrSpec (mov_r64_imm64_effect_step 0x112d3d 0x48 0xb8 (by decide) (by decide) 0x4319055258e8617c) pre_rip
  have f6 : InstrSpec 0x112d47 [0x4C, 0x01, 0xD0] (fun s => s.RIP = 0x112d47) (addR64R64Effect 0x112d47 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112d47 0 10).toInstrSpec (add_r64_r64_effect_step 0x112d47 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x112d4a [0x48, 0x01, 0xD0] (fun s => s.RIP = 0x112d4a) (addR64R64Effect 0x112d4a 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112d4a 0 2).toInstrSpec (add_r64_r64_effect_step 0x112d4a 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x112d4d [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x112d4d) (notR64Effect 0x112d4d 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x112d4d 2).toInstrSpec (not_r64_effect_step 0x112d4d 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112d50 [0x48, 0x09, 0xC2] (fun s => s.RIP = 0x112d50) (orR64R64Effect 0x112d50 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x112d50 2 0).toInstrSpec (or_r64_r64_effect_step 0x112d50 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x112d53 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x112d53) (shrR64Effect 0x112d53 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x112d53 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x112d53 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d2f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d32) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d35) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 57), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d39) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d3d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d47) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d4a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d4d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 1), (2, 67), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d50) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 1), (2, 69), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d53) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (1, 1), (2, 71), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d57) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 73) (by decide) rfl

theorem block_l11880b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11880b :=
  Rest.liftedBlock (rest_l11880b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11880b x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
