import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l118856 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112d76 bytes_l118856) (entryMap (live .l118856))
      11 0x112d76 bytes_l118856 b_l118856 := by
  have f0 : InstrSpec 0x112d76 [0x48, 0x89, 0x34, 0x24] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112d76 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112d76 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112d76 6 (.sib 4 none 0 .none))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112d76 6 (.sib 4 none 0 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112d76 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x112d7a [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x112d7a) (movR64R64Effect 0x112d7a 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x112d7a 6 4).toInstrSpec (mov_r64_r64_effect_step 0x112d7a 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112d7d [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x112d7d) (xorR32R32Effect 0x112d7d 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x112d7d 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x112d7d 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x112d80 [0x4C, 0x2B, 0x14, 0x24] (LoadPre 0x112d80 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112d80 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x112d80 10 (.sib 4 none 0 .none))
      [.gpr 10, .gpr 4] [] [.reg 10, .flags, .rip] :=
    (subR64M64Effect_footprint 0x112d80 10 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x112d80 0x4c (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x112d84 [0x49, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x112d84) (sarR64Effect 0x112d84 4 10 63)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (sarR64Effect_footprint 0x112d84 4 10 63).toInstrSpec (sar_r64_imm8_effect_step 0x112d84 0x49 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112d88 [0x48, 0xBE, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x112d88) (movR64Imm64Effect 0x112d88 6 0x100000000)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x112d88 6 0x100000000).toInstrSpec (mov_r64_imm64_effect_step 0x112d88 0x48 0xbe (by decide) (by decide) 0x100000000) pre_rip
  have f6 : InstrSpec 0x112d92 [0x4C, 0x01, 0xD6] (fun s => s.RIP = 0x112d92) (addR64R64Effect 0x112d92 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112d92 6 10).toInstrSpec (add_r64_r64_effect_step 0x112d92 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x112d95 [0x4C, 0x01, 0xCE] (fun s => s.RIP = 0x112d95) (addR64R64Effect 0x112d95 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112d95 6 9).toInstrSpec (add_r64_r64_effect_step 0x112d95 0x4c 0xce (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x112d98 [0x49, 0xF7, 0xD1] (fun s => s.RIP = 0x112d98) (notR64Effect 0x112d98 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (notR64Effect_footprint 0x112d98 9).toInstrSpec (not_r64_effect_step 0x112d98 0x49 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112d9b [0x49, 0x09, 0xF1] (fun s => s.RIP = 0x112d9b) (orR64R64Effect 0x112d9b 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x112d9b 9 6).toInstrSpec (or_r64_r64_effect_step 0x112d9b 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x112d9e [0x49, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x112d9e) (shrR64Effect 0x112d9e 4 9 63)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x112d9e 4 9 63).toInstrSpec (shr_r64_imm8_effect_step 0x112d9e 0x49 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d7a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d7d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (7, 7), (8, 8), (9, 9), (10, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d80) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (7, 7), (8, 8), (9, 9), (10, 57), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d84) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (7, 7), (8, 8), (9, 9), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d88) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 61), (7, 7), (8, 8), (9, 9), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d92) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 63), (7, 7), (8, 8), (9, 9), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d95) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 65), (7, 7), (8, 8), (9, 9), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d98) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 65), (7, 7), (8, 8), (9, 67), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d9b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 65), (7, 7), (8, 8), (9, 69), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d9e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 65), (7, 7), (8, 8), (9, 71), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112da2) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 73) (by decide) rfl

theorem block_l118856 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l118856 :=
  Rest.liftedBlock (rest_l118856 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l118856 x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
