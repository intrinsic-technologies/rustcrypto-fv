import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.LinearCombination.l116d95_1
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116d95 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1112b5 bytes_l116d95) (entryMap (live .l116d95))
      21 0x1112b5 bytes_l116d95 b_l116d95 := by
  have f0 : InstrSpec 0x1112b5 [0x4D, 0x01, 0xF1] (fun s => s.RIP = 0x1112b5) (addR64R64Effect 0x1112b5 9 14)
      [.gpr 9, .gpr 14] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1112b5 9 14).toInstrSpec (add_r64_r64_effect_step 0x1112b5 0x4d 0xf1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1112b8 [0x4D, 0x11, 0xFC] (fun s => s.RIP = 0x1112b8) (atFlags StatusFlags.CF (adcR64R64Effect 0x1112b8 12 15))
      [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1112b8 12 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1112b8 0x4d 0xfc c (by decide) (by decide))) pre_rip
  have f2 : InstrSpec 0x1112bb [0x48, 0x11, 0xEB] (fun s => s.RIP = 0x1112bb) (atFlags StatusFlags.CF (adcR64R64Effect 0x1112bb 3 5))
      [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1112bb 3 5).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1112bb 0x48 0xeb c (by decide) (by decide))) pre_rip
  have f3 : InstrSpec 0x1112be [0x48, 0x83, 0xD1, 0x00] (fun s => s.RIP = 0x1112be) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1112be 1 0x0))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x1112be 1 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x1112be 0x48 0xd1 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f4 : InstrSpec 0x1112c2 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x1112c2) (movR64R64Effect 0x1112c2 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1112c2 0 13).toInstrSpec (mov_r64_r64_effect_step 0x1112c2 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1112c5 [0x49, 0xF7, 0x23] (LoadPre 0x1112c5 (fun s => AddrMode.addr (.base 11 .none) s (0x1112c5 + BitVec.ofNat 64 3)) 8) (mulM64Effect 0x1112c5 3 (.base 11 .none))
      [.gpr 0, .gpr 11] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x1112c5 3 (.base 11 .none)).toInstrSpec (mul_m64_effect_step 0x1112c5 0x49 (by decide) (.base 11 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1112c8 [0x48, 0x89, 0x54, 0x24, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1112c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1112c8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1112c8 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1112c8 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1112c8 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1112cd [0x48, 0x89, 0x44, 0x24, 0x28] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1112cd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1112cd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1112cd 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1112cd 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1112cd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1112d2 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x1112d2) (movR64R64Effect 0x1112d2 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1112d2 0 13).toInstrSpec (mov_r64_r64_effect_step 0x1112d2 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1112d5 [0x49, 0xF7, 0x63, 0x08] (LoadPre 0x1112d5 (fun s => AddrMode.addr (.base 11 (.d8 0x8)) s (0x1112d5 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x1112d5 4 (.base 11 (.d8 0x8)))
      [.gpr 0, .gpr 11] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x1112d5 4 (.base 11 (.d8 0x8))).toInstrSpec (mul_m64_effect_step 0x1112d5 0x49 (by decide) (.base 11 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1112d9 [0x48, 0x89, 0x54, 0x24, 0x08] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1112d9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1112d9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1112d9 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1112d9 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1112d9 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1112de [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x1112de) (movR64R64Effect 0x1112de 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1112de 15 0).toInstrSpec (mov_r64_r64_effect_step 0x1112de 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1112e1 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x1112e1) (movR64R64Effect 0x1112e1 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1112e1 0 13).toInstrSpec (mov_r64_r64_effect_step 0x1112e1 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1112e4 [0x49, 0xF7, 0x63, 0x10] (LoadPre 0x1112e4 (fun s => AddrMode.addr (.base 11 (.d8 0x10)) s (0x1112e4 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x1112e4 4 (.base 11 (.d8 0x10)))
      [.gpr 0, .gpr 11] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x1112e4 4 (.base 11 (.d8 0x10))).toInstrSpec (mul_m64_effect_step 0x1112e4 0x49 (by decide) (.base 11 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1112e8 [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x1112e8) (movR64R64Effect 0x1112e8 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1112e8 14 0).toInstrSpec (mov_r64_r64_effect_step 0x1112e8 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1112eb [0x48, 0x89, 0xD5] (fun s => s.RIP = 0x1112eb) (movR64R64Effect 0x1112eb 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1112eb 5 2).toInstrSpec (mov_r64_r64_effect_step 0x1112eb 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1112ee [0x4C, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x1112ee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1112ee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1112ee 8 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1112ee 8 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1112ee 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x1112f3 [0x44, 0x32, 0x46, 0x20] (LoadPre 0x1112f3 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1112f3 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1112f3 4 8 (.base 6 (.d8 0x20)))
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x1112f3 4 8 (.base 6 (.d8 0x20))).toInstrSpec (xor_r8_m8_rex_effect_step 0x1112f3 0x44 (by decide) 0 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x1112f7 [0x4C, 0x89, 0x44, 0x24, 0x20] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1112f7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1112f7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1112f7 8 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1112f7 8 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1112f7 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1112fc [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x1112fc) (movR64R64Effect 0x1112fc 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1112fc 0 13).toInstrSpec (mov_r64_r64_effect_step 0x1112fc 0x4c 0xe8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 54), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112b8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 57) f1 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x1112b8 12 15 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112bb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 60) f2 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x1112bb 3 5 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(1, 1), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 15), (16, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112be) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 62), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112c2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 62), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112c5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 62), (2, 67), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112c8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 66), (1, 62), (2, 67), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112cd) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 66), (1, 62), (2, 67), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112d2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 62), (2, 67), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112d5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 73), (1, 62), (2, 74), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112d9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 73), (1, 62), (2, 74), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112de) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 73), (1, 62), (2, 74), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 77), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112e1) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 62), (2, 74), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 77), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112e4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 82) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 62), (2, 82), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 77), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112e8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f14 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 81), (1, 62), (2, 82), (3, 59), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 84), (15, 77), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112eb) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f15 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 81), (1, 62), (2, 82), (3, 59), (4, 4), (5, 86), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 84), (15, 77), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112ee) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 81), (1, 62), (2, 82), (3, 59), (4, 4), (5, 86), (6, 6), (7, 7), (8, 88), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 84), (15, 77), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112f3) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f17 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 81), (1, 62), (2, 82), (3, 59), (4, 4), (5, 86), (6, 6), (7, 7), (8, 90), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 84), (15, 77), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112f7) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 81), (1, 62), (2, 82), (3, 59), (4, 4), (5, 86), (6, 6), (7, 7), (8, 90), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 84), (15, 77), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112fc) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 62), (2, 82), (3, 59), (4, 4), (5, 86), (6, 6), (7, 7), (8, 90), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 84), (15, 77), (22, 22), (39, 39), (51, 51)]) (p' := 0x1112ff) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l116d95_1 code

theorem block_l116d95 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l116d95 :=
  Rest.liftedBlock (rest_l116d95 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l116d95 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
