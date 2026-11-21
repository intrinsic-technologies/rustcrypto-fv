import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Correction.l118251

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l118288 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1127a8 bytes_l118288) (entryMap (live .l118288))
      9 0x1127a8 bytes_l118288 b_l118288 := by
  have f0 : InstrSpec 0x1127a8 [0x4C, 0x89, 0xC9] (fun s => s.RIP = 0x1127a8) (movR64R64Effect 0x1127a8 1 9)
      [.gpr 9] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1127a8 1 9).toInstrSpec (mov_r64_r64_effect_step 0x1127a8 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1127ab [0x4C, 0x09, 0xD1] (fun s => s.RIP = 0x1127ab) (orR64R64Effect 0x1127ab 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1127ab 1 10).toInstrSpec (or_r64_r64_effect_step 0x1127ab 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1127ae [0x4C, 0x09, 0xC1] (fun s => s.RIP = 0x1127ae) (orR64R64Effect 0x1127ae 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1127ae 1 8).toInstrSpec (or_r64_r64_effect_step 0x1127ae 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1127b1 [0x80, 0xE2, 0x01] (fun s => s.RIP = 0x1127b1) (andR8Imm8Effect 0x1127b1 3 2 0x1)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x1127b1 3 2 0x1).toInstrSpec (and_r8_imm8_effect_step 0x1127b1 0xe2 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1127b4 [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x1127b4) (orR64R64Effect 0x1127b4 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1127b4 1 0).toInstrSpec (or_r64_r64_effect_step 0x1127b4 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1127b7 [0x0F, 0xB6, 0xD2] (fun s => s.RIP = 0x1127b7) (movzxR32R8Effect 0x1127b7 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x1127b7 3 2 2).toInstrSpec (movzx_r32_r8_effect_step 0x1127b7 0xd2 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1127ba [0x41, 0x0F, 0x44, 0xD6] (fun s => s.RIP = 0x1127ba) (atFlags (condHolds 4) (cmovR32R32Effect 0x1127ba 4 2 14))
      [.gpr 2, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR32R32Effect_footprint 0x1127ba 4 2 14 4).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_rex_effect_step 0x1127ba 4 0x41 (by decide) 0xd6 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x1127be [0x88, 0x54, 0x24, 0x07] (StorePre 0x1127be 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1127be + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1127be 4 2 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1127be 4 2 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x1127be 2 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1127c2 [0x4C, 0x8D, 0x74, 0x24, 0x07] (fun s => s.RIP = 0x1127c2) (leaR64Effect 0x1127c2 14 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x1127c2 14 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x1127c2 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127ab) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127ae) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127b1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127b4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127b7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127ba) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (2, 65), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127be) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (2, 65), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127c2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (2, 65), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (19, 61), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127c7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 69) (by decide) rfl

theorem block_l118288 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l118288 :=
  Rest.liftedBlock (rest_l118288 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l118288 x hx)

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine
