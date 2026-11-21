import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l1038b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1038b0 bytes_l1038b0) (entryMap (live .l1038b0))
      7 0x1038b0 bytes_l1038b0 b_l1038b0 := by
  have f0 : InstrSpec 0x1038b0 [0x4C, 0x8D, 0x47, 0x07] (fun s => s.RIP = 0x1038b0) (leaR64Effect 0x1038b0 8 (.base 7 (.d8 0x7)))
      [.gpr 7] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x1038b0 8 (.base 7 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x1038b0 0x4c (by decide) 0 (.base 7 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1038b4 [0x49, 0x83, 0xE0, 0xF8] (fun s => s.RIP = 0x1038b4) (andR64Imm8Effect 0x1038b4 8 0xf8)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x1038b4 8 0xf8).toInstrSpec (and_r64_imm8_effect_step 0x1038b4 0x49 0xe0 0xf8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1038b8 [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x1038b8) (movR64R64Effect 0x1038b8 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1038b8 0 8).toInstrSpec (mov_r64_r64_effect_step 0x1038b8 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1038bb [0x48, 0x29, 0xF8] (fun s => s.RIP = 0x1038bb) (subR64R64Effect 0x1038bb 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1038bb 0 7).toInstrSpec (sub_r64_r64_effect_step 0x1038bb 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1038be [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x1038be) (movR64R64Effect 0x1038be 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1038be 2 6).toInstrSpec (mov_r64_r64_effect_step 0x1038be 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1038c1 [0x48, 0x29, 0xC2] (fun s => s.RIP = 0x1038c1) (subR64R64Effect 0x1038c1 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1038c1 2 0).toInstrSpec (sub_r64_r64_effect_step 0x1038c1 0x48 0xc2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038b4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038b8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038bb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038be) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038c1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038c4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x1038c4 3 0x19) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1038b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1038b0 :=
  Rest.liftedBlock (rest_l1038b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1038b0 x hx)

theorem rest_l1038c6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1038c6 bytes_l1038c6) (entryMap (live .l1038c6))
      2 0x1038c6 bytes_l1038c6 b_l1038c6 := by
  have f0 : InstrSpec 0x1038c6 [0x48, 0x85, 0xF6] (fun s => s.RIP = 0x1038c6) (testR64R64Effect 0x1038c6 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1038c6 6 6).toInstrSpec (test_r64_r64_effect_step 0x1038c6 0x48 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038c9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1038c9 4 0x5a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1038c6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1038c6 :=
  Rest.liftedBlock (rest_l1038c6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1038c6 x hx)

theorem rest_l1038cb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1038cb bytes_l1038cb) (entryMap (live .l1038cb))
      4 0x1038cb bytes_l1038cb b_l1038cb := by
  have f0 : InstrSpec 0x1038cb [0x89, 0xF1] (fun s => s.RIP = 0x1038cb) (movR32R32Effect 0x1038cb 2 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1038cb 2 1 6).toInstrSpec (mov_r32_r32_effect_step 0x1038cb 0xf1 (by decide)) pre_rip
  have f1 : InstrSpec 0x1038cd [0x83, 0xE1, 0x03] (fun s => s.RIP = 0x1038cd) (andR32Imm8Effect 0x1038cd 3 1 0x3)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1038cd 3 1 0x3).toInstrSpec (and_r32_imm8_effect_step 0x1038cd 0xe1 0x3 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1038d0 [0x48, 0x83, 0xFE, 0x04] (fun s => s.RIP = 0x1038d0) (cmpR64Imm8Effect 0x1038d0 6 0x4)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1038d0 6 0x4).toInstrSpec (cmp_r64_imm8_effect_step 0x1038d0 0x48 0xfe 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038cd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038d0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038d4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x1038d4 3 0x52) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1038cb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1038cb :=
  Rest.liftedBlock (rest_l1038cb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1038cb x hx)

theorem rest_l1038d6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1038d6 bytes_l1038d6) (entryMap (live .l1038d6))
      3 0x1038d6 bytes_l1038d6 b_l1038d6 := by
  have f0 : InstrSpec 0x1038d6 [0x31, 0xD2] (fun s => s.RIP = 0x1038d6) (xorR32R32Effect 0x1038d6 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1038d6 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x1038d6 0xd2 (by decide)) pre_rip
  have f1 : InstrSpec 0x1038d8 [0x31, 0xC0] (fun s => s.RIP = 0x1038d8) (xorR32R32Effect 0x1038d8 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1038d8 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x1038d8 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038d8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038da) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x1038da 0x96 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1038d6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1038d6 :=
  Rest.liftedBlock (rest_l1038d6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1038d6 x hx)

theorem rest_l1038df [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1038df bytes_l1038df) (entryMap (live .l1038df))
      3 0x1038df bytes_l1038df b_l1038df := by
  have f0 : InstrSpec 0x1038df [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x1038df) (movR64R64Effect 0x1038df 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1038df 1 2).toInstrSpec (mov_r64_r64_effect_step 0x1038df 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1038e2 [0x48, 0xC1, 0xE9, 0x03] (fun s => s.RIP = 0x1038e2) (shrR64Effect 0x1038e2 4 1 3)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1038e2 4 1 3).toInstrSpec (shr_r64_imm8_effect_step 0x1038e2 0x48 0xe9 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038e2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 56) f1 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x1038e2 4 1 3 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038e6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x1038e6 4 0xde) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1038df [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1038df :=
  Rest.liftedBlock (rest_l1038df code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1038df x hx)

theorem rest_l1038e8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1038e8 bytes_l1038e8) (entryMap (live .l1038e8))
      9 0x1038e8 bytes_l1038e8 b_l1038e8 := by
  have f0 : InstrSpec 0x1038e8 [0x41, 0x57] (PushPre 0x1038e8 2) (pushR64Effect 0x1038e8 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1038e8 2 15).toInstrSpec (push_r64_rex_effect_step 0x1038e8 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1038ea [0x41, 0x56] (PushPre 0x1038ea 2) (pushR64Effect 0x1038ea 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1038ea 2 14).toInstrSpec (push_r64_rex_effect_step 0x1038ea 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1038ec [0x41, 0x55] (PushPre 0x1038ec 2) (pushR64Effect 0x1038ec 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1038ec 2 13).toInstrSpec (push_r64_rex_effect_step 0x1038ec 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1038ee [0x41, 0x54] (PushPre 0x1038ee 2) (pushR64Effect 0x1038ee 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1038ee 2 12).toInstrSpec (push_r64_rex_effect_step 0x1038ee 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1038f0 [0x53] (PushPre 0x1038f0 1) (pushR64Effect 0x1038f0 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1038f0 1 3).toInstrSpec (push_r64_effect_step 0x1038f0 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1038f1 [0x89, 0xD6] (fun s => s.RIP = 0x1038f1) (movR32R32Effect 0x1038f1 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x1038f1 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x1038f1 0xd6 (by decide)) pre_rip
  have f6 : InstrSpec 0x1038f3 [0x83, 0xE6, 0x07] (fun s => s.RIP = 0x1038f3) (andR32Imm8Effect 0x1038f3 3 6 0x7)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1038f3 3 6 0x7).toInstrSpec (and_r32_imm8_effect_step 0x1038f3 0xe6 0x7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1038f6 [0x49, 0x39, 0xF8] (fun s => s.RIP = 0x1038f6) (cmpR64R64Effect 0x1038f6 8 7)
      [.gpr 8, .gpr 7] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1038f6 8 7).toInstrSpec (cmp_r64_r64_effect_step 0x1038f6 0x49 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038ea) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038ec) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038ee) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038f0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038f1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 63), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038f3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 65), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038f6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 65), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038f9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel8_effect_step 0x1038f9 5 0x8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1038e8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1038e8 :=
  Rest.liftedBlock (rest_l1038e8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1038e8 x hx)

theorem rest_l1038fb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1038fb bytes_l1038fb) (entryMap (live .l1038fb))
      2 0x1038fb bytes_l1038fb b_l1038fb := by
  have f0 : InstrSpec 0x1038fb [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x1038fb) (xorR32R32Effect 0x1038fb 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1038fb 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1038fb 0x45 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038fe) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x1038fe 0x122 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1038fb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1038fb :=
  Rest.liftedBlock (rest_l1038fb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1038fb x hx)

theorem rest_l103903 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103903 bytes_l103903) (entryMap (live .l103903))
      6 0x103903 bytes_l103903 b_l103903 := by
  have f0 : InstrSpec 0x103903 [0x41, 0x89, 0xC1] (fun s => s.RIP = 0x103903) (movR32R32Effect 0x103903 3 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x103903 3 9 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x103903 0x41 0xc1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103906 [0x41, 0x83, 0xE1, 0x03] (fun s => s.RIP = 0x103906) (andR32Imm8Effect 0x103906 4 9 0x3)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x103906 4 9 0x3).toInstrSpec (and_r32_imm8_rex_effect_step 0x103906 0x41 0xe1 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10390a [0x49, 0x89, 0xFA] (fun s => s.RIP = 0x10390a) (movR64R64Effect 0x10390a 10 7)
      [.gpr 7] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10390a 10 7).toInstrSpec (mov_r64_r64_effect_step 0x10390a 0x49 0xfa (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10390d [0x4D, 0x29, 0xC2] (fun s => s.RIP = 0x10390d) (subR64R64Effect 0x10390d 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10390d 10 8).toInstrSpec (sub_r64_r64_effect_step 0x10390d 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103910 [0x49, 0x83, 0xFA, 0xFC] (fun s => s.RIP = 0x103910) (cmpR64Imm8Effect 0x103910 10 0xfc)
      [.gpr 10] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x103910 10 0xfc).toInstrSpec (cmp_r64_imm8_effect_step 0x103910 0x49 0xfa 0xfc (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103906) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10390a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 57), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10390d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 59), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103910) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 59), (11, 11), (14, 14), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103914) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel32_effect_step 0x103914 6 0x7c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103903 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103903 :=
  Rest.liftedBlock (rest_l103903 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103903 x hx)

theorem rest_l10391a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10391a bytes_l10391a) (entryMap (live .l10391a))
      3 0x10391a bytes_l10391a b_l10391a := by
  have f0 : InstrSpec 0x10391a [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x10391a) (xorR32R32Effect 0x10391a 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10391a 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x10391a 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10391d [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x10391d) (xorR32R32Effect 0x10391d 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10391d 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x10391d 0x45 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10391d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 53), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103920) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x103920 0xd6 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10391a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10391a :=
  Rest.liftedBlock (rest_l10391a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10391a x hx)

theorem rest_l103925 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103925 bytes_l103925) (entryMap (live .l103925))
      2 0x103925 bytes_l103925 b_l103925 := by
  have f0 : InstrSpec 0x103925 [0x31, 0xC0] (fun s => s.RIP = 0x103925) (xorR32R32Effect 0x103925 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103925 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x103925 0xc0 (by decide)) pre_rip
  have f1 : InstrSpec 0x103927 [0xC3] (RetPre 0x103927) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x103927).toInstrSpec (ret_effect_step 0x103927) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103927) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 57) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f1 (by decide) rfl rfl rfl (by decide)

theorem block_l103925 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103925 :=
  Rest.liftedBlock (rest_l103925 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103925 x hx)

theorem rest_l103928 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103928 bytes_l103928) (entryMap (live .l103928))
      3 0x103928 bytes_l103928 b_l103928 := by
  have f0 : InstrSpec 0x103928 [0x48, 0x83, 0xE6, 0xFC] (fun s => s.RIP = 0x103928) (andR64Imm8Effect 0x103928 6 0xfc)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x103928 6 0xfc).toInstrSpec (and_r64_imm8_effect_step 0x103928 0x48 0xe6 0xfc (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10392c [0x31, 0xD2] (fun s => s.RIP = 0x10392c) (xorR32R32Effect 0x10392c 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10392c 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x10392c 0xd2 (by decide)) pre_rip
  have f2 : InstrSpec 0x10392e [0x31, 0xC0] (fun s => s.RIP = 0x10392e) (xorR32R32Effect 0x10392e 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10392e 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x10392e 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10392c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10392e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103930) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l103928 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103928 :=
  Rest.liftedBlock (rest_l103928 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103928 x hx)

theorem rest_l103930 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103930 bytes_l103930) (entryMap (live .l103930))
      19 0x103930 bytes_l103930 b_l103930 := by
  have f0 : InstrSpec 0x103930 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x103930) (xorR32R32Effect 0x103930 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103930 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x103930 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103933 [0x80, 0x3C, 0x17, 0xC0] (LoadPre 0x103933 (fun s => AddrMode.addr (.sib 7 (some 2) 0 .none) s (0x103933 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x103933 4 (.sib 7 (some 2) 0 .none) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x103933 4 (.sib 7 (some 2) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x103933 (.sib 7 (some 2) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103937 [0x41, 0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x103937) (atFlags (condHolds 13) (setccR8Effect 0x103937 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x103937 4 8 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x103937 13 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x10393b [0x49, 0x01, 0xC0] (fun s => s.RIP = 0x10393b) (addR64R64Effect 0x10393b 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10393b 8 0).toInstrSpec (add_r64_r64_effect_step 0x10393b 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10393e [0x31, 0xC0] (fun s => s.RIP = 0x10393e) (xorR32R32Effect 0x10393e 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10393e 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x10393e 0xc0 (by decide)) pre_rip
  have f5 : InstrSpec 0x103940 [0x80, 0x7C, 0x17, 0x01, 0xC0] (LoadPre 0x103940 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x1)) s (0x103940 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103940 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x103940 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x103940 (.sib 7 (some 2) 0 (.d8 0x1)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x103945 [0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x103945) (atFlags (condHolds 13) (setccR8Effect 0x103945 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x103945 3 0 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x103945 13 0xc0 (by decide) (by decide) c)) pre_rip
  have f7 : InstrSpec 0x103948 [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x103948) (xorR32R32Effect 0x103948 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103948 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x103948 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10394b [0x80, 0x7C, 0x17, 0x02, 0xC0] (LoadPre 0x10394b (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x2)) s (0x10394b + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x10394b 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x10394b 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x10394b (.sib 7 (some 2) 0 (.d8 0x2)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x103950 [0x41, 0x0F, 0x9D, 0xC1] (fun s => s.RIP = 0x103950) (atFlags (condHolds 13) (setccR8Effect 0x103950 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x103950 4 9 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x103950 13 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f10 : InstrSpec 0x103954 [0x49, 0x01, 0xC1] (fun s => s.RIP = 0x103954) (addR64R64Effect 0x103954 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103954 9 0).toInstrSpec (add_r64_r64_effect_step 0x103954 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x103957 [0x4D, 0x01, 0xC1] (fun s => s.RIP = 0x103957) (addR64R64Effect 0x103957 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103957 9 8).toInstrSpec (add_r64_r64_effect_step 0x103957 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10395a [0x31, 0xC0] (fun s => s.RIP = 0x10395a) (xorR32R32Effect 0x10395a 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10395a 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x10395a 0xc0 (by decide)) pre_rip
  have f13 : InstrSpec 0x10395c [0x80, 0x7C, 0x17, 0x03, 0xC0] (LoadPre 0x10395c (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x3)) s (0x10395c + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x10395c 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x10395c 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x10395c (.sib 7 (some 2) 0 (.d8 0x3)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x103961 [0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x103961) (atFlags (condHolds 13) (setccR8Effect 0x103961 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x103961 3 0 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x103961 13 0xc0 (by decide) (by decide) c)) pre_rip
  have f15 : InstrSpec 0x103964 [0x4C, 0x01, 0xC8] (fun s => s.RIP = 0x103964) (addR64R64Effect 0x103964 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103964 0 9).toInstrSpec (add_r64_r64_effect_step 0x103964 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x103967 [0x48, 0x83, 0xC2, 0x04] (fun s => s.RIP = 0x103967) (addR64Imm8Effect 0x103967 2 0x4)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x103967 2 0x4).toInstrSpec (add_r64_imm8_effect_step 0x103967 0x48 0xc2 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10396b [0x48, 0x39, 0xD6] (fun s => s.RIP = 0x10396b) (cmpR64R64Effect 0x10396b 6 2)
      [.gpr 6, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x10396b 6 2).toInstrSpec (cmp_r64_r64_effect_step 0x10396b 0x48 0xd6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103933) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103937) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 58), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10393b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10393e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103940) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 64), (21, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103945) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 64), (21, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103948) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10394b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f8 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f8 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 71), (21, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103950) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 74), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 71), (21, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103954) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 76), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103957) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10395a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10395c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f13 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f13 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 82), (21, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103961) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 82), (21, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103964) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103967) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 87), (1, 1), (2, 89), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10396b) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 87), (1, 1), (2, 89), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10396e) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 93) (jcc_rel8_effect_step 0x10396e 5 0xc0) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103930 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103930 :=
  Rest.liftedBlock (rest_l103930 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103930 x hx)

theorem rest_l103970 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103970 bytes_l103970) (entryMap (live .l103970))
      2 0x103970 bytes_l103970 b_l103970 := by
  have f0 : InstrSpec 0x103970 [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x103970) (testR64R64Effect 0x103970 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x103970 1 1).toInstrSpec (test_r64_r64_effect_step 0x103970 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103973) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x103973 4 0x20) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103970 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103970 :=
  Rest.liftedBlock (rest_l103970 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103970 x hx)

theorem rest_l103975 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103975 bytes_l103975) (entryMap (live .l103975))
      3 0x103975 bytes_l103975 b_l103975 := by
  have f0 : InstrSpec 0x103975 [0x48, 0x01, 0xD7] (fun s => s.RIP = 0x103975) (addR64R64Effect 0x103975 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103975 7 2).toInstrSpec (add_r64_r64_effect_step 0x103975 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103978 [0x31, 0xD2] (fun s => s.RIP = 0x103978) (xorR32R32Effect 0x103978 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103978 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x103978 0xd2 (by decide)) pre_rip
  have f2 : InstrSpec 0x10397a [0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x10397a) (fun _ => nopEffect 0x10397a 6)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10397a 6).toInstrSpec (nop_m_effect_step 0x10397a [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103978) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10397a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103980) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l103975 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103975 :=
  Rest.liftedBlock (rest_l103975 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103975 x hx)

theorem rest_l103980 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103980 bytes_l103980) (entryMap (live .l103980))
      7 0x103980 bytes_l103980 b_l103980 := by
  have f0 : InstrSpec 0x103980 [0x31, 0xF6] (fun s => s.RIP = 0x103980) (xorR32R32Effect 0x103980 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103980 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x103980 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x103982 [0x80, 0x3C, 0x17, 0xC0] (LoadPre 0x103982 (fun s => AddrMode.addr (.sib 7 (some 2) 0 .none) s (0x103982 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x103982 4 (.sib 7 (some 2) 0 .none) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x103982 4 (.sib 7 (some 2) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x103982 (.sib 7 (some 2) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103986 [0x40, 0x0F, 0x9D, 0xC6] (fun s => s.RIP = 0x103986) (atFlags (condHolds 13) (setccR8Effect 0x103986 4 6))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 6, .rip] :=
    (setccR8Effect_footprint 0x103986 4 6 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x103986 13 0x40 (by decide) 0xc6 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x10398a [0x48, 0x01, 0xF0] (fun s => s.RIP = 0x10398a) (addR64R64Effect 0x10398a 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10398a 0 6).toInstrSpec (add_r64_r64_effect_step 0x10398a 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10398d [0x48, 0xFF, 0xC2] (fun s => s.RIP = 0x10398d) (incR64Effect 0x10398d 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (incR64Effect_footprint 0x10398d 2).toInstrSpec (inc_r64_effect_step 0x10398d 0x48 0xc2 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103990 [0x48, 0x39, 0xD1] (fun s => s.RIP = 0x103990) (cmpR64R64Effect 0x103990 1 2)
      [.gpr 1, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103990 1 2).toInstrSpec (cmp_r64_r64_effect_step 0x103990 0x48 0xd1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103982) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103986) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10398a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10398d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103990) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 60), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103993) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x103993 5 0xeb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103980 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103980 :=
  Rest.liftedBlock (rest_l103980 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103980 x hx)

theorem rest_l103995 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103995 bytes_l103995) (entryMap (live .l103995))
      1 0x103995 bytes_l103995 b_l103995 := by
  have f0 : InstrSpec 0x103995 [0xC3] (RetPre 0x103995) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x103995).toInstrSpec (ret_effect_step 0x103995) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f0 (by decide) rfl rfl rfl (by decide)

theorem block_l103995 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103995 :=
  Rest.liftedBlock (rest_l103995 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103995 x hx)

theorem rest_l103996 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103996 bytes_l103996) (entryMap (live .l103996))
      5 0x103996 bytes_l103996 b_l103996 := by
  have f0 : InstrSpec 0x103996 [0x41, 0x89, 0xC3] (fun s => s.RIP = 0x103996) (movR32R32Effect 0x103996 3 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x103996 3 11 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x103996 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103999 [0x41, 0x83, 0xE3, 0x04] (fun s => s.RIP = 0x103999) (andR32Imm8Effect 0x103999 4 11 0x4)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x103999 4 11 0x4).toInstrSpec (and_r32_imm8_rex_effect_step 0x103999 0x41 0xe3 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10399d [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x10399d) (xorR32R32Effect 0x10399d 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10399d 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x10399d 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1039a0 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x1039a0) (xorR32R32Effect 0x1039a0 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1039a0 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1039a0 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1039a3 [0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1039a3) (fun _ => nopEffect 0x1039a3 13)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1039a3 13).toInstrSpec (nop_m_effect_step 0x1039a3 [0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103999) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10399d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 57), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039a0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 57), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039a3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 57), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039b0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l103996 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103996 :=
  Rest.liftedBlock (rest_l103996 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103996 x hx)

theorem rest_l1039b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1039b0 bytes_l1039b0) (entryMap (live .l1039b0))
      19 0x1039b0 bytes_l1039b0 b_l1039b0 := by
  have f0 : InstrSpec 0x1039b0 [0x31, 0xDB] (fun s => s.RIP = 0x1039b0) (xorR32R32Effect 0x1039b0 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1039b0 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x1039b0 0xdb (by decide)) pre_rip
  have f1 : InstrSpec 0x1039b2 [0x42, 0x80, 0x3C, 0x17, 0xC0] (LoadPre 0x1039b2 (fun s => AddrMode.addr (.sib 7 (some 10) 0 .none) s (0x1039b2 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1039b2 5 (.sib 7 (some 10) 0 .none) 0xc0)
      [.gpr 7, .gpr 10] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x1039b2 5 (.sib 7 (some 10) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x1039b2 0x42 (by decide) (.sib 7 (some 10) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1039b7 [0x0F, 0x9D, 0xC3] (fun s => s.RIP = 0x1039b7) (atFlags (condHolds 13) (setccR8Effect 0x1039b7 3 3))
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 3, .rip] :=
    (setccR8Effect_footprint 0x1039b7 3 3 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1039b7 13 0xc3 (by decide) (by decide) c)) pre_rip
  have f3 : InstrSpec 0x1039ba [0x4C, 0x01, 0xC3] (fun s => s.RIP = 0x1039ba) (addR64R64Effect 0x1039ba 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1039ba 3 8).toInstrSpec (add_r64_r64_effect_step 0x1039ba 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1039bd [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x1039bd) (xorR32R32Effect 0x1039bd 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1039bd 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1039bd 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1039c0 [0x42, 0x80, 0x7C, 0x17, 0x01, 0xC0] (LoadPre 0x1039c0 (fun s => AddrMode.addr (.sib 7 (some 10) 0 (.d8 0x1)) s (0x1039c0 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x1039c0 6 (.sib 7 (some 10) 0 (.d8 0x1)) 0xc0)
      [.gpr 7, .gpr 10] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x1039c0 6 (.sib 7 (some 10) 0 (.d8 0x1)) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x1039c0 0x42 (by decide) (.sib 7 (some 10) 0 (.d8 0x1)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1039c6 [0x41, 0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x1039c6) (atFlags (condHolds 13) (setccR8Effect 0x1039c6 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x1039c6 4 8 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1039c6 13 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x1039ca [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x1039ca) (xorR32R32Effect 0x1039ca 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1039ca 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x1039ca 0x45 0xf6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1039cd [0x42, 0x80, 0x7C, 0x17, 0x02, 0xC0] (LoadPre 0x1039cd (fun s => AddrMode.addr (.sib 7 (some 10) 0 (.d8 0x2)) s (0x1039cd + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x1039cd 6 (.sib 7 (some 10) 0 (.d8 0x2)) 0xc0)
      [.gpr 7, .gpr 10] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x1039cd 6 (.sib 7 (some 10) 0 (.d8 0x2)) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x1039cd 0x42 (by decide) (.sib 7 (some 10) 0 (.d8 0x2)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1039d3 [0x41, 0x0F, 0x9D, 0xC6] (fun s => s.RIP = 0x1039d3) (atFlags (condHolds 13) (setccR8Effect 0x1039d3 4 14))
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 14, .rip] :=
    (setccR8Effect_footprint 0x1039d3 4 14 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1039d3 13 0x41 (by decide) 0xc6 (by decide) c)) pre_rip
  have f10 : InstrSpec 0x1039d7 [0x4D, 0x01, 0xC6] (fun s => s.RIP = 0x1039d7) (addR64R64Effect 0x1039d7 14 8)
      [.gpr 14, .gpr 8] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1039d7 14 8).toInstrSpec (add_r64_r64_effect_step 0x1039d7 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1039da [0x49, 0x01, 0xDE] (fun s => s.RIP = 0x1039da) (addR64R64Effect 0x1039da 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1039da 14 3).toInstrSpec (add_r64_r64_effect_step 0x1039da 0x49 0xde (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1039dd [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x1039dd) (xorR32R32Effect 0x1039dd 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1039dd 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1039dd 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1039e0 [0x42, 0x80, 0x7C, 0x17, 0x03, 0xC0] (LoadPre 0x1039e0 (fun s => AddrMode.addr (.sib 7 (some 10) 0 (.d8 0x3)) s (0x1039e0 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x1039e0 6 (.sib 7 (some 10) 0 (.d8 0x3)) 0xc0)
      [.gpr 7, .gpr 10] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x1039e0 6 (.sib 7 (some 10) 0 (.d8 0x3)) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x1039e0 0x42 (by decide) (.sib 7 (some 10) 0 (.d8 0x3)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1039e6 [0x41, 0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x1039e6) (atFlags (condHolds 13) (setccR8Effect 0x1039e6 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x1039e6 4 8 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1039e6 13 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x1039ea [0x4D, 0x01, 0xF0] (fun s => s.RIP = 0x1039ea) (addR64R64Effect 0x1039ea 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1039ea 8 14).toInstrSpec (add_r64_r64_effect_step 0x1039ea 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1039ed [0x49, 0x83, 0xC2, 0x04] (fun s => s.RIP = 0x1039ed) (addR64Imm8Effect 0x1039ed 10 0x4)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1039ed 10 0x4).toInstrSpec (add_r64_imm8_effect_step 0x1039ed 0x49 0xc2 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1039f1 [0x4D, 0x39, 0xD3] (fun s => s.RIP = 0x1039f1) (cmpR64R64Effect 0x1039f1 11 10)
      [.gpr 11, .gpr 10] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1039f1 11 10).toInstrSpec (cmp_r64_r64_effect_step 0x1039f1 0x4d 0xd3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039b2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039b7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039ba) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039bd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 62), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039c0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 62), (9, 9), (10, 10), (11, 11), (14, 14), (20, 64), (21, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039c6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (14, 14), (20, 64), (21, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039ca) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (14, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039cd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f8 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f8 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (14, 69), (20, 71), (21, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039d3) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (14, 74), (20, 71), (21, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039d7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (14, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039da) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (14, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039dd) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 80), (9, 9), (10, 10), (11, 11), (14, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039e0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f13 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f13 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 80), (9, 9), (10, 10), (11, 11), (14, 78), (20, 82), (21, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039e6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 9), (10, 10), (11, 11), (14, 78), (20, 82), (21, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039ea) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 87), (9, 9), (10, 10), (11, 11), (14, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039ed) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f16 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 87), (9, 9), (10, 89), (11, 11), (14, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039f1) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 87), (9, 9), (10, 89), (11, 11), (14, 78), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039f4) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 93) (jcc_rel8_effect_step 0x1039f4 5 0xba) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1039b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1039b0 :=
  Rest.liftedBlock (rest_l1039b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1039b0 x hx)

theorem rest_l1039f6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1039f6 bytes_l1039f6) (entryMap (live .l1039f6))
      2 0x1039f6 bytes_l1039f6 b_l1039f6 := by
  have f0 : InstrSpec 0x1039f6 [0x4D, 0x85, 0xC9] (fun s => s.RIP = 0x1039f6) (testR64R64Effect 0x1039f6 9 9)
      [.gpr 9, .gpr 9] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1039f6 9 9).toInstrSpec (test_r64_r64_effect_step 0x1039f6 0x4d 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039f9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1039f9 4 0x2a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1039f6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1039f6 :=
  Rest.liftedBlock (rest_l1039f6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1039f6 x hx)

theorem rest_l1039fb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1039fb bytes_l1039fb) (entryMap (live .l1039fb))
      3 0x1039fb bytes_l1039fb b_l1039fb := by
  have f0 : InstrSpec 0x1039fb [0x49, 0x01, 0xFA] (fun s => s.RIP = 0x1039fb) (addR64R64Effect 0x1039fb 10 7)
      [.gpr 10, .gpr 7] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1039fb 10 7).toInstrSpec (add_r64_r64_effect_step 0x1039fb 0x49 0xfa (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1039fe [0x45, 0x31, 0xDB] (fun s => s.RIP = 0x1039fe) (xorR32R32Effect 0x1039fe 3 11 11)
      [.gpr 11, .gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1039fe 3 11 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x1039fe 0x45 0xdb (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103a01 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103a01) (fun _ => nopEffect 0x103a01 15)
      [] [] [.rip] :=
    (nopEffect_footprint 0x103a01 15).toInstrSpec (nop_m_effect_step 0x103a01 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1039fe) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a01) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a10) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l1039fb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1039fb :=
  Rest.liftedBlock (rest_l1039fb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1039fb x hx)

theorem rest_l103a10 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103a10 bytes_l103a10) (entryMap (live .l103a10))
      7 0x103a10 bytes_l103a10 b_l103a10 := by
  have f0 : InstrSpec 0x103a10 [0x31, 0xDB] (fun s => s.RIP = 0x103a10) (xorR32R32Effect 0x103a10 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103a10 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x103a10 0xdb (by decide)) pre_rip
  have f1 : InstrSpec 0x103a12 [0x43, 0x80, 0x3C, 0x1A, 0xC0] (LoadPre 0x103a12 (fun s => AddrMode.addr (.sib 10 (some 11) 0 .none) s (0x103a12 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103a12 5 (.sib 10 (some 11) 0 .none) 0xc0)
      [.gpr 10, .gpr 11] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x103a12 5 (.sib 10 (some 11) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x103a12 0x43 (by decide) (.sib 10 (some 11) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103a17 [0x0F, 0x9D, 0xC3] (fun s => s.RIP = 0x103a17) (atFlags (condHolds 13) (setccR8Effect 0x103a17 3 3))
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 3, .rip] :=
    (setccR8Effect_footprint 0x103a17 3 3 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x103a17 13 0xc3 (by decide) (by decide) c)) pre_rip
  have f3 : InstrSpec 0x103a1a [0x49, 0x01, 0xD8] (fun s => s.RIP = 0x103a1a) (addR64R64Effect 0x103a1a 8 3)
      [.gpr 8, .gpr 3] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103a1a 8 3).toInstrSpec (add_r64_r64_effect_step 0x103a1a 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103a1d [0x49, 0xFF, 0xC3] (fun s => s.RIP = 0x103a1d) (incR64Effect 0x103a1d 11)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (incR64Effect_footprint 0x103a1d 11).toInstrSpec (inc_r64_effect_step 0x103a1d 0x49 0xc3 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103a20 [0x4D, 0x39, 0xD9] (fun s => s.RIP = 0x103a20) (cmpR64R64Effect 0x103a20 9 11)
      [.gpr 9, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103a20 9 11).toInstrSpec (cmp_r64_r64_effect_step 0x103a20 0x4d 0xd9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a12) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a17) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a1a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a1d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 62), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a20) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 62), (14, 14), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a23) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x103a23 5 0xeb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103a10 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103a10 :=
  Rest.liftedBlock (rest_l103a10 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103a10 x hx)

theorem rest_l103a25 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103a25 bytes_l103a25) (entryMap (live .l103a25))
      3 0x103a25 bytes_l103a25 b_l103a25 := by
  have f0 : InstrSpec 0x103a25 [0x48, 0x01, 0xC7] (fun s => s.RIP = 0x103a25) (addR64R64Effect 0x103a25 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103a25 7 0).toInstrSpec (add_r64_r64_effect_step 0x103a25 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103a28 [0x48, 0x85, 0xF6] (fun s => s.RIP = 0x103a28) (testR64R64Effect 0x103a28 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x103a28 6 6).toInstrSpec (test_r64_r64_effect_step 0x103a28 0x48 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a28) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a2b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x103a2b 4 0x8f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103a25 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103a25 :=
  Rest.liftedBlock (rest_l103a25 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103a25 x hx)

theorem rest_l103a31 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103a31 bytes_l103a31) (entryMap (live .l103a31))
      7 0x103a31 bytes_l103a31 b_l103a31 := by
  have f0 : InstrSpec 0x103a31 [0x48, 0xB8, 0xF8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x103a31) (movR64Imm64Effect 0x103a31 0 0x7ffffffffffffff8)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x103a31 0 0x7ffffffffffffff8).toInstrSpec (mov_r64_imm64_effect_step 0x103a31 0x48 0xb8 (by decide) (by decide) 0x7ffffffffffffff8) pre_rip
  have f1 : InstrSpec 0x103a3b [0x48, 0x21, 0xC2] (fun s => s.RIP = 0x103a3b) (andR64R64Effect 0x103a3b 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103a3b 2 0).toInstrSpec (and_r64_r64_effect_step 0x103a3b 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103a3e [0x31, 0xC0] (fun s => s.RIP = 0x103a3e) (xorR32R32Effect 0x103a3e 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103a3e 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x103a3e 0xc0 (by decide)) pre_rip
  have f3 : InstrSpec 0x103a40 [0x80, 0x3C, 0x17, 0xC0] (LoadPre 0x103a40 (fun s => AddrMode.addr (.sib 7 (some 2) 0 .none) s (0x103a40 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x103a40 4 (.sib 7 (some 2) 0 .none) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x103a40 4 (.sib 7 (some 2) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x103a40 (.sib 7 (some 2) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x103a44 [0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x103a44) (atFlags (condHolds 13) (setccR8Effect 0x103a44 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x103a44 3 0 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x103a44 13 0xc0 (by decide) (by decide) c)) pre_rip
  have f5 : InstrSpec 0x103a47 [0x83, 0xFE, 0x01] (fun s => s.RIP = 0x103a47) (cmpR32Imm8Effect 0x103a47 3 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x103a47 3 6 0x1).toInstrSpec (cmp_r32_imm8_effect_step 0x103a47 0xfe 0x1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a3b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a3e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a40) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 57), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (20, 59), (21, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a44) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (20, 59), (21, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a47) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a4a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x103a4a 4 0x76) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103a31 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103a31 :=
  Rest.liftedBlock (rest_l103a31 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103a31 x hx)

theorem rest_l103a4c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103a4c bytes_l103a4c) (entryMap (live .l103a4c))
      6 0x103a4c bytes_l103a4c b_l103a4c := by
  have f0 : InstrSpec 0x103a4c [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x103a4c) (xorR32R32Effect 0x103a4c 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103a4c 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x103a4c 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103a4f [0x80, 0x7C, 0x17, 0x01, 0xC0] (LoadPre 0x103a4f (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x1)) s (0x103a4f + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103a4f 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x103a4f 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x103a4f (.sib 7 (some 2) 0 (.d8 0x1)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103a54 [0x41, 0x0F, 0x9D, 0xC1] (fun s => s.RIP = 0x103a54) (atFlags (condHolds 13) (setccR8Effect 0x103a54 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x103a54 4 9 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x103a54 13 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x103a58 [0x4C, 0x01, 0xC8] (fun s => s.RIP = 0x103a58) (addR64R64Effect 0x103a58 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103a58 0 9).toInstrSpec (add_r64_r64_effect_step 0x103a58 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103a5b [0x83, 0xFE, 0x02] (fun s => s.RIP = 0x103a5b) (cmpR32Imm8Effect 0x103a5b 3 6 0x2)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x103a5b 3 6 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x103a5b 0xfe 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a4f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a54) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a58) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a5b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a5e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x103a5e 4 0x62) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103a4c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103a4c :=
  Rest.liftedBlock (rest_l103a4c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103a4c x hx)

theorem rest_l103a60 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103a60 bytes_l103a60) (entryMap (live .l103a60))
      6 0x103a60 bytes_l103a60 b_l103a60 := by
  have f0 : InstrSpec 0x103a60 [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x103a60) (xorR32R32Effect 0x103a60 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103a60 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x103a60 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103a63 [0x80, 0x7C, 0x17, 0x02, 0xC0] (LoadPre 0x103a63 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x2)) s (0x103a63 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103a63 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x103a63 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x103a63 (.sib 7 (some 2) 0 (.d8 0x2)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103a68 [0x41, 0x0F, 0x9D, 0xC1] (fun s => s.RIP = 0x103a68) (atFlags (condHolds 13) (setccR8Effect 0x103a68 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x103a68 4 9 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x103a68 13 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x103a6c [0x4C, 0x01, 0xC8] (fun s => s.RIP = 0x103a6c) (addR64R64Effect 0x103a6c 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103a6c 0 9).toInstrSpec (add_r64_r64_effect_step 0x103a6c 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103a6f [0x83, 0xFE, 0x03] (fun s => s.RIP = 0x103a6f) (cmpR32Imm8Effect 0x103a6f 3 6 0x3)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x103a6f 3 6 0x3).toInstrSpec (cmp_r32_imm8_effect_step 0x103a6f 0xfe 0x3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a63) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a68) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a6c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a6f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a72) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x103a72 4 0x4e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103a60 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103a60 :=
  Rest.liftedBlock (rest_l103a60 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103a60 x hx)

theorem rest_l103a74 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103a74 bytes_l103a74) (entryMap (live .l103a74))
      6 0x103a74 bytes_l103a74 b_l103a74 := by
  have f0 : InstrSpec 0x103a74 [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x103a74) (xorR32R32Effect 0x103a74 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103a74 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x103a74 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103a77 [0x80, 0x7C, 0x17, 0x03, 0xC0] (LoadPre 0x103a77 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x3)) s (0x103a77 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103a77 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x103a77 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x103a77 (.sib 7 (some 2) 0 (.d8 0x3)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103a7c [0x41, 0x0F, 0x9D, 0xC1] (fun s => s.RIP = 0x103a7c) (atFlags (condHolds 13) (setccR8Effect 0x103a7c 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x103a7c 4 9 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x103a7c 13 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x103a80 [0x4C, 0x01, 0xC8] (fun s => s.RIP = 0x103a80) (addR64R64Effect 0x103a80 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103a80 0 9).toInstrSpec (add_r64_r64_effect_step 0x103a80 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103a83 [0x83, 0xFE, 0x04] (fun s => s.RIP = 0x103a83) (cmpR32Imm8Effect 0x103a83 3 6 0x4)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x103a83 3 6 0x4).toInstrSpec (cmp_r32_imm8_effect_step 0x103a83 0xfe 0x4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a77) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a7c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a80) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a83) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a86) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x103a86 4 0x3a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103a74 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103a74 :=
  Rest.liftedBlock (rest_l103a74 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103a74 x hx)

theorem rest_l103a88 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103a88 bytes_l103a88) (entryMap (live .l103a88))
      6 0x103a88 bytes_l103a88 b_l103a88 := by
  have f0 : InstrSpec 0x103a88 [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x103a88) (xorR32R32Effect 0x103a88 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103a88 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x103a88 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103a8b [0x80, 0x7C, 0x17, 0x04, 0xC0] (LoadPre 0x103a8b (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x4)) s (0x103a8b + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103a8b 5 (.sib 7 (some 2) 0 (.d8 0x4)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x103a8b 5 (.sib 7 (some 2) 0 (.d8 0x4)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x103a8b (.sib 7 (some 2) 0 (.d8 0x4)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103a90 [0x41, 0x0F, 0x9D, 0xC1] (fun s => s.RIP = 0x103a90) (atFlags (condHolds 13) (setccR8Effect 0x103a90 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x103a90 4 9 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x103a90 13 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x103a94 [0x4C, 0x01, 0xC8] (fun s => s.RIP = 0x103a94) (addR64R64Effect 0x103a94 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103a94 0 9).toInstrSpec (add_r64_r64_effect_step 0x103a94 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103a97 [0x83, 0xFE, 0x05] (fun s => s.RIP = 0x103a97) (cmpR32Imm8Effect 0x103a97 3 6 0x5)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x103a97 3 6 0x5).toInstrSpec (cmp_r32_imm8_effect_step 0x103a97 0xfe 0x5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a8b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a90) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a94) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a97) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a9a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x103a9a 4 0x26) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103a88 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103a88 :=
  Rest.liftedBlock (rest_l103a88 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103a88 x hx)

theorem rest_l103a9c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103a9c bytes_l103a9c) (entryMap (live .l103a9c))
      6 0x103a9c bytes_l103a9c b_l103a9c := by
  have f0 : InstrSpec 0x103a9c [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x103a9c) (xorR32R32Effect 0x103a9c 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103a9c 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x103a9c 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103a9f [0x80, 0x7C, 0x17, 0x05, 0xC0] (LoadPre 0x103a9f (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x5)) s (0x103a9f + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103a9f 5 (.sib 7 (some 2) 0 (.d8 0x5)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x103a9f 5 (.sib 7 (some 2) 0 (.d8 0x5)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x103a9f (.sib 7 (some 2) 0 (.d8 0x5)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103aa4 [0x41, 0x0F, 0x9D, 0xC1] (fun s => s.RIP = 0x103aa4) (atFlags (condHolds 13) (setccR8Effect 0x103aa4 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x103aa4 4 9 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x103aa4 13 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x103aa8 [0x4C, 0x01, 0xC8] (fun s => s.RIP = 0x103aa8) (addR64R64Effect 0x103aa8 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103aa8 0 9).toInstrSpec (add_r64_r64_effect_step 0x103aa8 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103aab [0x83, 0xFE, 0x06] (fun s => s.RIP = 0x103aab) (cmpR32Imm8Effect 0x103aab 3 6 0x6)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x103aab 3 6 0x6).toInstrSpec (cmp_r32_imm8_effect_step 0x103aab 0xfe 0x6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103a9f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103aa4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103aa8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103aab) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103aae) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x103aae 4 0x12) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103a9c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103a9c :=
  Rest.liftedBlock (rest_l103a9c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103a9c x hx)

theorem rest_l103ab0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103ab0 bytes_l103ab0) (entryMap (live .l103ab0))
      5 0x103ab0 bytes_l103ab0 b_l103ab0 := by
  have f0 : InstrSpec 0x103ab0 [0x31, 0xF6] (fun s => s.RIP = 0x103ab0) (xorR32R32Effect 0x103ab0 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103ab0 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x103ab0 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x103ab2 [0x80, 0x7C, 0x17, 0x06, 0xC0] (LoadPre 0x103ab2 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x6)) s (0x103ab2 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103ab2 5 (.sib 7 (some 2) 0 (.d8 0x6)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x103ab2 5 (.sib 7 (some 2) 0 (.d8 0x6)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x103ab2 (.sib 7 (some 2) 0 (.d8 0x6)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103ab7 [0x40, 0x0F, 0x9D, 0xC6] (fun s => s.RIP = 0x103ab7) (atFlags (condHolds 13) (setccR8Effect 0x103ab7 4 6))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 6, .rip] :=
    (setccR8Effect_footprint 0x103ab7 4 6 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x103ab7 13 0x40 (by decide) 0xc6 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x103abb [0x48, 0x01, 0xF0] (fun s => s.RIP = 0x103abb) (addR64R64Effect 0x103abb 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103abb 0 6).toInstrSpec (add_r64_r64_effect_step 0x103abb 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ab2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ab7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103abb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103abe) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 62) (jmp_rel8_effect_step 0x103abe 0x2 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103ab0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103ab0 :=
  Rest.liftedBlock (rest_l103ab0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103ab0 x hx)

theorem rest_l103ac0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103ac0 bytes_l103ac0) (entryMap (live .l103ac0))
      1 0x103ac0 bytes_l103ac0 b_l103ac0 := by
  have f0 : InstrSpec 0x103ac0 [0x31, 0xC0] (fun s => s.RIP = 0x103ac0) (xorR32R32Effect 0x103ac0 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103ac0 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x103ac0 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ac2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l103ac0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103ac0 :=
  Rest.liftedBlock (rest_l103ac0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103ac0 x hx)

theorem rest_l103ac2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103ac2 bytes_l103ac2) (entryMap (live .l103ac2))
      5 0x103ac2 bytes_l103ac2 b_l103ac2 := by
  have f0 : InstrSpec 0x103ac2 [0x4C, 0x01, 0xC0] (fun s => s.RIP = 0x103ac2) (addR64R64Effect 0x103ac2 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103ac2 0 8).toInstrSpec (add_r64_r64_effect_step 0x103ac2 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103ac5 [0x49, 0xB8, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01] (fun s => s.RIP = 0x103ac5) (movR64Imm64Effect 0x103ac5 8 0x101010101010101)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x103ac5 8 0x101010101010101).toInstrSpec (mov_r64_imm64_effect_step 0x103ac5 0x49 0xb8 (by decide) (by decide) 0x101010101010101) pre_rip
  have f2 : InstrSpec 0x103acf [0x48, 0xBE, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00] (fun s => s.RIP = 0x103acf) (movR64Imm64Effect 0x103acf 6 0xff00ff00ff00ff)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x103acf 6 0xff00ff00ff00ff).toInstrSpec (mov_r64_imm64_effect_step 0x103acf 0x48 0xbe (by decide) (by decide) 0xff00ff00ff00ff) pre_rip
  have f3 : InstrSpec 0x103ad9 [0x48, 0xBA, 0x01, 0x00, 0x01, 0x00, 0x01, 0x00, 0x01, 0x00] (fun s => s.RIP = 0x103ad9) (movR64Imm64Effect 0x103ad9 2 0x1000100010001)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x103ad9 2 0x1000100010001).toInstrSpec (mov_r64_imm64_effect_step 0x103ad9 0x48 0xba (by decide) (by decide) 0x1000100010001) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ac5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (4, 4), (5, 5), (7, 7), (8, 55), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103acf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (4, 4), (5, 5), (6, 57), (7, 7), (8, 55), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ad9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 59), (4, 4), (5, 5), (6, 57), (7, 7), (8, 55), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ae3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 61) (jmp_rel8_effect_step 0x103ae3 0x3f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103ac2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103ac2 :=
  Rest.liftedBlock (rest_l103ac2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103ac2 x hx)

theorem rest_l103af0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103af0 bytes_l103af0) (entryMap (live .l103af0))
      1 0x103af0 bytes_l103af0 b_l103af0 := by
  have f0 : InstrSpec 0x103af0 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x103af0) (xorR32R32Effect 0x103af0 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103af0 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x103af0 0x45 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103af3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l103af0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103af0 :=
  Rest.liftedBlock (rest_l103af0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103af0 x hx)

theorem rest_l103af3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103af3 bytes_l103af3) (entryMap (live .l103af3))
      14 0x103af3 bytes_l103af3 b_l103af3 := by
  have f0 : InstrSpec 0x103af3 [0x4C, 0x01, 0xCF] (fun s => s.RIP = 0x103af3) (addR64R64Effect 0x103af3 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103af3 7 9).toInstrSpec (add_r64_r64_effect_step 0x103af3 0x4c 0xcf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103af6 [0x4C, 0x29, 0xD1] (fun s => s.RIP = 0x103af6) (subR64R64Effect 0x103af6 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x103af6 1 10).toInstrSpec (sub_r64_r64_effect_step 0x103af6 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103af9 [0x45, 0x89, 0xD3] (fun s => s.RIP = 0x103af9) (movR32R32Effect 0x103af9 3 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x103af9 3 11 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x103af9 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103afc [0x41, 0x83, 0xE3, 0x03] (fun s => s.RIP = 0x103afc) (andR32Imm8Effect 0x103afc 4 11 0x3)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x103afc 4 11 0x3).toInstrSpec (and_r32_imm8_rex_effect_step 0x103afc 0x41 0xe3 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103b00 [0x4C, 0x89, 0xF3] (fun s => s.RIP = 0x103b00) (movR64R64Effect 0x103b00 3 14)
      [.gpr 14] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x103b00 3 14).toInstrSpec (mov_r64_r64_effect_step 0x103b00 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103b03 [0x48, 0x21, 0xF3] (fun s => s.RIP = 0x103b03) (andR64R64Effect 0x103b03 3 6)
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103b03 3 6).toInstrSpec (and_r64_r64_effect_step 0x103b03 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x103b06 [0x49, 0xC1, 0xEE, 0x08] (fun s => s.RIP = 0x103b06) (shrR64Effect 0x103b06 4 14 8)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64Effect_footprint 0x103b06 4 14 8).toInstrSpec (shr_r64_imm8_effect_step 0x103b06 0x49 0xee 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103b0a [0x49, 0x21, 0xF6] (fun s => s.RIP = 0x103b0a) (andR64R64Effect 0x103b0a 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103b0a 14 6).toInstrSpec (and_r64_r64_effect_step 0x103b0a 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x103b0d [0x49, 0x01, 0xDE] (fun s => s.RIP = 0x103b0d) (addR64R64Effect 0x103b0d 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103b0d 14 3).toInstrSpec (add_r64_r64_effect_step 0x103b0d 0x49 0xde (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x103b10 [0x4C, 0x0F, 0xAF, 0xF2] (fun s => s.RIP = 0x103b10) (imulR64R64Effect 0x103b10 4 14 2)
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x103b10 4 14 2).toInstrSpec (imul_r64_r64_effect_step 0x103b10 0x4c (by decide) 0xf2 (by decide)) pre_rip
  have f10 : InstrSpec 0x103b14 [0x49, 0xC1, 0xEE, 0x30] (fun s => s.RIP = 0x103b14) (shrR64Effect 0x103b14 4 14 48)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64Effect_footprint 0x103b14 4 14 48).toInstrSpec (shr_r64_imm8_effect_step 0x103b14 0x49 0xee 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x103b18 [0x4C, 0x01, 0xF0] (fun s => s.RIP = 0x103b18) (addR64R64Effect 0x103b18 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103b18 0 14).toInstrSpec (add_r64_r64_effect_step 0x103b18 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x103b1b [0x4D, 0x85, 0xDB] (fun s => s.RIP = 0x103b1b) (testR64R64Effect 0x103b1b 11 11)
      [.gpr 11, .gpr 11] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x103b1b 11 11).toInstrSpec (test_r64_r64_effect_step 0x103b1b 0x4d 0xdb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103af6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103af9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 57), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103afc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b00) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 61), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b03) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b06) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b0a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b0d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b10) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b14) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b18) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b1b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 75), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 73), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b1e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 79) (jcc_rel32_effect_step 0x103b1e 5 0xb5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103af3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103af3 :=
  Rest.liftedBlock (rest_l103af3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103af3 x hx)

theorem rest_l103b24 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103b24 bytes_l103b24) (entryMap (live .l103b24))
      2 0x103b24 bytes_l103b24 b_l103b24 := by
  have f0 : InstrSpec 0x103b24 [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x103b24) (testR64R64Effect 0x103b24 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x103b24 1 1).toInstrSpec (test_r64_r64_effect_step 0x103b24 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b27) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x103b27 4 0x12d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103b24 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103b24 :=
  Rest.liftedBlock (rest_l103b24 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103b24 x hx)

theorem rest_l103b2d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103b2d bytes_l103b2d) (entryMap (live .l103b2d))
      8 0x103b2d bytes_l103b2d b_l103b2d := by
  have f0 : InstrSpec 0x103b2d [0x49, 0x89, 0xF9] (fun s => s.RIP = 0x103b2d) (movR64R64Effect 0x103b2d 9 7)
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x103b2d 9 7).toInstrSpec (mov_r64_r64_effect_step 0x103b2d 0x49 0xf9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103b30 [0x48, 0x81, 0xF9, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103b30) (cmpR64Imm32Effect 0x103b30 1 0xc0)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm32Effect_footprint 0x103b30 1 0xc0).toInstrSpec (cmp_r64_imm32_effect_step 0x103b30 0x48 0xf9 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103b37 [0x41, 0xBA, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103b37) (movR32Imm32Effect 0x103b37 6 10 0xc0)
      [] [] [.reg 10, .rip] :=
    (movR32Imm32Effect_footprint 0x103b37 6 10 0xc0).toInstrSpec (mov_r32_imm32_rex_effect_step 0x103b37 0x41 0xba (by decide) (by decide) 0xc0) pre_rip
  have f3 : InstrSpec 0x103b3d [0x4C, 0x0F, 0x42, 0xD1] (fun s => s.RIP = 0x103b3d) (atFlags (condHolds 2) (cmovR64R64Effect 0x103b3d 4 10 1))
      [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .rip] :=
    (cmovR64R64Effect_footprint 0x103b3d 4 10 1 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x103b3d 2 0x4c (by decide) 0xd1 (by decide) c)) pre_rip
  have f4 : InstrSpec 0x103b41 [0x42, 0x8D, 0x3C, 0xD5, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103b41) (leaR32Effect 0x103b41 8 7 (.abs (some 10) 3 0x0))
      [.gpr 10] [] [.reg 7, .rip] :=
    (leaR32Effect_footprint 0x103b41 8 7 (.abs (some 10) 3 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x103b41 0x42 (by decide) 7 (.abs (some 10) 3 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103b49 [0x41, 0x89, 0xFB] (fun s => s.RIP = 0x103b49) (movR32R32Effect 0x103b49 3 11 7)
      [.gpr 7] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x103b49 3 11 7).toInstrSpec (mov_r32_r32_rex_effect_step 0x103b49 0x41 0xfb (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x103b4c [0x41, 0x81, 0xE3, 0xE0, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x103b4c) (andR32Imm32Effect 0x103b4c 7 11 0x7e0)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x103b4c 7 11 0x7e0).toInstrSpec (and_r32_imm32_rex_effect_step 0x103b4c 0x41 0xe3 0x7e0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b30) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (14, 14), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b37) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 57), (14, 14), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b3d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 59), (14, 14), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b41) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 53), (10, 59), (14, 14), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b49) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 53), (10, 59), (11, 63), (14, 14), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b4c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 53), (10, 59), (11, 65), (14, 14), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b53) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 68) (jcc_rel8_effect_step 0x103b53 4 0x9b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103b2d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103b2d :=
  Rest.liftedBlock (rest_l103b2d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103b2d x hx)

theorem rest_l103b55 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103b55 bytes_l103b55) (entryMap (live .l103b55))
      4 0x103b55 bytes_l103b55 b_l103b55 := by
  have f0 : InstrSpec 0x103b55 [0x4D, 0x01, 0xCB] (fun s => s.RIP = 0x103b55) (addR64R64Effect 0x103b55 11 9)
      [.gpr 11, .gpr 9] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103b55 11 9).toInstrSpec (add_r64_r64_effect_step 0x103b55 0x4d 0xcb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103b58 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x103b58) (xorR32R32Effect 0x103b58 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103b58 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x103b58 0x45 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103b5b [0x4C, 0x89, 0xCB] (fun s => s.RIP = 0x103b5b) (movR64R64Effect 0x103b5b 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x103b5b 3 9).toInstrSpec (mov_r64_r64_effect_step 0x103b5b 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103b5e [0x66, 0x90] (fun s => s.RIP = 0x103b5e) (fun _ => nopEffect 0x103b5e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x103b5e 2).toInstrSpec (nop_66_effect_step 0x103b5e) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b58) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b5b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b5e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b60) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l103b55 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103b55 :=
  Rest.liftedBlock (rest_l103b55 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103b55 x hx)

theorem rest_l103b60_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x103b60 bytes_l103b60) [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 91), (14, 89), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]
      15 0x103ba4 bytes_l103b60_1 b_l103b60_1 := by
  have f20 : InstrSpec 0x103ba4 [0x4D, 0x09, 0xF5] (fun s => s.RIP = 0x103ba4) (orR64R64Effect 0x103ba4 13 14)
      [.gpr 13, .gpr 14] [] [.reg 13, .flags, .rip] :=
    (orR64R64Effect_footprint 0x103ba4 13 14).toInstrSpec (or_r64_r64_effect_step 0x103ba4 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x103ba7 [0x4D, 0x21, 0xC5] (fun s => s.RIP = 0x103ba7) (andR64R64Effect 0x103ba7 13 8)
      [.gpr 13, .gpr 8] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103ba7 13 8).toInstrSpec (and_r64_r64_effect_step 0x103ba7 0x4d 0xc5 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x103baa [0x4D, 0x01, 0xE5] (fun s => s.RIP = 0x103baa) (addR64R64Effect 0x103baa 13 12)
      [.gpr 13, .gpr 12] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103baa 13 12).toInstrSpec (add_r64_r64_effect_step 0x103baa 0x4d 0xe5 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x103bad [0x4D, 0x01, 0xFD] (fun s => s.RIP = 0x103bad) (addR64R64Effect 0x103bad 13 15)
      [.gpr 13, .gpr 15] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103bad 13 15).toInstrSpec (add_r64_r64_effect_step 0x103bad 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x103bb0 [0x4C, 0x8B, 0x73, 0x18] (LoadPre 0x103bb0 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x103bb0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103bb0 14 (.base 3 (.d8 0x18)))
      [.gpr 3] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x103bb0 14 (.base 3 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x103bb0 0x4c (by decide) 6 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x103bb4 [0x4D, 0x89, 0xF7] (fun s => s.RIP = 0x103bb4) (movR64R64Effect 0x103bb4 15 14)
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x103bb4 15 14).toInstrSpec (mov_r64_r64_effect_step 0x103bb4 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x103bb7 [0x49, 0xF7, 0xD7] (fun s => s.RIP = 0x103bb7) (notR64Effect 0x103bb7 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (notR64Effect_footprint 0x103bb7 15).toInstrSpec (not_r64_effect_step 0x103bb7 0x49 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x103bba [0x49, 0xC1, 0xEF, 0x07] (fun s => s.RIP = 0x103bba) (shrR64Effect 0x103bba 4 15 7)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x103bba 4 15 7).toInstrSpec (shr_r64_imm8_effect_step 0x103bba 0x49 0xef 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x103bbe [0x49, 0xC1, 0xEE, 0x06] (fun s => s.RIP = 0x103bbe) (shrR64Effect 0x103bbe 4 14 6)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64Effect_footprint 0x103bbe 4 14 6).toInstrSpec (shr_r64_imm8_effect_step 0x103bbe 0x49 0xee 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x103bc2 [0x4D, 0x09, 0xFE] (fun s => s.RIP = 0x103bc2) (orR64R64Effect 0x103bc2 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (orR64R64Effect_footprint 0x103bc2 14 15).toInstrSpec (or_r64_r64_effect_step 0x103bc2 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x103bc5 [0x4D, 0x21, 0xC6] (fun s => s.RIP = 0x103bc5) (andR64R64Effect 0x103bc5 14 8)
      [.gpr 14, .gpr 8] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103bc5 14 8).toInstrSpec (and_r64_r64_effect_step 0x103bc5 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x103bc8 [0x4D, 0x01, 0xEE] (fun s => s.RIP = 0x103bc8) (addR64R64Effect 0x103bc8 14 13)
      [.gpr 14, .gpr 13] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103bc8 14 13).toInstrSpec (add_r64_r64_effect_step 0x103bc8 0x4d 0xee (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x103bcb [0x48, 0x83, 0xC3, 0x20] (fun s => s.RIP = 0x103bcb) (addR64Imm8Effect 0x103bcb 3 0x20)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x103bcb 3 0x20).toInstrSpec (add_r64_imm8_effect_step 0x103bcb 0x48 0xc3 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x103bcf [0x4C, 0x39, 0xDB] (fun s => s.RIP = 0x103bcf) (cmpR64R64Effect 0x103bcf 3 11)
      [.gpr 3, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103bcf 3 11).toInstrSpec (cmp_r64_r64_effect_step 0x103bcf 0x4c 0xdb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 93), (14, 89), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ba7) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 95), (14, 89), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103baa) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 97), (14, 89), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bad) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 89), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bb0) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 101), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bb4) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 101), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bb7) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 101), (15, 105), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bba) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 101), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bbe) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 109), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bc2) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 111), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bc5) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 113), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bc8) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 115), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bcb) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 117), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 115), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bcf) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 117), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 115), (15, 107), (19, 119), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bd2) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 121) (jcc_rel8_effect_step 0x103bd2 5 0x8c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l103b60 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103b60 bytes_l103b60) (entryMap (live .l103b60))
      35 0x103b60 bytes_l103b60 b_l103b60 := by
  have f0 : InstrSpec 0x103b60 [0x4C, 0x8B, 0x3B] (LoadPre 0x103b60 (fun s => AddrMode.addr (.base 3 .none) s (0x103b60 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x103b60 15 (.base 3 .none))
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x103b60 15 (.base 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x103b60 0x4c (by decide) 7 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103b63 [0x4C, 0x8B, 0x63, 0x08] (LoadPre 0x103b63 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x103b63 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103b63 12 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x103b63 12 (.base 3 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x103b63 0x4c (by decide) 4 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103b67 [0x4D, 0x89, 0xFD] (fun s => s.RIP = 0x103b67) (movR64R64Effect 0x103b67 13 15)
      [.gpr 15] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x103b67 13 15).toInstrSpec (mov_r64_r64_effect_step 0x103b67 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103b6a [0x49, 0xF7, 0xD5] (fun s => s.RIP = 0x103b6a) (notR64Effect 0x103b6a 13)
      [.gpr 13] [] [.reg 13, .rip] :=
    (notR64Effect_footprint 0x103b6a 13).toInstrSpec (not_r64_effect_step 0x103b6a 0x49 0xd5 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103b6d [0x49, 0xC1, 0xED, 0x07] (fun s => s.RIP = 0x103b6d) (shrR64Effect 0x103b6d 4 13 7)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR64Effect_footprint 0x103b6d 4 13 7).toInstrSpec (shr_r64_imm8_effect_step 0x103b6d 0x49 0xed 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103b71 [0x49, 0xC1, 0xEF, 0x06] (fun s => s.RIP = 0x103b71) (shrR64Effect 0x103b71 4 15 6)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x103b71 4 15 6).toInstrSpec (shr_r64_imm8_effect_step 0x103b71 0x49 0xef 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x103b75 [0x4D, 0x09, 0xEF] (fun s => s.RIP = 0x103b75) (orR64R64Effect 0x103b75 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x103b75 15 13).toInstrSpec (or_r64_r64_effect_step 0x103b75 0x4d 0xef (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103b78 [0x4D, 0x21, 0xC7] (fun s => s.RIP = 0x103b78) (andR64R64Effect 0x103b78 15 8)
      [.gpr 15, .gpr 8] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103b78 15 8).toInstrSpec (and_r64_r64_effect_step 0x103b78 0x4d 0xc7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x103b7b [0x4D, 0x01, 0xF7] (fun s => s.RIP = 0x103b7b) (addR64R64Effect 0x103b7b 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103b7b 15 14).toInstrSpec (add_r64_r64_effect_step 0x103b7b 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x103b7e [0x4D, 0x89, 0xE6] (fun s => s.RIP = 0x103b7e) (movR64R64Effect 0x103b7e 14 12)
      [.gpr 12] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103b7e 14 12).toInstrSpec (mov_r64_r64_effect_step 0x103b7e 0x4d 0xe6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x103b81 [0x49, 0xF7, 0xD6] (fun s => s.RIP = 0x103b81) (notR64Effect 0x103b81 14)
      [.gpr 14] [] [.reg 14, .rip] :=
    (notR64Effect_footprint 0x103b81 14).toInstrSpec (not_r64_effect_step 0x103b81 0x49 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x103b84 [0x49, 0xC1, 0xEE, 0x07] (fun s => s.RIP = 0x103b84) (shrR64Effect 0x103b84 4 14 7)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64Effect_footprint 0x103b84 4 14 7).toInstrSpec (shr_r64_imm8_effect_step 0x103b84 0x49 0xee 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x103b88 [0x49, 0xC1, 0xEC, 0x06] (fun s => s.RIP = 0x103b88) (shrR64Effect 0x103b88 4 12 6)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR64Effect_footprint 0x103b88 4 12 6).toInstrSpec (shr_r64_imm8_effect_step 0x103b88 0x49 0xec 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x103b8c [0x4D, 0x09, 0xF4] (fun s => s.RIP = 0x103b8c) (orR64R64Effect 0x103b8c 12 14)
      [.gpr 12, .gpr 14] [] [.reg 12, .flags, .rip] :=
    (orR64R64Effect_footprint 0x103b8c 12 14).toInstrSpec (or_r64_r64_effect_step 0x103b8c 0x4d 0xf4 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x103b8f [0x4D, 0x21, 0xC4] (fun s => s.RIP = 0x103b8f) (andR64R64Effect 0x103b8f 12 8)
      [.gpr 12, .gpr 8] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103b8f 12 8).toInstrSpec (and_r64_r64_effect_step 0x103b8f 0x4d 0xc4 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x103b92 [0x4C, 0x8B, 0x6B, 0x10] (LoadPre 0x103b92 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x103b92 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103b92 13 (.base 3 (.d8 0x10)))
      [.gpr 3] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x103b92 13 (.base 3 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x103b92 0x4c (by decide) 5 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x103b96 [0x4D, 0x89, 0xEE] (fun s => s.RIP = 0x103b96) (movR64R64Effect 0x103b96 14 13)
      [.gpr 13] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103b96 14 13).toInstrSpec (mov_r64_r64_effect_step 0x103b96 0x4d 0xee (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x103b99 [0x49, 0xF7, 0xD6] (fun s => s.RIP = 0x103b99) (notR64Effect 0x103b99 14)
      [.gpr 14] [] [.reg 14, .rip] :=
    (notR64Effect_footprint 0x103b99 14).toInstrSpec (not_r64_effect_step 0x103b99 0x49 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x103b9c [0x49, 0xC1, 0xEE, 0x07] (fun s => s.RIP = 0x103b9c) (shrR64Effect 0x103b9c 4 14 7)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64Effect_footprint 0x103b9c 4 14 7).toInstrSpec (shr_r64_imm8_effect_step 0x103b9c 0x49 0xee 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x103ba0 [0x49, 0xC1, 0xED, 0x06] (fun s => s.RIP = 0x103ba0) (shrR64Effect 0x103ba0 4 13 6)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR64Effect_footprint 0x103ba0 4 13 6).toInstrSpec (shr_r64_imm8_effect_step 0x103ba0 0x49 0xed 0x6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b63) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b67) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b6a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 59), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b6d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b71) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b75) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b78) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 14), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b7b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b7e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b81) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b84) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 75), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b88) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 61), (14, 75), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b8c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 79), (13, 61), (14, 75), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b8f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 61), (14, 75), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b92) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 83), (14, 75), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b96) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 83), (14, 85), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b99) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 83), (14, 87), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103b9c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 83), (14, 89), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ba0) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 91), (14, 89), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ba4) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l103b60_1 code

theorem block_l103b60 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103b60 :=
  Rest.liftedBlock (rest_l103b60 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103b60 x hx)

theorem rest_l103bd4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103bd4 bytes_l103bd4) (entryMap (live .l103bd4))
      1 0x103bd4 bytes_l103bd4 b_l103bd4 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x103bd4 0xffffff1a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103bd4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103bd4 :=
  Rest.liftedBlock (rest_l103bd4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103bd4 x hx)

theorem rest_l103bd9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103bd9 bytes_l103bd9) (entryMap (live .l103bd9))
      11 0x103bd9 bytes_l103bd9 b_l103bd9 := by
  have f0 : InstrSpec 0x103bd9 [0x41, 0x81, 0xE2, 0xFC, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103bd9) (andR32Imm32Effect 0x103bd9 7 10 0xfc)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x103bd9 7 10 0xfc).toInstrSpec (and_r32_imm32_rex_effect_step 0x103bd9 0x41 0xe2 0xfc (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103be0 [0x44, 0x89, 0xD1] (fun s => s.RIP = 0x103be0) (movR32R32Effect 0x103be0 3 1 10)
      [.gpr 10] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x103be0 3 1 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x103be0 0x44 0xd1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103be3 [0x49, 0x8B, 0x0C, 0xC9] (LoadPre 0x103be3 (fun s => AddrMode.addr (.sib 9 (some 1) 3 .none) s (0x103be3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103be3 1 (.sib 9 (some 1) 3 .none))
      [.gpr 9, .gpr 1] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x103be3 1 (.sib 9 (some 1) 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x103be3 0x49 (by decide) 1 (.sib 9 (some 1) 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x103be7 [0x48, 0x89, 0xCF] (fun s => s.RIP = 0x103be7) (movR64R64Effect 0x103be7 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103be7 7 1).toInstrSpec (mov_r64_r64_effect_step 0x103be7 0x48 0xcf (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103bea [0x48, 0xF7, 0xD7] (fun s => s.RIP = 0x103bea) (notR64Effect 0x103bea 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (notR64Effect_footprint 0x103bea 7).toInstrSpec (not_r64_effect_step 0x103bea 0x48 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103bed [0x48, 0xC1, 0xEF, 0x07] (fun s => s.RIP = 0x103bed) (shrR64Effect 0x103bed 4 7 7)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x103bed 4 7 7).toInstrSpec (shr_r64_imm8_effect_step 0x103bed 0x48 0xef 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x103bf1 [0x48, 0xC1, 0xE9, 0x06] (fun s => s.RIP = 0x103bf1) (shrR64Effect 0x103bf1 4 1 6)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x103bf1 4 1 6).toInstrSpec (shr_r64_imm8_effect_step 0x103bf1 0x48 0xe9 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103bf5 [0x48, 0x09, 0xF9] (fun s => s.RIP = 0x103bf5) (orR64R64Effect 0x103bf5 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x103bf5 1 7).toInstrSpec (or_r64_r64_effect_step 0x103bf5 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x103bf8 [0x4C, 0x21, 0xC1] (fun s => s.RIP = 0x103bf8) (andR64R64Effect 0x103bf8 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103bf8 1 8).toInstrSpec (and_r64_r64_effect_step 0x103bf8 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x103bfb [0x41, 0x83, 0xFB, 0x01] (fun s => s.RIP = 0x103bfb) (cmpR32Imm8Effect 0x103bfb 4 11 0x1)
      [.gpr 11] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x103bfb 4 11 0x1).toInstrSpec (cmp_r32_imm8_rex_effect_step 0x103bfb 0x41 0xfb 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103be0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103be3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103be7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bea) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bed) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bf1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bf5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bf8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bfb) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 69), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 53), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103bff) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 73) (jcc_rel8_effect_step 0x103bff 4 0x3e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103bd9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103bd9 :=
  Rest.liftedBlock (rest_l103bd9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103bd9 x hx)

theorem rest_l103c01 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103c01 bytes_l103c01) (entryMap (live .l103c01))
      10 0x103c01 bytes_l103c01 b_l103c01 := by
  have f0 : InstrSpec 0x103c01 [0x4B, 0x8B, 0x7C, 0xD1, 0x08] (LoadPre 0x103c01 (fun s => AddrMode.addr (.sib 9 (some 10) 3 (.d8 0x8)) s (0x103c01 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103c01 7 (.sib 9 (some 10) 3 (.d8 0x8)))
      [.gpr 9, .gpr 10] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103c01 7 (.sib 9 (some 10) 3 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x103c01 0x4b (by decide) 7 (.sib 9 (some 10) 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103c06 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x103c06) (movR64R64Effect 0x103c06 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x103c06 3 7).toInstrSpec (mov_r64_r64_effect_step 0x103c06 0x48 0xfb (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103c09 [0x48, 0xF7, 0xD3] (fun s => s.RIP = 0x103c09) (notR64Effect 0x103c09 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (notR64Effect_footprint 0x103c09 3).toInstrSpec (not_r64_effect_step 0x103c09 0x48 0xd3 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103c0c [0x48, 0xC1, 0xEB, 0x07] (fun s => s.RIP = 0x103c0c) (shrR64Effect 0x103c0c 4 3 7)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x103c0c 4 3 7).toInstrSpec (shr_r64_imm8_effect_step 0x103c0c 0x48 0xeb 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103c10 [0x48, 0xC1, 0xEF, 0x06] (fun s => s.RIP = 0x103c10) (shrR64Effect 0x103c10 4 7 6)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x103c10 4 7 6).toInstrSpec (shr_r64_imm8_effect_step 0x103c10 0x48 0xef 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103c14 [0x48, 0x09, 0xDF] (fun s => s.RIP = 0x103c14) (orR64R64Effect 0x103c14 7 3)
      [.gpr 7, .gpr 3] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x103c14 7 3).toInstrSpec (or_r64_r64_effect_step 0x103c14 0x48 0xdf (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x103c17 [0x4C, 0x21, 0xC7] (fun s => s.RIP = 0x103c17) (andR64R64Effect 0x103c17 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103c17 7 8).toInstrSpec (and_r64_r64_effect_step 0x103c17 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103c1a [0x48, 0x01, 0xF9] (fun s => s.RIP = 0x103c1a) (addR64R64Effect 0x103c1a 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103c1a 1 7).toInstrSpec (add_r64_r64_effect_step 0x103c1a 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x103c1d [0x41, 0x83, 0xFB, 0x02] (fun s => s.RIP = 0x103c1d) (cmpR32Imm8Effect 0x103c1d 4 11 0x2)
      [.gpr 11] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x103c1d 4 11 0x2).toInstrSpec (cmp_r32_imm8_rex_effect_step 0x103c1d 0x41 0xfb 0x2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c06) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c09) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c0c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c10) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c14) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c17) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c1a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c1d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 67), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c21) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel8_effect_step 0x103c21 4 0x1c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103c01 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103c01 :=
  Rest.liftedBlock (rest_l103c01 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103c01 x hx)

theorem rest_l103c23 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103c23 bytes_l103c23) (entryMap (live .l103c23))
      8 0x103c23 bytes_l103c23 b_l103c23 := by
  have f0 : InstrSpec 0x103c23 [0x4B, 0x8B, 0x7C, 0xD1, 0x10] (LoadPre 0x103c23 (fun s => AddrMode.addr (.sib 9 (some 10) 3 (.d8 0x10)) s (0x103c23 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103c23 7 (.sib 9 (some 10) 3 (.d8 0x10)))
      [.gpr 9, .gpr 10] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103c23 7 (.sib 9 (some 10) 3 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x103c23 0x4b (by decide) 7 (.sib 9 (some 10) 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103c28 [0x49, 0x89, 0xF9] (fun s => s.RIP = 0x103c28) (movR64R64Effect 0x103c28 9 7)
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x103c28 9 7).toInstrSpec (mov_r64_r64_effect_step 0x103c28 0x49 0xf9 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103c2b [0x49, 0xF7, 0xD1] (fun s => s.RIP = 0x103c2b) (notR64Effect 0x103c2b 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (notR64Effect_footprint 0x103c2b 9).toInstrSpec (not_r64_effect_step 0x103c2b 0x49 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103c2e [0x49, 0xC1, 0xE9, 0x07] (fun s => s.RIP = 0x103c2e) (shrR64Effect 0x103c2e 4 9 7)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x103c2e 4 9 7).toInstrSpec (shr_r64_imm8_effect_step 0x103c2e 0x49 0xe9 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103c32 [0x48, 0xC1, 0xEF, 0x06] (fun s => s.RIP = 0x103c32) (shrR64Effect 0x103c32 4 7 6)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x103c32 4 7 6).toInstrSpec (shr_r64_imm8_effect_step 0x103c32 0x48 0xef 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103c36 [0x4C, 0x09, 0xCF] (fun s => s.RIP = 0x103c36) (orR64R64Effect 0x103c36 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x103c36 7 9).toInstrSpec (or_r64_r64_effect_step 0x103c36 0x4c 0xcf (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x103c39 [0x4C, 0x21, 0xC7] (fun s => s.RIP = 0x103c39) (andR64R64Effect 0x103c39 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103c39 7 8).toInstrSpec (and_r64_r64_effect_step 0x103c39 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103c3c [0x48, 0x01, 0xF9] (fun s => s.RIP = 0x103c3c) (addR64R64Effect 0x103c3c 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103c3c 1 7).toInstrSpec (add_r64_r64_effect_step 0x103c3c 0x48 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c28) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c2b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 57), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c2e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 59), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c32) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 59), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c36) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 59), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c39) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 59), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c3c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 59), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c3f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 69) (by decide) rfl

theorem block_l103c23 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103c23 :=
  Rest.liftedBlock (rest_l103c23 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103c23 x hx)

theorem rest_l103c3f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103c3f bytes_l103c3f) (entryMap (live .l103c3f))
      8 0x103c3f bytes_l103c3f b_l103c3f := by
  have f0 : InstrSpec 0x103c3f [0x48, 0x89, 0xCF] (fun s => s.RIP = 0x103c3f) (movR64R64Effect 0x103c3f 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103c3f 7 1).toInstrSpec (mov_r64_r64_effect_step 0x103c3f 0x48 0xcf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103c42 [0x48, 0x21, 0xF7] (fun s => s.RIP = 0x103c42) (andR64R64Effect 0x103c42 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103c42 7 6).toInstrSpec (and_r64_r64_effect_step 0x103c42 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103c45 [0x48, 0xC1, 0xE9, 0x08] (fun s => s.RIP = 0x103c45) (shrR64Effect 0x103c45 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x103c45 4 1 8).toInstrSpec (shr_r64_imm8_effect_step 0x103c45 0x48 0xe9 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103c49 [0x48, 0x21, 0xF1] (fun s => s.RIP = 0x103c49) (andR64R64Effect 0x103c49 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103c49 1 6).toInstrSpec (and_r64_r64_effect_step 0x103c49 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103c4c [0x48, 0x01, 0xF9] (fun s => s.RIP = 0x103c4c) (addR64R64Effect 0x103c4c 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103c4c 1 7).toInstrSpec (add_r64_r64_effect_step 0x103c4c 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103c4f [0x48, 0x0F, 0xAF, 0xCA] (fun s => s.RIP = 0x103c4f) (imulR64R64Effect 0x103c4f 4 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x103c4f 4 1 2).toInstrSpec (imul_r64_r64_effect_step 0x103c4f 0x48 (by decide) 0xca (by decide)) pre_rip
  have f6 : InstrSpec 0x103c53 [0x48, 0xC1, 0xE9, 0x30] (fun s => s.RIP = 0x103c53) (shrR64Effect 0x103c53 4 1 48)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x103c53 4 1 48).toInstrSpec (shr_r64_imm8_effect_step 0x103c53 0x48 0xe9 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103c57 [0x48, 0x01, 0xC8] (fun s => s.RIP = 0x103c57) (addR64R64Effect 0x103c57 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103c57 0 1).toInstrSpec (add_r64_r64_effect_step 0x103c57 0x48 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c42) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c45) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c49) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c4c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c4f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c53) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c57) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 65), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c5a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 69) (by decide) rfl

theorem block_l103c3f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103c3f :=
  Rest.liftedBlock (rest_l103c3f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103c3f x hx)

theorem rest_l103c5a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103c5a bytes_l103c5a) (entryMap (live .l103c5a))
      6 0x103c5a bytes_l103c5a b_l103c5a := by
  have f0 : InstrSpec 0x103c5a [0x5B] (PopPre 0x103c5a) (popR64Effect 0x103c5a 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103c5a 1 3).toInstrSpec (pop_r64_effect_step 0x103c5a 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x103c5b [0x41, 0x5C] (PopPre 0x103c5b) (popR64Effect 0x103c5b 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103c5b 2 12).toInstrSpec (pop_r64_rex_effect_step 0x103c5b 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x103c5d [0x41, 0x5D] (PopPre 0x103c5d) (popR64Effect 0x103c5d 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103c5d 2 13).toInstrSpec (pop_r64_rex_effect_step 0x103c5d 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x103c5f [0x41, 0x5E] (PopPre 0x103c5f) (popR64Effect 0x103c5f 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103c5f 2 14).toInstrSpec (pop_r64_rex_effect_step 0x103c5f 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x103c61 [0x41, 0x5F] (PopPre 0x103c61) (popR64Effect 0x103c61 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103c61 2 15).toInstrSpec (pop_r64_rex_effect_step 0x103c61 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x103c63 [0xC3] (RetPre 0x103c63) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x103c63).toInstrSpec (ret_effect_step 0x103c63) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c5b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c5d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c5f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 59), (14, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c61) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 59), (14, 62), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103c63) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 59), (14, 62), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l103c5a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103c5a :=
  Rest.liftedBlock (rest_l103c5a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103c5a x hx)

section Steps

variable (code : CodeMap)
    (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64)
    (cf pf af zf sf of : Bool) (df : BitVec 1)
    (xmm0 xmm1 xmm2 xmm3 xmm4 xmm5 xmm6 xmm7 xmm8 xmm9 xmm10 xmm11 xmm12 xmm13 xmm14 xmm15 : BitVec 128)
    (mxcsr : BitVec 32) (st0 st1 st2 st3 st4 st5 st6 st7 : BitVec 80) (fsw : BitVec 16)
    (fcc : BitVec 4) (ftw fcw : BitVec 16) (fpuPtr : BitVec 171) (mem : Ram)

set_option hygiene false in
local notation "args" =>
  (#v[⟨64, rax⟩, ⟨64, rcx⟩, ⟨64, rdx⟩, ⟨64, rbx⟩, ⟨64, rsp⟩, ⟨64, rbp⟩, ⟨64, rsi⟩, ⟨64, rdi⟩, ⟨64, r8⟩, ⟨64, r9⟩, ⟨64, r10⟩, ⟨64, r11⟩, ⟨64, r12⟩, ⟨64, r13⟩, ⟨64, r14⟩, ⟨64, r15⟩] : Vector Value 16) ++
  (#v[.ofBool cf, .ofBool pf, .ofBool af, .ofBool zf, .ofBool sf, .ofBool of, ⟨1, df⟩] : Vector Value 7) ++
  (#v[⟨128, xmm0⟩, ⟨128, xmm1⟩, ⟨128, xmm2⟩, ⟨128, xmm3⟩, ⟨128, xmm4⟩, ⟨128, xmm5⟩, ⟨128, xmm6⟩, ⟨128, xmm7⟩, ⟨128, xmm8⟩, ⟨128, xmm9⟩, ⟨128, xmm10⟩, ⟨128, xmm11⟩, ⟨128, xmm12⟩, ⟨128, xmm13⟩, ⟨128, xmm14⟩, ⟨128, xmm15⟩, ⟨32, mxcsr⟩, ⟨80, st0⟩, ⟨80, st1⟩, ⟨80, st2⟩, ⟨80, st3⟩, ⟨80, st4⟩, ⟨80, st5⟩, ⟨80, st6⟩, ⟨80, st7⟩, ⟨16, fsw⟩, ⟨4, fcc⟩, ⟨16, ftw⟩, ⟨16, fcw⟩, ⟨171, fpuPtr⟩] : Vector Value 30)

theorem_by block_l1038b0_eval :
    program.runBlock (dialect code) ⟨.l1038b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1038c6_eval :
    program.runBlock (dialect code) ⟨.l1038c6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1038cb_eval :
    program.runBlock (dialect code) ⟨.l1038cb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1038d6_eval :
    program.runBlock (dialect code) ⟨.l1038d6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1038df_eval :
    program.runBlock (dialect code) ⟨.l1038df, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1038e8_eval :
    program.runBlock (dialect code) ⟨.l1038e8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1038fb_eval :
    program.runBlock (dialect code) ⟨.l1038fb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103903_eval :
    program.runBlock (dialect code) ⟨.l103903, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10391a_eval :
    program.runBlock (dialect code) ⟨.l10391a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103925_eval :
    program.runBlock (dialect code) ⟨.l103925, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103928_eval :
    program.runBlock (dialect code) ⟨.l103928, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103930_eval :
    program.runBlock (dialect code) ⟨.l103930, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103970_eval :
    program.runBlock (dialect code) ⟨.l103970, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103975_eval :
    program.runBlock (dialect code) ⟨.l103975, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103980_eval :
    program.runBlock (dialect code) ⟨.l103980, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103995_eval :
    program.runBlock (dialect code) ⟨.l103995, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103996_eval :
    program.runBlock (dialect code) ⟨.l103996, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1039b0_eval :
    program.runBlock (dialect code) ⟨.l1039b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1039f6_eval :
    program.runBlock (dialect code) ⟨.l1039f6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1039fb_eval :
    program.runBlock (dialect code) ⟨.l1039fb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103a10_eval :
    program.runBlock (dialect code) ⟨.l103a10, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103a25_eval :
    program.runBlock (dialect code) ⟨.l103a25, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103a31_eval :
    program.runBlock (dialect code) ⟨.l103a31, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103a4c_eval :
    program.runBlock (dialect code) ⟨.l103a4c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103a60_eval :
    program.runBlock (dialect code) ⟨.l103a60, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103a74_eval :
    program.runBlock (dialect code) ⟨.l103a74, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103a88_eval :
    program.runBlock (dialect code) ⟨.l103a88, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103a9c_eval :
    program.runBlock (dialect code) ⟨.l103a9c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103ab0_eval :
    program.runBlock (dialect code) ⟨.l103ab0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103ac0_eval :
    program.runBlock (dialect code) ⟨.l103ac0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103ac2_eval :
    program.runBlock (dialect code) ⟨.l103ac2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103af0_eval :
    program.runBlock (dialect code) ⟨.l103af0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103af3_eval :
    program.runBlock (dialect code) ⟨.l103af3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103b24_eval :
    program.runBlock (dialect code) ⟨.l103b24, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103b2d_eval :
    program.runBlock (dialect code) ⟨.l103b2d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103b55_eval :
    program.runBlock (dialect code) ⟨.l103b55, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103b60_eval :
    program.runBlock (dialect code) ⟨.l103b60, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103bd4_eval :
    program.runBlock (dialect code) ⟨.l103bd4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103bd9_eval :
    program.runBlock (dialect code) ⟨.l103bd9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103c01_eval :
    program.runBlock (dialect code) ⟨.l103c01, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103c23_eval :
    program.runBlock (dialect code) ⟨.l103c23, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103c3f_eval :
    program.runBlock (dialect code) ⟨.l103c3f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103c5a_eval :
    program.runBlock (dialect code) ⟨.l103c5a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
