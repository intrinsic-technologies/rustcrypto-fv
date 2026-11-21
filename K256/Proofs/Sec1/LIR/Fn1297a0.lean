import K256.Proofs.Sec1.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Sec1.LIR.Generated.Values

namespace K256.Proofs.Sec1.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

theorem rest_l1297a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1297a0 bytes_l1297a0) (entryMap (live .l1297a0))
      7 0x1297a0 bytes_l1297a0 b_l1297a0 := by
  have f0 : InstrSpec 0x1297a0 [0x4C, 0x8D, 0x47, 0x07] (fun s => s.RIP = 0x1297a0) (leaR64Effect 0x1297a0 8 (.base 7 (.d8 0x7)))
      [.gpr 7] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x1297a0 8 (.base 7 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x1297a0 0x4c (by decide) 0 (.base 7 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1297a4 [0x49, 0x83, 0xE0, 0xF8] (fun s => s.RIP = 0x1297a4) (andR64Imm8Effect 0x1297a4 8 0xf8)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x1297a4 8 0xf8).toInstrSpec (and_r64_imm8_effect_step 0x1297a4 0x49 0xe0 0xf8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1297a8 [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x1297a8) (movR64R64Effect 0x1297a8 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1297a8 0 8).toInstrSpec (mov_r64_r64_effect_step 0x1297a8 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1297ab [0x48, 0x29, 0xF8] (fun s => s.RIP = 0x1297ab) (subR64R64Effect 0x1297ab 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1297ab 0 7).toInstrSpec (sub_r64_r64_effect_step 0x1297ab 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1297ae [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x1297ae) (movR64R64Effect 0x1297ae 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1297ae 2 6).toInstrSpec (mov_r64_r64_effect_step 0x1297ae 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1297b1 [0x48, 0x29, 0xC2] (fun s => s.RIP = 0x1297b1) (subR64R64Effect 0x1297b1 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1297b1 2 0).toInstrSpec (sub_r64_r64_effect_step 0x1297b1 0x48 0xc2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297a4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297a8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297ab) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297ae) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297b1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297b4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x1297b4 3 0x19) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1297a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1297a0 :=
  Rest.liftedBlock (rest_l1297a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1297a0 x hx)

theorem rest_l1297b6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1297b6 bytes_l1297b6) (entryMap (live .l1297b6))
      2 0x1297b6 bytes_l1297b6 b_l1297b6 := by
  have f0 : InstrSpec 0x1297b6 [0x48, 0x85, 0xF6] (fun s => s.RIP = 0x1297b6) (testR64R64Effect 0x1297b6 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1297b6 6 6).toInstrSpec (test_r64_r64_effect_step 0x1297b6 0x48 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297b9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1297b9 4 0x5a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1297b6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1297b6 :=
  Rest.liftedBlock (rest_l1297b6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1297b6 x hx)

theorem rest_l1297bb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1297bb bytes_l1297bb) (entryMap (live .l1297bb))
      4 0x1297bb bytes_l1297bb b_l1297bb := by
  have f0 : InstrSpec 0x1297bb [0x89, 0xF1] (fun s => s.RIP = 0x1297bb) (movR32R32Effect 0x1297bb 2 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1297bb 2 1 6).toInstrSpec (mov_r32_r32_effect_step 0x1297bb 0xf1 (by decide)) pre_rip
  have f1 : InstrSpec 0x1297bd [0x83, 0xE1, 0x03] (fun s => s.RIP = 0x1297bd) (andR32Imm8Effect 0x1297bd 3 1 0x3)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1297bd 3 1 0x3).toInstrSpec (and_r32_imm8_effect_step 0x1297bd 0xe1 0x3 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1297c0 [0x48, 0x83, 0xFE, 0x04] (fun s => s.RIP = 0x1297c0) (cmpR64Imm8Effect 0x1297c0 6 0x4)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1297c0 6 0x4).toInstrSpec (cmp_r64_imm8_effect_step 0x1297c0 0x48 0xfe 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297bd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297c0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297c4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x1297c4 3 0x52) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1297bb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1297bb :=
  Rest.liftedBlock (rest_l1297bb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1297bb x hx)

theorem rest_l1297c6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1297c6 bytes_l1297c6) (entryMap (live .l1297c6))
      3 0x1297c6 bytes_l1297c6 b_l1297c6 := by
  have f0 : InstrSpec 0x1297c6 [0x31, 0xD2] (fun s => s.RIP = 0x1297c6) (xorR32R32Effect 0x1297c6 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1297c6 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x1297c6 0xd2 (by decide)) pre_rip
  have f1 : InstrSpec 0x1297c8 [0x31, 0xC0] (fun s => s.RIP = 0x1297c8) (xorR32R32Effect 0x1297c8 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1297c8 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x1297c8 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297c8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297ca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x1297ca 0x96 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1297c6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1297c6 :=
  Rest.liftedBlock (rest_l1297c6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1297c6 x hx)

theorem rest_l1297cf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1297cf bytes_l1297cf) (entryMap (live .l1297cf))
      3 0x1297cf bytes_l1297cf b_l1297cf := by
  have f0 : InstrSpec 0x1297cf [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x1297cf) (movR64R64Effect 0x1297cf 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1297cf 1 2).toInstrSpec (mov_r64_r64_effect_step 0x1297cf 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1297d2 [0x48, 0xC1, 0xE9, 0x03] (fun s => s.RIP = 0x1297d2) (shrR64Effect 0x1297d2 4 1 3)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1297d2 4 1 3).toInstrSpec (shr_r64_imm8_effect_step 0x1297d2 0x48 0xe9 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297d2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 56) f1 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x1297d2 4 1 3 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297d6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x1297d6 4 0xde) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1297cf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1297cf :=
  Rest.liftedBlock (rest_l1297cf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1297cf x hx)

theorem rest_l1297d8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1297d8 bytes_l1297d8) (entryMap (live .l1297d8))
      9 0x1297d8 bytes_l1297d8 b_l1297d8 := by
  have f0 : InstrSpec 0x1297d8 [0x41, 0x57] (PushPre 0x1297d8 2) (pushR64Effect 0x1297d8 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1297d8 2 15).toInstrSpec (push_r64_rex_effect_step 0x1297d8 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1297da [0x41, 0x56] (PushPre 0x1297da 2) (pushR64Effect 0x1297da 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1297da 2 14).toInstrSpec (push_r64_rex_effect_step 0x1297da 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1297dc [0x41, 0x55] (PushPre 0x1297dc 2) (pushR64Effect 0x1297dc 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1297dc 2 13).toInstrSpec (push_r64_rex_effect_step 0x1297dc 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1297de [0x41, 0x54] (PushPre 0x1297de 2) (pushR64Effect 0x1297de 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1297de 2 12).toInstrSpec (push_r64_rex_effect_step 0x1297de 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1297e0 [0x53] (PushPre 0x1297e0 1) (pushR64Effect 0x1297e0 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1297e0 1 3).toInstrSpec (push_r64_effect_step 0x1297e0 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1297e1 [0x89, 0xD6] (fun s => s.RIP = 0x1297e1) (movR32R32Effect 0x1297e1 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x1297e1 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x1297e1 0xd6 (by decide)) pre_rip
  have f6 : InstrSpec 0x1297e3 [0x83, 0xE6, 0x07] (fun s => s.RIP = 0x1297e3) (andR32Imm8Effect 0x1297e3 3 6 0x7)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1297e3 3 6 0x7).toInstrSpec (and_r32_imm8_effect_step 0x1297e3 0xe6 0x7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1297e6 [0x49, 0x39, 0xF8] (fun s => s.RIP = 0x1297e6) (cmpR64R64Effect 0x1297e6 8 7)
      [.gpr 8, .gpr 7] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1297e6 8 7).toInstrSpec (cmp_r64_r64_effect_step 0x1297e6 0x49 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297da) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297dc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297de) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297e0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297e1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297e3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 65), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297e6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 65), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297e9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel8_effect_step 0x1297e9 5 0x8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1297d8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1297d8 :=
  Rest.liftedBlock (rest_l1297d8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1297d8 x hx)

theorem rest_l1297eb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1297eb bytes_l1297eb) (entryMap (live .l1297eb))
      2 0x1297eb bytes_l1297eb b_l1297eb := by
  have f0 : InstrSpec 0x1297eb [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x1297eb) (xorR32R32Effect 0x1297eb 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1297eb 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1297eb 0x45 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297ee) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x1297ee 0x122 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1297eb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1297eb :=
  Rest.liftedBlock (rest_l1297eb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1297eb x hx)

theorem rest_l1297f3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1297f3 bytes_l1297f3) (entryMap (live .l1297f3))
      6 0x1297f3 bytes_l1297f3 b_l1297f3 := by
  have f0 : InstrSpec 0x1297f3 [0x41, 0x89, 0xC1] (fun s => s.RIP = 0x1297f3) (movR32R32Effect 0x1297f3 3 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x1297f3 3 9 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x1297f3 0x41 0xc1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1297f6 [0x41, 0x83, 0xE1, 0x03] (fun s => s.RIP = 0x1297f6) (andR32Imm8Effect 0x1297f6 4 9 0x3)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1297f6 4 9 0x3).toInstrSpec (and_r32_imm8_rex_effect_step 0x1297f6 0x41 0xe1 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1297fa [0x49, 0x89, 0xFA] (fun s => s.RIP = 0x1297fa) (movR64R64Effect 0x1297fa 10 7)
      [.gpr 7] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1297fa 10 7).toInstrSpec (mov_r64_r64_effect_step 0x1297fa 0x49 0xfa (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1297fd [0x4D, 0x29, 0xC2] (fun s => s.RIP = 0x1297fd) (subR64R64Effect 0x1297fd 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1297fd 10 8).toInstrSpec (sub_r64_r64_effect_step 0x1297fd 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129800 [0x49, 0x83, 0xFA, 0xFC] (fun s => s.RIP = 0x129800) (cmpR64Imm8Effect 0x129800 10 0xfc)
      [.gpr 10] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x129800 10 0xfc).toInstrSpec (cmp_r64_imm8_effect_step 0x129800 0x49 0xfa 0xfc (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297f6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297fa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 57), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297fd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 59), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129800) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 59), (11, 11), (14, 14), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129804) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel32_effect_step 0x129804 6 0x7c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1297f3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1297f3 :=
  Rest.liftedBlock (rest_l1297f3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1297f3 x hx)

theorem rest_l12980a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12980a bytes_l12980a) (entryMap (live .l12980a))
      3 0x12980a bytes_l12980a b_l12980a := by
  have f0 : InstrSpec 0x12980a [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x12980a) (xorR32R32Effect 0x12980a 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12980a 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x12980a 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12980d [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x12980d) (xorR32R32Effect 0x12980d 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12980d 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x12980d 0x45 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12980d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 53), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129810) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x129810 0xd6 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12980a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12980a :=
  Rest.liftedBlock (rest_l12980a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12980a x hx)

theorem rest_l129815 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129815 bytes_l129815) (entryMap (live .l129815))
      2 0x129815 bytes_l129815 b_l129815 := by
  have f0 : InstrSpec 0x129815 [0x31, 0xC0] (fun s => s.RIP = 0x129815) (xorR32R32Effect 0x129815 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129815 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x129815 0xc0 (by decide)) pre_rip
  have f1 : InstrSpec 0x129817 [0xC3] (RetPre 0x129817) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x129817).toInstrSpec (ret_effect_step 0x129817) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129817) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 57) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f1 (by decide) rfl rfl rfl (by decide)

theorem block_l129815 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129815 :=
  Rest.liftedBlock (rest_l129815 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129815 x hx)

theorem rest_l129818 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129818 bytes_l129818) (entryMap (live .l129818))
      3 0x129818 bytes_l129818 b_l129818 := by
  have f0 : InstrSpec 0x129818 [0x48, 0x83, 0xE6, 0xFC] (fun s => s.RIP = 0x129818) (andR64Imm8Effect 0x129818 6 0xfc)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x129818 6 0xfc).toInstrSpec (and_r64_imm8_effect_step 0x129818 0x48 0xe6 0xfc (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12981c [0x31, 0xD2] (fun s => s.RIP = 0x12981c) (xorR32R32Effect 0x12981c 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12981c 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x12981c 0xd2 (by decide)) pre_rip
  have f2 : InstrSpec 0x12981e [0x31, 0xC0] (fun s => s.RIP = 0x12981e) (xorR32R32Effect 0x12981e 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12981e 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x12981e 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12981c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12981e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129820) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l129818 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129818 :=
  Rest.liftedBlock (rest_l129818 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129818 x hx)

theorem rest_l129820 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129820 bytes_l129820) (entryMap (live .l129820))
      19 0x129820 bytes_l129820 b_l129820 := by
  have f0 : InstrSpec 0x129820 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x129820) (xorR32R32Effect 0x129820 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129820 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x129820 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129823 [0x80, 0x3C, 0x17, 0xC0] (LoadPre 0x129823 (fun s => AddrMode.addr (.sib 7 (some 2) 0 .none) s (0x129823 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x129823 4 (.sib 7 (some 2) 0 .none) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129823 4 (.sib 7 (some 2) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x129823 (.sib 7 (some 2) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x129827 [0x41, 0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x129827) (atFlags (condHolds 13) (setccR8Effect 0x129827 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x129827 4 8 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x129827 13 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x12982b [0x49, 0x01, 0xC0] (fun s => s.RIP = 0x12982b) (addR64R64Effect 0x12982b 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12982b 8 0).toInstrSpec (add_r64_r64_effect_step 0x12982b 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12982e [0x31, 0xC0] (fun s => s.RIP = 0x12982e) (xorR32R32Effect 0x12982e 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12982e 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x12982e 0xc0 (by decide)) pre_rip
  have f5 : InstrSpec 0x129830 [0x80, 0x7C, 0x17, 0x01, 0xC0] (LoadPre 0x129830 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x1)) s (0x129830 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x129830 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129830 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x129830 (.sib 7 (some 2) 0 (.d8 0x1)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x129835 [0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x129835) (atFlags (condHolds 13) (setccR8Effect 0x129835 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x129835 3 0 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x129835 13 0xc0 (by decide) (by decide) c)) pre_rip
  have f7 : InstrSpec 0x129838 [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x129838) (xorR32R32Effect 0x129838 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129838 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x129838 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12983b [0x80, 0x7C, 0x17, 0x02, 0xC0] (LoadPre 0x12983b (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x2)) s (0x12983b + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x12983b 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x12983b 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x12983b (.sib 7 (some 2) 0 (.d8 0x2)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x129840 [0x41, 0x0F, 0x9D, 0xC1] (fun s => s.RIP = 0x129840) (atFlags (condHolds 13) (setccR8Effect 0x129840 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x129840 4 9 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x129840 13 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f10 : InstrSpec 0x129844 [0x49, 0x01, 0xC1] (fun s => s.RIP = 0x129844) (addR64R64Effect 0x129844 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129844 9 0).toInstrSpec (add_r64_r64_effect_step 0x129844 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x129847 [0x4D, 0x01, 0xC1] (fun s => s.RIP = 0x129847) (addR64R64Effect 0x129847 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129847 9 8).toInstrSpec (add_r64_r64_effect_step 0x129847 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x12984a [0x31, 0xC0] (fun s => s.RIP = 0x12984a) (xorR32R32Effect 0x12984a 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12984a 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x12984a 0xc0 (by decide)) pre_rip
  have f13 : InstrSpec 0x12984c [0x80, 0x7C, 0x17, 0x03, 0xC0] (LoadPre 0x12984c (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x3)) s (0x12984c + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x12984c 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x12984c 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x12984c (.sib 7 (some 2) 0 (.d8 0x3)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x129851 [0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x129851) (atFlags (condHolds 13) (setccR8Effect 0x129851 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x129851 3 0 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x129851 13 0xc0 (by decide) (by decide) c)) pre_rip
  have f15 : InstrSpec 0x129854 [0x4C, 0x01, 0xC8] (fun s => s.RIP = 0x129854) (addR64R64Effect 0x129854 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129854 0 9).toInstrSpec (add_r64_r64_effect_step 0x129854 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x129857 [0x48, 0x83, 0xC2, 0x04] (fun s => s.RIP = 0x129857) (addR64Imm8Effect 0x129857 2 0x4)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x129857 2 0x4).toInstrSpec (add_r64_imm8_effect_step 0x129857 0x48 0xc2 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x12985b [0x48, 0x39, 0xD6] (fun s => s.RIP = 0x12985b) (cmpR64R64Effect 0x12985b 6 2)
      [.gpr 6, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12985b 6 2).toInstrSpec (cmp_r64_r64_effect_step 0x12985b 0x48 0xd6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129823) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129827) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12982b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12982e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129830) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 64), (21, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129835) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 64), (21, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129838) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 69), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12983b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f8 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f8 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 69), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 71), (21, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129840) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 74), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 71), (21, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129844) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 76), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129847) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12984a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12984c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f13 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f13 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 82), (21, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129851) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 82), (21, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129854) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129857) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 87), (1, 1), (2, 89), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12985b) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 87), (1, 1), (2, 89), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12985e) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 93) (jcc_rel8_effect_step 0x12985e 5 0xc0) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129820 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129820 :=
  Rest.liftedBlock (rest_l129820 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129820 x hx)

theorem rest_l129860 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129860 bytes_l129860) (entryMap (live .l129860))
      2 0x129860 bytes_l129860 b_l129860 := by
  have f0 : InstrSpec 0x129860 [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x129860) (testR64R64Effect 0x129860 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x129860 1 1).toInstrSpec (test_r64_r64_effect_step 0x129860 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129863) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x129863 4 0x20) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129860 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129860 :=
  Rest.liftedBlock (rest_l129860 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129860 x hx)

theorem rest_l129865 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129865 bytes_l129865) (entryMap (live .l129865))
      3 0x129865 bytes_l129865 b_l129865 := by
  have f0 : InstrSpec 0x129865 [0x48, 0x01, 0xD7] (fun s => s.RIP = 0x129865) (addR64R64Effect 0x129865 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129865 7 2).toInstrSpec (add_r64_r64_effect_step 0x129865 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129868 [0x31, 0xD2] (fun s => s.RIP = 0x129868) (xorR32R32Effect 0x129868 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129868 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x129868 0xd2 (by decide)) pre_rip
  have f2 : InstrSpec 0x12986a [0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x12986a) (fun _ => nopEffect 0x12986a 6)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12986a 6).toInstrSpec (nop_m_effect_step 0x12986a [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129868) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12986a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129870) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l129865 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129865 :=
  Rest.liftedBlock (rest_l129865 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129865 x hx)

theorem rest_l129870 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129870 bytes_l129870) (entryMap (live .l129870))
      7 0x129870 bytes_l129870 b_l129870 := by
  have f0 : InstrSpec 0x129870 [0x31, 0xF6] (fun s => s.RIP = 0x129870) (xorR32R32Effect 0x129870 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129870 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x129870 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x129872 [0x80, 0x3C, 0x17, 0xC0] (LoadPre 0x129872 (fun s => AddrMode.addr (.sib 7 (some 2) 0 .none) s (0x129872 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x129872 4 (.sib 7 (some 2) 0 .none) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129872 4 (.sib 7 (some 2) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x129872 (.sib 7 (some 2) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x129876 [0x40, 0x0F, 0x9D, 0xC6] (fun s => s.RIP = 0x129876) (atFlags (condHolds 13) (setccR8Effect 0x129876 4 6))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 6, .rip] :=
    (setccR8Effect_footprint 0x129876 4 6 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x129876 13 0x40 (by decide) 0xc6 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x12987a [0x48, 0x01, 0xF0] (fun s => s.RIP = 0x12987a) (addR64R64Effect 0x12987a 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12987a 0 6).toInstrSpec (add_r64_r64_effect_step 0x12987a 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12987d [0x48, 0xFF, 0xC2] (fun s => s.RIP = 0x12987d) (incR64Effect 0x12987d 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (incR64Effect_footprint 0x12987d 2).toInstrSpec (inc_r64_effect_step 0x12987d 0x48 0xc2 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x129880 [0x48, 0x39, 0xD1] (fun s => s.RIP = 0x129880) (cmpR64R64Effect 0x129880 1 2)
      [.gpr 1, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129880 1 2).toInstrSpec (cmp_r64_r64_effect_step 0x129880 0x48 0xd1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129872) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129876) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12987a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12987d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129880) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 60), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129883) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x129883 5 0xeb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129870 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129870 :=
  Rest.liftedBlock (rest_l129870 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129870 x hx)

theorem rest_l129885 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129885 bytes_l129885) (entryMap (live .l129885))
      1 0x129885 bytes_l129885 b_l129885 := by
  have f0 : InstrSpec 0x129885 [0xC3] (RetPre 0x129885) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x129885).toInstrSpec (ret_effect_step 0x129885) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f0 (by decide) rfl rfl rfl (by decide)

theorem block_l129885 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129885 :=
  Rest.liftedBlock (rest_l129885 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129885 x hx)

theorem rest_l129886 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129886 bytes_l129886) (entryMap (live .l129886))
      5 0x129886 bytes_l129886 b_l129886 := by
  have f0 : InstrSpec 0x129886 [0x41, 0x89, 0xC3] (fun s => s.RIP = 0x129886) (movR32R32Effect 0x129886 3 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x129886 3 11 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x129886 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129889 [0x41, 0x83, 0xE3, 0x04] (fun s => s.RIP = 0x129889) (andR32Imm8Effect 0x129889 4 11 0x4)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x129889 4 11 0x4).toInstrSpec (and_r32_imm8_rex_effect_step 0x129889 0x41 0xe3 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12988d [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x12988d) (xorR32R32Effect 0x12988d 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12988d 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x12988d 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129890 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x129890) (xorR32R32Effect 0x129890 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129890 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x129890 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129893 [0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129893) (fun _ => nopEffect 0x129893 13)
      [] [] [.rip] :=
    (nopEffect_footprint 0x129893 13).toInstrSpec (nop_m_effect_step 0x129893 [0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129889) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12988d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 57), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129890) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 57), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129893) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 57), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298a0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l129886 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129886 :=
  Rest.liftedBlock (rest_l129886 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129886 x hx)

theorem rest_l1298a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1298a0 bytes_l1298a0) (entryMap (live .l1298a0))
      19 0x1298a0 bytes_l1298a0 b_l1298a0 := by
  have f0 : InstrSpec 0x1298a0 [0x31, 0xDB] (fun s => s.RIP = 0x1298a0) (xorR32R32Effect 0x1298a0 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1298a0 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x1298a0 0xdb (by decide)) pre_rip
  have f1 : InstrSpec 0x1298a2 [0x42, 0x80, 0x3C, 0x17, 0xC0] (LoadPre 0x1298a2 (fun s => AddrMode.addr (.sib 7 (some 10) 0 .none) s (0x1298a2 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1298a2 5 (.sib 7 (some 10) 0 .none) 0xc0)
      [.gpr 7, .gpr 10] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x1298a2 5 (.sib 7 (some 10) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x1298a2 0x42 (by decide) (.sib 7 (some 10) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1298a7 [0x0F, 0x9D, 0xC3] (fun s => s.RIP = 0x1298a7) (atFlags (condHolds 13) (setccR8Effect 0x1298a7 3 3))
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 3, .rip] :=
    (setccR8Effect_footprint 0x1298a7 3 3 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1298a7 13 0xc3 (by decide) (by decide) c)) pre_rip
  have f3 : InstrSpec 0x1298aa [0x4C, 0x01, 0xC3] (fun s => s.RIP = 0x1298aa) (addR64R64Effect 0x1298aa 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1298aa 3 8).toInstrSpec (add_r64_r64_effect_step 0x1298aa 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1298ad [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x1298ad) (xorR32R32Effect 0x1298ad 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1298ad 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1298ad 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1298b0 [0x42, 0x80, 0x7C, 0x17, 0x01, 0xC0] (LoadPre 0x1298b0 (fun s => AddrMode.addr (.sib 7 (some 10) 0 (.d8 0x1)) s (0x1298b0 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x1298b0 6 (.sib 7 (some 10) 0 (.d8 0x1)) 0xc0)
      [.gpr 7, .gpr 10] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x1298b0 6 (.sib 7 (some 10) 0 (.d8 0x1)) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x1298b0 0x42 (by decide) (.sib 7 (some 10) 0 (.d8 0x1)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1298b6 [0x41, 0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x1298b6) (atFlags (condHolds 13) (setccR8Effect 0x1298b6 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x1298b6 4 8 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1298b6 13 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x1298ba [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x1298ba) (xorR32R32Effect 0x1298ba 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1298ba 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x1298ba 0x45 0xf6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1298bd [0x42, 0x80, 0x7C, 0x17, 0x02, 0xC0] (LoadPre 0x1298bd (fun s => AddrMode.addr (.sib 7 (some 10) 0 (.d8 0x2)) s (0x1298bd + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x1298bd 6 (.sib 7 (some 10) 0 (.d8 0x2)) 0xc0)
      [.gpr 7, .gpr 10] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x1298bd 6 (.sib 7 (some 10) 0 (.d8 0x2)) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x1298bd 0x42 (by decide) (.sib 7 (some 10) 0 (.d8 0x2)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1298c3 [0x41, 0x0F, 0x9D, 0xC6] (fun s => s.RIP = 0x1298c3) (atFlags (condHolds 13) (setccR8Effect 0x1298c3 4 14))
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 14, .rip] :=
    (setccR8Effect_footprint 0x1298c3 4 14 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1298c3 13 0x41 (by decide) 0xc6 (by decide) c)) pre_rip
  have f10 : InstrSpec 0x1298c7 [0x4D, 0x01, 0xC6] (fun s => s.RIP = 0x1298c7) (addR64R64Effect 0x1298c7 14 8)
      [.gpr 14, .gpr 8] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1298c7 14 8).toInstrSpec (add_r64_r64_effect_step 0x1298c7 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1298ca [0x49, 0x01, 0xDE] (fun s => s.RIP = 0x1298ca) (addR64R64Effect 0x1298ca 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1298ca 14 3).toInstrSpec (add_r64_r64_effect_step 0x1298ca 0x49 0xde (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1298cd [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x1298cd) (xorR32R32Effect 0x1298cd 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1298cd 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1298cd 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1298d0 [0x42, 0x80, 0x7C, 0x17, 0x03, 0xC0] (LoadPre 0x1298d0 (fun s => AddrMode.addr (.sib 7 (some 10) 0 (.d8 0x3)) s (0x1298d0 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x1298d0 6 (.sib 7 (some 10) 0 (.d8 0x3)) 0xc0)
      [.gpr 7, .gpr 10] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x1298d0 6 (.sib 7 (some 10) 0 (.d8 0x3)) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x1298d0 0x42 (by decide) (.sib 7 (some 10) 0 (.d8 0x3)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1298d6 [0x41, 0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x1298d6) (atFlags (condHolds 13) (setccR8Effect 0x1298d6 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x1298d6 4 8 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1298d6 13 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x1298da [0x4D, 0x01, 0xF0] (fun s => s.RIP = 0x1298da) (addR64R64Effect 0x1298da 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1298da 8 14).toInstrSpec (add_r64_r64_effect_step 0x1298da 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1298dd [0x49, 0x83, 0xC2, 0x04] (fun s => s.RIP = 0x1298dd) (addR64Imm8Effect 0x1298dd 10 0x4)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1298dd 10 0x4).toInstrSpec (add_r64_imm8_effect_step 0x1298dd 0x49 0xc2 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1298e1 [0x4D, 0x39, 0xD3] (fun s => s.RIP = 0x1298e1) (cmpR64R64Effect 0x1298e1 11 10)
      [.gpr 11, .gpr 10] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1298e1 11 10).toInstrSpec (cmp_r64_r64_effect_step 0x1298e1 0x4d 0xd3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298a2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298a7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298aa) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298ad) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 62), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298b0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 62), (9, 9), (10, 10), (11, 11), (14, 14), (20, 64), (21, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298b6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (14, 14), (20, 64), (21, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298ba) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (14, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298bd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f8 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f8 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (14, 69), (20, 71), (21, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298c3) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (14, 74), (20, 71), (21, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298c7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (14, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298ca) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (14, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298cd) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 80), (9, 9), (10, 10), (11, 11), (14, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298d0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f13 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f13 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 80), (9, 9), (10, 10), (11, 11), (14, 78), (20, 82), (21, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298d6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 9), (10, 10), (11, 11), (14, 78), (20, 82), (21, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298da) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 87), (9, 9), (10, 10), (11, 11), (14, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298dd) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f16 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 87), (9, 9), (10, 89), (11, 11), (14, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298e1) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 87), (9, 9), (10, 89), (11, 11), (14, 78), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298e4) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 93) (jcc_rel8_effect_step 0x1298e4 5 0xba) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1298a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1298a0 :=
  Rest.liftedBlock (rest_l1298a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1298a0 x hx)

theorem rest_l1298e6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1298e6 bytes_l1298e6) (entryMap (live .l1298e6))
      2 0x1298e6 bytes_l1298e6 b_l1298e6 := by
  have f0 : InstrSpec 0x1298e6 [0x4D, 0x85, 0xC9] (fun s => s.RIP = 0x1298e6) (testR64R64Effect 0x1298e6 9 9)
      [.gpr 9, .gpr 9] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1298e6 9 9).toInstrSpec (test_r64_r64_effect_step 0x1298e6 0x4d 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298e9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1298e9 4 0x2a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1298e6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1298e6 :=
  Rest.liftedBlock (rest_l1298e6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1298e6 x hx)

theorem rest_l1298eb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1298eb bytes_l1298eb) (entryMap (live .l1298eb))
      3 0x1298eb bytes_l1298eb b_l1298eb := by
  have f0 : InstrSpec 0x1298eb [0x49, 0x01, 0xFA] (fun s => s.RIP = 0x1298eb) (addR64R64Effect 0x1298eb 10 7)
      [.gpr 10, .gpr 7] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1298eb 10 7).toInstrSpec (add_r64_r64_effect_step 0x1298eb 0x49 0xfa (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1298ee [0x45, 0x31, 0xDB] (fun s => s.RIP = 0x1298ee) (xorR32R32Effect 0x1298ee 3 11 11)
      [.gpr 11, .gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1298ee 3 11 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x1298ee 0x45 0xdb (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1298f1 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1298f1) (fun _ => nopEffect 0x1298f1 15)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1298f1 15).toInstrSpec (nop_m_effect_step 0x1298f1 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298ee) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1298f1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129900) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l1298eb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1298eb :=
  Rest.liftedBlock (rest_l1298eb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1298eb x hx)

theorem rest_l129900 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129900 bytes_l129900) (entryMap (live .l129900))
      7 0x129900 bytes_l129900 b_l129900 := by
  have f0 : InstrSpec 0x129900 [0x31, 0xDB] (fun s => s.RIP = 0x129900) (xorR32R32Effect 0x129900 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129900 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x129900 0xdb (by decide)) pre_rip
  have f1 : InstrSpec 0x129902 [0x43, 0x80, 0x3C, 0x1A, 0xC0] (LoadPre 0x129902 (fun s => AddrMode.addr (.sib 10 (some 11) 0 .none) s (0x129902 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x129902 5 (.sib 10 (some 11) 0 .none) 0xc0)
      [.gpr 10, .gpr 11] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129902 5 (.sib 10 (some 11) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x129902 0x43 (by decide) (.sib 10 (some 11) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x129907 [0x0F, 0x9D, 0xC3] (fun s => s.RIP = 0x129907) (atFlags (condHolds 13) (setccR8Effect 0x129907 3 3))
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 3, .rip] :=
    (setccR8Effect_footprint 0x129907 3 3 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x129907 13 0xc3 (by decide) (by decide) c)) pre_rip
  have f3 : InstrSpec 0x12990a [0x49, 0x01, 0xD8] (fun s => s.RIP = 0x12990a) (addR64R64Effect 0x12990a 8 3)
      [.gpr 8, .gpr 3] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12990a 8 3).toInstrSpec (add_r64_r64_effect_step 0x12990a 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12990d [0x49, 0xFF, 0xC3] (fun s => s.RIP = 0x12990d) (incR64Effect 0x12990d 11)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (incR64Effect_footprint 0x12990d 11).toInstrSpec (inc_r64_effect_step 0x12990d 0x49 0xc3 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x129910 [0x4D, 0x39, 0xD9] (fun s => s.RIP = 0x129910) (cmpR64R64Effect 0x129910 9 11)
      [.gpr 9, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129910 9 11).toInstrSpec (cmp_r64_r64_effect_step 0x129910 0x4d 0xd9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129902) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129907) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12990a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12990d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 62), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129910) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 62), (14, 14), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129913) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x129913 5 0xeb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129900 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129900 :=
  Rest.liftedBlock (rest_l129900 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129900 x hx)

theorem rest_l129915 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129915 bytes_l129915) (entryMap (live .l129915))
      3 0x129915 bytes_l129915 b_l129915 := by
  have f0 : InstrSpec 0x129915 [0x48, 0x01, 0xC7] (fun s => s.RIP = 0x129915) (addR64R64Effect 0x129915 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129915 7 0).toInstrSpec (add_r64_r64_effect_step 0x129915 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129918 [0x48, 0x85, 0xF6] (fun s => s.RIP = 0x129918) (testR64R64Effect 0x129918 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x129918 6 6).toInstrSpec (test_r64_r64_effect_step 0x129918 0x48 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129918) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12991b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x12991b 4 0x8f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129915 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129915 :=
  Rest.liftedBlock (rest_l129915 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129915 x hx)

theorem rest_l129921 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129921 bytes_l129921) (entryMap (live .l129921))
      7 0x129921 bytes_l129921 b_l129921 := by
  have f0 : InstrSpec 0x129921 [0x48, 0xB8, 0xF8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x129921) (movR64Imm64Effect 0x129921 0 0x7ffffffffffffff8)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x129921 0 0x7ffffffffffffff8).toInstrSpec (mov_r64_imm64_effect_step 0x129921 0x48 0xb8 (by decide) (by decide) 0x7ffffffffffffff8) pre_rip
  have f1 : InstrSpec 0x12992b [0x48, 0x21, 0xC2] (fun s => s.RIP = 0x12992b) (andR64R64Effect 0x12992b 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x12992b 2 0).toInstrSpec (and_r64_r64_effect_step 0x12992b 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12992e [0x31, 0xC0] (fun s => s.RIP = 0x12992e) (xorR32R32Effect 0x12992e 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12992e 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x12992e 0xc0 (by decide)) pre_rip
  have f3 : InstrSpec 0x129930 [0x80, 0x3C, 0x17, 0xC0] (LoadPre 0x129930 (fun s => AddrMode.addr (.sib 7 (some 2) 0 .none) s (0x129930 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x129930 4 (.sib 7 (some 2) 0 .none) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129930 4 (.sib 7 (some 2) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x129930 (.sib 7 (some 2) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x129934 [0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x129934) (atFlags (condHolds 13) (setccR8Effect 0x129934 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x129934 3 0 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x129934 13 0xc0 (by decide) (by decide) c)) pre_rip
  have f5 : InstrSpec 0x129937 [0x83, 0xFE, 0x01] (fun s => s.RIP = 0x129937) (cmpR32Imm8Effect 0x129937 3 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x129937 3 6 0x1).toInstrSpec (cmp_r32_imm8_effect_step 0x129937 0xfe 0x1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12992b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12992e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129930) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 57), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (20, 59), (21, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129934) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (20, 59), (21, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129937) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12993a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x12993a 4 0x76) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129921 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129921 :=
  Rest.liftedBlock (rest_l129921 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129921 x hx)

theorem rest_l12993c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12993c bytes_l12993c) (entryMap (live .l12993c))
      6 0x12993c bytes_l12993c b_l12993c := by
  have f0 : InstrSpec 0x12993c [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x12993c) (xorR32R32Effect 0x12993c 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12993c 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x12993c 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12993f [0x80, 0x7C, 0x17, 0x01, 0xC0] (LoadPre 0x12993f (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x1)) s (0x12993f + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x12993f 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x12993f 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x12993f (.sib 7 (some 2) 0 (.d8 0x1)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x129944 [0x41, 0x0F, 0x9D, 0xC1] (fun s => s.RIP = 0x129944) (atFlags (condHolds 13) (setccR8Effect 0x129944 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x129944 4 9 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x129944 13 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x129948 [0x4C, 0x01, 0xC8] (fun s => s.RIP = 0x129948) (addR64R64Effect 0x129948 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129948 0 9).toInstrSpec (add_r64_r64_effect_step 0x129948 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12994b [0x83, 0xFE, 0x02] (fun s => s.RIP = 0x12994b) (cmpR32Imm8Effect 0x12994b 3 6 0x2)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x12994b 3 6 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x12994b 0xfe 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12993f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129944) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129948) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12994b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12994e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x12994e 4 0x62) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12993c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12993c :=
  Rest.liftedBlock (rest_l12993c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12993c x hx)

theorem rest_l129950 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129950 bytes_l129950) (entryMap (live .l129950))
      6 0x129950 bytes_l129950 b_l129950 := by
  have f0 : InstrSpec 0x129950 [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x129950) (xorR32R32Effect 0x129950 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129950 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x129950 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129953 [0x80, 0x7C, 0x17, 0x02, 0xC0] (LoadPre 0x129953 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x2)) s (0x129953 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x129953 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129953 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x129953 (.sib 7 (some 2) 0 (.d8 0x2)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x129958 [0x41, 0x0F, 0x9D, 0xC1] (fun s => s.RIP = 0x129958) (atFlags (condHolds 13) (setccR8Effect 0x129958 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x129958 4 9 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x129958 13 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x12995c [0x4C, 0x01, 0xC8] (fun s => s.RIP = 0x12995c) (addR64R64Effect 0x12995c 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12995c 0 9).toInstrSpec (add_r64_r64_effect_step 0x12995c 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12995f [0x83, 0xFE, 0x03] (fun s => s.RIP = 0x12995f) (cmpR32Imm8Effect 0x12995f 3 6 0x3)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x12995f 3 6 0x3).toInstrSpec (cmp_r32_imm8_effect_step 0x12995f 0xfe 0x3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129953) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129958) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12995c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12995f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129962) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x129962 4 0x4e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129950 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129950 :=
  Rest.liftedBlock (rest_l129950 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129950 x hx)

theorem rest_l129964 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129964 bytes_l129964) (entryMap (live .l129964))
      6 0x129964 bytes_l129964 b_l129964 := by
  have f0 : InstrSpec 0x129964 [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x129964) (xorR32R32Effect 0x129964 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129964 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x129964 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129967 [0x80, 0x7C, 0x17, 0x03, 0xC0] (LoadPre 0x129967 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x3)) s (0x129967 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x129967 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129967 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x129967 (.sib 7 (some 2) 0 (.d8 0x3)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12996c [0x41, 0x0F, 0x9D, 0xC1] (fun s => s.RIP = 0x12996c) (atFlags (condHolds 13) (setccR8Effect 0x12996c 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x12996c 4 9 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x12996c 13 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x129970 [0x4C, 0x01, 0xC8] (fun s => s.RIP = 0x129970) (addR64R64Effect 0x129970 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129970 0 9).toInstrSpec (add_r64_r64_effect_step 0x129970 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129973 [0x83, 0xFE, 0x04] (fun s => s.RIP = 0x129973) (cmpR32Imm8Effect 0x129973 3 6 0x4)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x129973 3 6 0x4).toInstrSpec (cmp_r32_imm8_effect_step 0x129973 0xfe 0x4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129967) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12996c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129970) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129973) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129976) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x129976 4 0x3a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129964 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129964 :=
  Rest.liftedBlock (rest_l129964 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129964 x hx)

theorem rest_l129978 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129978 bytes_l129978) (entryMap (live .l129978))
      6 0x129978 bytes_l129978 b_l129978 := by
  have f0 : InstrSpec 0x129978 [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x129978) (xorR32R32Effect 0x129978 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129978 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x129978 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12997b [0x80, 0x7C, 0x17, 0x04, 0xC0] (LoadPre 0x12997b (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x4)) s (0x12997b + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x12997b 5 (.sib 7 (some 2) 0 (.d8 0x4)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x12997b 5 (.sib 7 (some 2) 0 (.d8 0x4)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x12997b (.sib 7 (some 2) 0 (.d8 0x4)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x129980 [0x41, 0x0F, 0x9D, 0xC1] (fun s => s.RIP = 0x129980) (atFlags (condHolds 13) (setccR8Effect 0x129980 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x129980 4 9 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x129980 13 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x129984 [0x4C, 0x01, 0xC8] (fun s => s.RIP = 0x129984) (addR64R64Effect 0x129984 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129984 0 9).toInstrSpec (add_r64_r64_effect_step 0x129984 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129987 [0x83, 0xFE, 0x05] (fun s => s.RIP = 0x129987) (cmpR32Imm8Effect 0x129987 3 6 0x5)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x129987 3 6 0x5).toInstrSpec (cmp_r32_imm8_effect_step 0x129987 0xfe 0x5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12997b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129980) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129984) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129987) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12998a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x12998a 4 0x26) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129978 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129978 :=
  Rest.liftedBlock (rest_l129978 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129978 x hx)

theorem rest_l12998c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12998c bytes_l12998c) (entryMap (live .l12998c))
      6 0x12998c bytes_l12998c b_l12998c := by
  have f0 : InstrSpec 0x12998c [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x12998c) (xorR32R32Effect 0x12998c 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12998c 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x12998c 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12998f [0x80, 0x7C, 0x17, 0x05, 0xC0] (LoadPre 0x12998f (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x5)) s (0x12998f + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x12998f 5 (.sib 7 (some 2) 0 (.d8 0x5)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x12998f 5 (.sib 7 (some 2) 0 (.d8 0x5)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x12998f (.sib 7 (some 2) 0 (.d8 0x5)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x129994 [0x41, 0x0F, 0x9D, 0xC1] (fun s => s.RIP = 0x129994) (atFlags (condHolds 13) (setccR8Effect 0x129994 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x129994 4 9 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x129994 13 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x129998 [0x4C, 0x01, 0xC8] (fun s => s.RIP = 0x129998) (addR64R64Effect 0x129998 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129998 0 9).toInstrSpec (add_r64_r64_effect_step 0x129998 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12999b [0x83, 0xFE, 0x06] (fun s => s.RIP = 0x12999b) (cmpR32Imm8Effect 0x12999b 3 6 0x6)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x12999b 3 6 0x6).toInstrSpec (cmp_r32_imm8_effect_step 0x12999b 0xfe 0x6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12998f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129994) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129998) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12999b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12999e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x12999e 4 0x12) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12998c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12998c :=
  Rest.liftedBlock (rest_l12998c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12998c x hx)

theorem rest_l1299a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1299a0 bytes_l1299a0) (entryMap (live .l1299a0))
      5 0x1299a0 bytes_l1299a0 b_l1299a0 := by
  have f0 : InstrSpec 0x1299a0 [0x31, 0xF6] (fun s => s.RIP = 0x1299a0) (xorR32R32Effect 0x1299a0 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1299a0 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x1299a0 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x1299a2 [0x80, 0x7C, 0x17, 0x06, 0xC0] (LoadPre 0x1299a2 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x6)) s (0x1299a2 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1299a2 5 (.sib 7 (some 2) 0 (.d8 0x6)) 0xc0)
      [.gpr 7, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x1299a2 5 (.sib 7 (some 2) 0 (.d8 0x6)) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x1299a2 (.sib 7 (some 2) 0 (.d8 0x6)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1299a7 [0x40, 0x0F, 0x9D, 0xC6] (fun s => s.RIP = 0x1299a7) (atFlags (condHolds 13) (setccR8Effect 0x1299a7 4 6))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 6, .rip] :=
    (setccR8Effect_footprint 0x1299a7 4 6 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1299a7 13 0x40 (by decide) 0xc6 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x1299ab [0x48, 0x01, 0xF0] (fun s => s.RIP = 0x1299ab) (addR64R64Effect 0x1299ab 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1299ab 0 6).toInstrSpec (add_r64_r64_effect_step 0x1299ab 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299a2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299a7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299ab) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299ae) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 62) (jmp_rel8_effect_step 0x1299ae 0x2 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1299a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1299a0 :=
  Rest.liftedBlock (rest_l1299a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1299a0 x hx)

theorem rest_l1299b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1299b0 bytes_l1299b0) (entryMap (live .l1299b0))
      1 0x1299b0 bytes_l1299b0 b_l1299b0 := by
  have f0 : InstrSpec 0x1299b0 [0x31, 0xC0] (fun s => s.RIP = 0x1299b0) (xorR32R32Effect 0x1299b0 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1299b0 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x1299b0 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299b2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1299b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1299b0 :=
  Rest.liftedBlock (rest_l1299b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1299b0 x hx)

theorem rest_l1299b2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1299b2 bytes_l1299b2) (entryMap (live .l1299b2))
      5 0x1299b2 bytes_l1299b2 b_l1299b2 := by
  have f0 : InstrSpec 0x1299b2 [0x4C, 0x01, 0xC0] (fun s => s.RIP = 0x1299b2) (addR64R64Effect 0x1299b2 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1299b2 0 8).toInstrSpec (add_r64_r64_effect_step 0x1299b2 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1299b5 [0x49, 0xB8, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01] (fun s => s.RIP = 0x1299b5) (movR64Imm64Effect 0x1299b5 8 0x101010101010101)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x1299b5 8 0x101010101010101).toInstrSpec (mov_r64_imm64_effect_step 0x1299b5 0x49 0xb8 (by decide) (by decide) 0x101010101010101) pre_rip
  have f2 : InstrSpec 0x1299bf [0x48, 0xBE, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00] (fun s => s.RIP = 0x1299bf) (movR64Imm64Effect 0x1299bf 6 0xff00ff00ff00ff)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x1299bf 6 0xff00ff00ff00ff).toInstrSpec (mov_r64_imm64_effect_step 0x1299bf 0x48 0xbe (by decide) (by decide) 0xff00ff00ff00ff) pre_rip
  have f3 : InstrSpec 0x1299c9 [0x48, 0xBA, 0x01, 0x00, 0x01, 0x00, 0x01, 0x00, 0x01, 0x00] (fun s => s.RIP = 0x1299c9) (movR64Imm64Effect 0x1299c9 2 0x1000100010001)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x1299c9 2 0x1000100010001).toInstrSpec (mov_r64_imm64_effect_step 0x1299c9 0x48 0xba (by decide) (by decide) 0x1000100010001) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299b5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (4, 4), (5, 5), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299bf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (4, 4), (5, 5), (6, 57), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299c9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 59), (4, 4), (5, 5), (6, 57), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299d3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 61) (jmp_rel8_effect_step 0x1299d3 0x3f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1299b2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1299b2 :=
  Rest.liftedBlock (rest_l1299b2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1299b2 x hx)

theorem rest_l1299e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1299e0 bytes_l1299e0) (entryMap (live .l1299e0))
      1 0x1299e0 bytes_l1299e0 b_l1299e0 := by
  have f0 : InstrSpec 0x1299e0 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x1299e0) (xorR32R32Effect 0x1299e0 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1299e0 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x1299e0 0x45 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299e3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1299e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1299e0 :=
  Rest.liftedBlock (rest_l1299e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1299e0 x hx)

theorem rest_l1299e3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1299e3 bytes_l1299e3) (entryMap (live .l1299e3))
      14 0x1299e3 bytes_l1299e3 b_l1299e3 := by
  have f0 : InstrSpec 0x1299e3 [0x4C, 0x01, 0xCF] (fun s => s.RIP = 0x1299e3) (addR64R64Effect 0x1299e3 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1299e3 7 9).toInstrSpec (add_r64_r64_effect_step 0x1299e3 0x4c 0xcf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1299e6 [0x4C, 0x29, 0xD1] (fun s => s.RIP = 0x1299e6) (subR64R64Effect 0x1299e6 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1299e6 1 10).toInstrSpec (sub_r64_r64_effect_step 0x1299e6 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1299e9 [0x45, 0x89, 0xD3] (fun s => s.RIP = 0x1299e9) (movR32R32Effect 0x1299e9 3 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x1299e9 3 11 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x1299e9 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1299ec [0x41, 0x83, 0xE3, 0x03] (fun s => s.RIP = 0x1299ec) (andR32Imm8Effect 0x1299ec 4 11 0x3)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1299ec 4 11 0x3).toInstrSpec (and_r32_imm8_rex_effect_step 0x1299ec 0x41 0xe3 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1299f0 [0x4C, 0x89, 0xF3] (fun s => s.RIP = 0x1299f0) (movR64R64Effect 0x1299f0 3 14)
      [.gpr 14] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1299f0 3 14).toInstrSpec (mov_r64_r64_effect_step 0x1299f0 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1299f3 [0x48, 0x21, 0xF3] (fun s => s.RIP = 0x1299f3) (andR64R64Effect 0x1299f3 3 6)
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1299f3 3 6).toInstrSpec (and_r64_r64_effect_step 0x1299f3 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1299f6 [0x49, 0xC1, 0xEE, 0x08] (fun s => s.RIP = 0x1299f6) (shrR64Effect 0x1299f6 4 14 8)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64Effect_footprint 0x1299f6 4 14 8).toInstrSpec (shr_r64_imm8_effect_step 0x1299f6 0x49 0xee 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1299fa [0x49, 0x21, 0xF6] (fun s => s.RIP = 0x1299fa) (andR64R64Effect 0x1299fa 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1299fa 14 6).toInstrSpec (and_r64_r64_effect_step 0x1299fa 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1299fd [0x49, 0x01, 0xDE] (fun s => s.RIP = 0x1299fd) (addR64R64Effect 0x1299fd 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1299fd 14 3).toInstrSpec (add_r64_r64_effect_step 0x1299fd 0x49 0xde (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x129a00 [0x4C, 0x0F, 0xAF, 0xF2] (fun s => s.RIP = 0x129a00) (imulR64R64Effect 0x129a00 4 14 2)
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x129a00 4 14 2).toInstrSpec (imul_r64_r64_effect_step 0x129a00 0x4c (by decide) 0xf2 (by decide)) pre_rip
  have f10 : InstrSpec 0x129a04 [0x49, 0xC1, 0xEE, 0x30] (fun s => s.RIP = 0x129a04) (shrR64Effect 0x129a04 4 14 48)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64Effect_footprint 0x129a04 4 14 48).toInstrSpec (shr_r64_imm8_effect_step 0x129a04 0x49 0xee 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x129a08 [0x4C, 0x01, 0xF0] (fun s => s.RIP = 0x129a08) (addR64R64Effect 0x129a08 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129a08 0 14).toInstrSpec (add_r64_r64_effect_step 0x129a08 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x129a0b [0x4D, 0x85, 0xDB] (fun s => s.RIP = 0x129a0b) (testR64R64Effect 0x129a0b 11 11)
      [.gpr 11, .gpr 11] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x129a0b 11 11).toInstrSpec (test_r64_r64_effect_step 0x129a0b 0x4d 0xdb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299e6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299e9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 57), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299ec) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299f0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 61), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299f3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299f6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299fa) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1299fd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a00) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a04) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a08) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a0b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 75), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 73), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a0e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 79) (jcc_rel32_effect_step 0x129a0e 5 0xb5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1299e3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1299e3 :=
  Rest.liftedBlock (rest_l1299e3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1299e3 x hx)

theorem rest_l129a14 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129a14 bytes_l129a14) (entryMap (live .l129a14))
      2 0x129a14 bytes_l129a14 b_l129a14 := by
  have f0 : InstrSpec 0x129a14 [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x129a14) (testR64R64Effect 0x129a14 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x129a14 1 1).toInstrSpec (test_r64_r64_effect_step 0x129a14 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a17) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x129a17 4 0x12d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129a14 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129a14 :=
  Rest.liftedBlock (rest_l129a14 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129a14 x hx)

theorem rest_l129a1d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129a1d bytes_l129a1d) (entryMap (live .l129a1d))
      8 0x129a1d bytes_l129a1d b_l129a1d := by
  have f0 : InstrSpec 0x129a1d [0x49, 0x89, 0xF9] (fun s => s.RIP = 0x129a1d) (movR64R64Effect 0x129a1d 9 7)
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x129a1d 9 7).toInstrSpec (mov_r64_r64_effect_step 0x129a1d 0x49 0xf9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129a20 [0x48, 0x81, 0xF9, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129a20) (cmpR64Imm32Effect 0x129a20 1 0xc0)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm32Effect_footprint 0x129a20 1 0xc0).toInstrSpec (cmp_r64_imm32_effect_step 0x129a20 0x48 0xf9 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129a27 [0x41, 0xBA, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129a27) (movR32Imm32Effect 0x129a27 6 10 0xc0)
      [] [] [.reg 10, .rip] :=
    (movR32Imm32Effect_footprint 0x129a27 6 10 0xc0).toInstrSpec (mov_r32_imm32_rex_effect_step 0x129a27 0x41 0xba (by decide) (by decide) 0xc0) pre_rip
  have f3 : InstrSpec 0x129a2d [0x4C, 0x0F, 0x42, 0xD1] (fun s => s.RIP = 0x129a2d) (atFlags (condHolds 2) (cmovR64R64Effect 0x129a2d 4 10 1))
      [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .rip] :=
    (cmovR64R64Effect_footprint 0x129a2d 4 10 1 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x129a2d 2 0x4c (by decide) 0xd1 (by decide) c)) pre_rip
  have f4 : InstrSpec 0x129a31 [0x42, 0x8D, 0x3C, 0xD5, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129a31) (leaR32Effect 0x129a31 8 7 (.abs (some 10) 3 0x0))
      [.gpr 10] [] [.reg 7, .rip] :=
    (leaR32Effect_footprint 0x129a31 8 7 (.abs (some 10) 3 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x129a31 0x42 (by decide) 7 (.abs (some 10) 3 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x129a39 [0x41, 0x89, 0xFB] (fun s => s.RIP = 0x129a39) (movR32R32Effect 0x129a39 3 11 7)
      [.gpr 7] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x129a39 3 11 7).toInstrSpec (mov_r32_r32_rex_effect_step 0x129a39 0x41 0xfb (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129a3c [0x41, 0x81, 0xE3, 0xE0, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x129a3c) (andR32Imm32Effect 0x129a3c 7 11 0x7e0)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x129a3c 7 11 0x7e0).toInstrSpec (and_r32_imm32_rex_effect_step 0x129a3c 0x41 0xe3 0x7e0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a20) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (14, 14), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a27) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 57), (14, 14), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a2d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 59), (14, 14), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a31) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 53), (10, 59), (14, 14), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a39) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 53), (10, 59), (11, 63), (14, 14), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a3c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 53), (10, 59), (11, 65), (14, 14), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a43) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 68) (jcc_rel8_effect_step 0x129a43 4 0x9b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129a1d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129a1d :=
  Rest.liftedBlock (rest_l129a1d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129a1d x hx)

theorem rest_l129a45 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129a45 bytes_l129a45) (entryMap (live .l129a45))
      4 0x129a45 bytes_l129a45 b_l129a45 := by
  have f0 : InstrSpec 0x129a45 [0x4D, 0x01, 0xCB] (fun s => s.RIP = 0x129a45) (addR64R64Effect 0x129a45 11 9)
      [.gpr 11, .gpr 9] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129a45 11 9).toInstrSpec (add_r64_r64_effect_step 0x129a45 0x4d 0xcb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129a48 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x129a48) (xorR32R32Effect 0x129a48 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129a48 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x129a48 0x45 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129a4b [0x4C, 0x89, 0xCB] (fun s => s.RIP = 0x129a4b) (movR64R64Effect 0x129a4b 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x129a4b 3 9).toInstrSpec (mov_r64_r64_effect_step 0x129a4b 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129a4e [0x66, 0x90] (fun s => s.RIP = 0x129a4e) (fun _ => nopEffect 0x129a4e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x129a4e 2).toInstrSpec (nop_66_effect_step 0x129a4e) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a48) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a4b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a4e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a50) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l129a45 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129a45 :=
  Rest.liftedBlock (rest_l129a45 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129a45 x hx)

theorem rest_l129a50_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x129a50 bytes_l129a50) [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 91), (14, 89), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]
      15 0x129a94 bytes_l129a50_1 b_l129a50_1 := by
  have f20 : InstrSpec 0x129a94 [0x4D, 0x09, 0xF5] (fun s => s.RIP = 0x129a94) (orR64R64Effect 0x129a94 13 14)
      [.gpr 13, .gpr 14] [] [.reg 13, .flags, .rip] :=
    (orR64R64Effect_footprint 0x129a94 13 14).toInstrSpec (or_r64_r64_effect_step 0x129a94 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x129a97 [0x4D, 0x21, 0xC5] (fun s => s.RIP = 0x129a97) (andR64R64Effect 0x129a97 13 8)
      [.gpr 13, .gpr 8] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x129a97 13 8).toInstrSpec (and_r64_r64_effect_step 0x129a97 0x4d 0xc5 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x129a9a [0x4D, 0x01, 0xE5] (fun s => s.RIP = 0x129a9a) (addR64R64Effect 0x129a9a 13 12)
      [.gpr 13, .gpr 12] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129a9a 13 12).toInstrSpec (add_r64_r64_effect_step 0x129a9a 0x4d 0xe5 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x129a9d [0x4D, 0x01, 0xFD] (fun s => s.RIP = 0x129a9d) (addR64R64Effect 0x129a9d 13 15)
      [.gpr 13, .gpr 15] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129a9d 13 15).toInstrSpec (add_r64_r64_effect_step 0x129a9d 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x129aa0 [0x4C, 0x8B, 0x73, 0x18] (LoadPre 0x129aa0 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x129aa0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129aa0 14 (.base 3 (.d8 0x18)))
      [.gpr 3] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x129aa0 14 (.base 3 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x129aa0 0x4c (by decide) 6 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x129aa4 [0x4D, 0x89, 0xF7] (fun s => s.RIP = 0x129aa4) (movR64R64Effect 0x129aa4 15 14)
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x129aa4 15 14).toInstrSpec (mov_r64_r64_effect_step 0x129aa4 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x129aa7 [0x49, 0xF7, 0xD7] (fun s => s.RIP = 0x129aa7) (notR64Effect 0x129aa7 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (notR64Effect_footprint 0x129aa7 15).toInstrSpec (not_r64_effect_step 0x129aa7 0x49 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x129aaa [0x49, 0xC1, 0xEF, 0x07] (fun s => s.RIP = 0x129aaa) (shrR64Effect 0x129aaa 4 15 7)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x129aaa 4 15 7).toInstrSpec (shr_r64_imm8_effect_step 0x129aaa 0x49 0xef 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x129aae [0x49, 0xC1, 0xEE, 0x06] (fun s => s.RIP = 0x129aae) (shrR64Effect 0x129aae 4 14 6)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64Effect_footprint 0x129aae 4 14 6).toInstrSpec (shr_r64_imm8_effect_step 0x129aae 0x49 0xee 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x129ab2 [0x4D, 0x09, 0xFE] (fun s => s.RIP = 0x129ab2) (orR64R64Effect 0x129ab2 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (orR64R64Effect_footprint 0x129ab2 14 15).toInstrSpec (or_r64_r64_effect_step 0x129ab2 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x129ab5 [0x4D, 0x21, 0xC6] (fun s => s.RIP = 0x129ab5) (andR64R64Effect 0x129ab5 14 8)
      [.gpr 14, .gpr 8] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x129ab5 14 8).toInstrSpec (and_r64_r64_effect_step 0x129ab5 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x129ab8 [0x4D, 0x01, 0xEE] (fun s => s.RIP = 0x129ab8) (addR64R64Effect 0x129ab8 14 13)
      [.gpr 14, .gpr 13] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129ab8 14 13).toInstrSpec (add_r64_r64_effect_step 0x129ab8 0x4d 0xee (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x129abb [0x48, 0x83, 0xC3, 0x20] (fun s => s.RIP = 0x129abb) (addR64Imm8Effect 0x129abb 3 0x20)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x129abb 3 0x20).toInstrSpec (add_r64_imm8_effect_step 0x129abb 0x48 0xc3 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x129abf [0x4C, 0x39, 0xDB] (fun s => s.RIP = 0x129abf) (cmpR64R64Effect 0x129abf 3 11)
      [.gpr 3, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129abf 3 11).toInstrSpec (cmp_r64_r64_effect_step 0x129abf 0x4c 0xdb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 93), (14, 89), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a97) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 95), (14, 89), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a9a) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 97), (14, 89), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a9d) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 89), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129aa0) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 101), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129aa4) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 101), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129aa7) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 101), (15, 105), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129aaa) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 101), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129aae) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 109), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ab2) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 111), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ab5) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 113), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ab8) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 115), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129abb) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 117), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 115), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129abf) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 117), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 115), (15, 107), (19, 119), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ac2) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 121) (jcc_rel8_effect_step 0x129ac2 5 0x8c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l129a50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129a50 bytes_l129a50) (entryMap (live .l129a50))
      35 0x129a50 bytes_l129a50 b_l129a50 := by
  have f0 : InstrSpec 0x129a50 [0x4C, 0x8B, 0x3B] (LoadPre 0x129a50 (fun s => AddrMode.addr (.base 3 .none) s (0x129a50 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x129a50 15 (.base 3 .none))
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x129a50 15 (.base 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x129a50 0x4c (by decide) 7 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x129a53 [0x4C, 0x8B, 0x63, 0x08] (LoadPre 0x129a53 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x129a53 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129a53 12 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x129a53 12 (.base 3 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x129a53 0x4c (by decide) 4 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x129a57 [0x4D, 0x89, 0xFD] (fun s => s.RIP = 0x129a57) (movR64R64Effect 0x129a57 13 15)
      [.gpr 15] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x129a57 13 15).toInstrSpec (mov_r64_r64_effect_step 0x129a57 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129a5a [0x49, 0xF7, 0xD5] (fun s => s.RIP = 0x129a5a) (notR64Effect 0x129a5a 13)
      [.gpr 13] [] [.reg 13, .rip] :=
    (notR64Effect_footprint 0x129a5a 13).toInstrSpec (not_r64_effect_step 0x129a5a 0x49 0xd5 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129a5d [0x49, 0xC1, 0xED, 0x07] (fun s => s.RIP = 0x129a5d) (shrR64Effect 0x129a5d 4 13 7)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR64Effect_footprint 0x129a5d 4 13 7).toInstrSpec (shr_r64_imm8_effect_step 0x129a5d 0x49 0xed 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x129a61 [0x49, 0xC1, 0xEF, 0x06] (fun s => s.RIP = 0x129a61) (shrR64Effect 0x129a61 4 15 6)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x129a61 4 15 6).toInstrSpec (shr_r64_imm8_effect_step 0x129a61 0x49 0xef 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129a65 [0x4D, 0x09, 0xEF] (fun s => s.RIP = 0x129a65) (orR64R64Effect 0x129a65 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x129a65 15 13).toInstrSpec (or_r64_r64_effect_step 0x129a65 0x4d 0xef (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129a68 [0x4D, 0x21, 0xC7] (fun s => s.RIP = 0x129a68) (andR64R64Effect 0x129a68 15 8)
      [.gpr 15, .gpr 8] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x129a68 15 8).toInstrSpec (and_r64_r64_effect_step 0x129a68 0x4d 0xc7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x129a6b [0x4D, 0x01, 0xF7] (fun s => s.RIP = 0x129a6b) (addR64R64Effect 0x129a6b 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129a6b 15 14).toInstrSpec (add_r64_r64_effect_step 0x129a6b 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x129a6e [0x4D, 0x89, 0xE6] (fun s => s.RIP = 0x129a6e) (movR64R64Effect 0x129a6e 14 12)
      [.gpr 12] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x129a6e 14 12).toInstrSpec (mov_r64_r64_effect_step 0x129a6e 0x4d 0xe6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129a71 [0x49, 0xF7, 0xD6] (fun s => s.RIP = 0x129a71) (notR64Effect 0x129a71 14)
      [.gpr 14] [] [.reg 14, .rip] :=
    (notR64Effect_footprint 0x129a71 14).toInstrSpec (not_r64_effect_step 0x129a71 0x49 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x129a74 [0x49, 0xC1, 0xEE, 0x07] (fun s => s.RIP = 0x129a74) (shrR64Effect 0x129a74 4 14 7)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64Effect_footprint 0x129a74 4 14 7).toInstrSpec (shr_r64_imm8_effect_step 0x129a74 0x49 0xee 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x129a78 [0x49, 0xC1, 0xEC, 0x06] (fun s => s.RIP = 0x129a78) (shrR64Effect 0x129a78 4 12 6)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR64Effect_footprint 0x129a78 4 12 6).toInstrSpec (shr_r64_imm8_effect_step 0x129a78 0x49 0xec 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x129a7c [0x4D, 0x09, 0xF4] (fun s => s.RIP = 0x129a7c) (orR64R64Effect 0x129a7c 12 14)
      [.gpr 12, .gpr 14] [] [.reg 12, .flags, .rip] :=
    (orR64R64Effect_footprint 0x129a7c 12 14).toInstrSpec (or_r64_r64_effect_step 0x129a7c 0x4d 0xf4 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x129a7f [0x4D, 0x21, 0xC4] (fun s => s.RIP = 0x129a7f) (andR64R64Effect 0x129a7f 12 8)
      [.gpr 12, .gpr 8] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x129a7f 12 8).toInstrSpec (and_r64_r64_effect_step 0x129a7f 0x4d 0xc4 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x129a82 [0x4C, 0x8B, 0x6B, 0x10] (LoadPre 0x129a82 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x129a82 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129a82 13 (.base 3 (.d8 0x10)))
      [.gpr 3] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x129a82 13 (.base 3 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x129a82 0x4c (by decide) 5 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x129a86 [0x4D, 0x89, 0xEE] (fun s => s.RIP = 0x129a86) (movR64R64Effect 0x129a86 14 13)
      [.gpr 13] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x129a86 14 13).toInstrSpec (mov_r64_r64_effect_step 0x129a86 0x4d 0xee (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x129a89 [0x49, 0xF7, 0xD6] (fun s => s.RIP = 0x129a89) (notR64Effect 0x129a89 14)
      [.gpr 14] [] [.reg 14, .rip] :=
    (notR64Effect_footprint 0x129a89 14).toInstrSpec (not_r64_effect_step 0x129a89 0x49 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x129a8c [0x49, 0xC1, 0xEE, 0x07] (fun s => s.RIP = 0x129a8c) (shrR64Effect 0x129a8c 4 14 7)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64Effect_footprint 0x129a8c 4 14 7).toInstrSpec (shr_r64_imm8_effect_step 0x129a8c 0x49 0xee 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x129a90 [0x49, 0xC1, 0xED, 0x06] (fun s => s.RIP = 0x129a90) (shrR64Effect 0x129a90 4 13 6)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR64Effect_footprint 0x129a90 4 13 6).toInstrSpec (shr_r64_imm8_effect_step 0x129a90 0x49 0xed 0x6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a53) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a57) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a5a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 59), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a5d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a61) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a65) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a68) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 14), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a6b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a6e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a71) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a74) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 75), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a78) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 61), (14, 75), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a7c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 79), (13, 61), (14, 75), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a7f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 61), (14, 75), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a82) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 83), (14, 75), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a86) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 83), (14, 85), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a89) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 83), (14, 87), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a8c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 83), (14, 89), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a90) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 91), (14, 89), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129a94) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l129a50_1 code

theorem block_l129a50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129a50 :=
  Rest.liftedBlock (rest_l129a50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129a50 x hx)

theorem rest_l129ac4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129ac4 bytes_l129ac4) (entryMap (live .l129ac4))
      1 0x129ac4 bytes_l129ac4 b_l129ac4 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x129ac4 0xffffff1a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l129ac4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129ac4 :=
  Rest.liftedBlock (rest_l129ac4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129ac4 x hx)

theorem rest_l129ac9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129ac9 bytes_l129ac9) (entryMap (live .l129ac9))
      11 0x129ac9 bytes_l129ac9 b_l129ac9 := by
  have f0 : InstrSpec 0x129ac9 [0x41, 0x81, 0xE2, 0xFC, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129ac9) (andR32Imm32Effect 0x129ac9 7 10 0xfc)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x129ac9 7 10 0xfc).toInstrSpec (and_r32_imm32_rex_effect_step 0x129ac9 0x41 0xe2 0xfc (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129ad0 [0x44, 0x89, 0xD1] (fun s => s.RIP = 0x129ad0) (movR32R32Effect 0x129ad0 3 1 10)
      [.gpr 10] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x129ad0 3 1 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x129ad0 0x44 0xd1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129ad3 [0x49, 0x8B, 0x0C, 0xC9] (LoadPre 0x129ad3 (fun s => AddrMode.addr (.sib 9 (some 1) 3 .none) s (0x129ad3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129ad3 1 (.sib 9 (some 1) 3 .none))
      [.gpr 9, .gpr 1] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x129ad3 1 (.sib 9 (some 1) 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x129ad3 0x49 (by decide) 1 (.sib 9 (some 1) 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x129ad7 [0x48, 0x89, 0xCF] (fun s => s.RIP = 0x129ad7) (movR64R64Effect 0x129ad7 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x129ad7 7 1).toInstrSpec (mov_r64_r64_effect_step 0x129ad7 0x48 0xcf (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129ada [0x48, 0xF7, 0xD7] (fun s => s.RIP = 0x129ada) (notR64Effect 0x129ada 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (notR64Effect_footprint 0x129ada 7).toInstrSpec (not_r64_effect_step 0x129ada 0x48 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x129add [0x48, 0xC1, 0xEF, 0x07] (fun s => s.RIP = 0x129add) (shrR64Effect 0x129add 4 7 7)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x129add 4 7 7).toInstrSpec (shr_r64_imm8_effect_step 0x129add 0x48 0xef 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129ae1 [0x48, 0xC1, 0xE9, 0x06] (fun s => s.RIP = 0x129ae1) (shrR64Effect 0x129ae1 4 1 6)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x129ae1 4 1 6).toInstrSpec (shr_r64_imm8_effect_step 0x129ae1 0x48 0xe9 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129ae5 [0x48, 0x09, 0xF9] (fun s => s.RIP = 0x129ae5) (orR64R64Effect 0x129ae5 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x129ae5 1 7).toInstrSpec (or_r64_r64_effect_step 0x129ae5 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x129ae8 [0x4C, 0x21, 0xC1] (fun s => s.RIP = 0x129ae8) (andR64R64Effect 0x129ae8 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x129ae8 1 8).toInstrSpec (and_r64_r64_effect_step 0x129ae8 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x129aeb [0x41, 0x83, 0xFB, 0x01] (fun s => s.RIP = 0x129aeb) (cmpR32Imm8Effect 0x129aeb 4 11 0x1)
      [.gpr 11] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x129aeb 4 11 0x1).toInstrSpec (cmp_r32_imm8_rex_effect_step 0x129aeb 0x41 0xfb 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ad0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ad3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ad7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ada) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129add) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ae1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ae5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ae8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129aeb) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 69), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 53), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129aef) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 73) (jcc_rel8_effect_step 0x129aef 4 0x3e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129ac9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129ac9 :=
  Rest.liftedBlock (rest_l129ac9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129ac9 x hx)

theorem rest_l129af1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129af1 bytes_l129af1) (entryMap (live .l129af1))
      10 0x129af1 bytes_l129af1 b_l129af1 := by
  have f0 : InstrSpec 0x129af1 [0x4B, 0x8B, 0x7C, 0xD1, 0x08] (LoadPre 0x129af1 (fun s => AddrMode.addr (.sib 9 (some 10) 3 (.d8 0x8)) s (0x129af1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x129af1 7 (.sib 9 (some 10) 3 (.d8 0x8)))
      [.gpr 9, .gpr 10] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x129af1 7 (.sib 9 (some 10) 3 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x129af1 0x4b (by decide) 7 (.sib 9 (some 10) 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x129af6 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x129af6) (movR64R64Effect 0x129af6 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x129af6 3 7).toInstrSpec (mov_r64_r64_effect_step 0x129af6 0x48 0xfb (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129af9 [0x48, 0xF7, 0xD3] (fun s => s.RIP = 0x129af9) (notR64Effect 0x129af9 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (notR64Effect_footprint 0x129af9 3).toInstrSpec (not_r64_effect_step 0x129af9 0x48 0xd3 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129afc [0x48, 0xC1, 0xEB, 0x07] (fun s => s.RIP = 0x129afc) (shrR64Effect 0x129afc 4 3 7)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x129afc 4 3 7).toInstrSpec (shr_r64_imm8_effect_step 0x129afc 0x48 0xeb 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129b00 [0x48, 0xC1, 0xEF, 0x06] (fun s => s.RIP = 0x129b00) (shrR64Effect 0x129b00 4 7 6)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x129b00 4 7 6).toInstrSpec (shr_r64_imm8_effect_step 0x129b00 0x48 0xef 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x129b04 [0x48, 0x09, 0xDF] (fun s => s.RIP = 0x129b04) (orR64R64Effect 0x129b04 7 3)
      [.gpr 7, .gpr 3] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x129b04 7 3).toInstrSpec (or_r64_r64_effect_step 0x129b04 0x48 0xdf (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129b07 [0x4C, 0x21, 0xC7] (fun s => s.RIP = 0x129b07) (andR64R64Effect 0x129b07 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x129b07 7 8).toInstrSpec (and_r64_r64_effect_step 0x129b07 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129b0a [0x48, 0x01, 0xF9] (fun s => s.RIP = 0x129b0a) (addR64R64Effect 0x129b0a 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129b0a 1 7).toInstrSpec (add_r64_r64_effect_step 0x129b0a 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x129b0d [0x41, 0x83, 0xFB, 0x02] (fun s => s.RIP = 0x129b0d) (cmpR32Imm8Effect 0x129b0d 4 11 0x2)
      [.gpr 11] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x129b0d 4 11 0x2).toInstrSpec (cmp_r32_imm8_rex_effect_step 0x129b0d 0x41 0xfb 0x2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129af6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129af9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129afc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b00) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b04) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b07) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b0a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b0d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 67), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b11) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel8_effect_step 0x129b11 4 0x1c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129af1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129af1 :=
  Rest.liftedBlock (rest_l129af1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129af1 x hx)

theorem rest_l129b13 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129b13 bytes_l129b13) (entryMap (live .l129b13))
      8 0x129b13 bytes_l129b13 b_l129b13 := by
  have f0 : InstrSpec 0x129b13 [0x4B, 0x8B, 0x7C, 0xD1, 0x10] (LoadPre 0x129b13 (fun s => AddrMode.addr (.sib 9 (some 10) 3 (.d8 0x10)) s (0x129b13 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x129b13 7 (.sib 9 (some 10) 3 (.d8 0x10)))
      [.gpr 9, .gpr 10] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x129b13 7 (.sib 9 (some 10) 3 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x129b13 0x4b (by decide) 7 (.sib 9 (some 10) 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x129b18 [0x49, 0x89, 0xF9] (fun s => s.RIP = 0x129b18) (movR64R64Effect 0x129b18 9 7)
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x129b18 9 7).toInstrSpec (mov_r64_r64_effect_step 0x129b18 0x49 0xf9 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129b1b [0x49, 0xF7, 0xD1] (fun s => s.RIP = 0x129b1b) (notR64Effect 0x129b1b 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (notR64Effect_footprint 0x129b1b 9).toInstrSpec (not_r64_effect_step 0x129b1b 0x49 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129b1e [0x49, 0xC1, 0xE9, 0x07] (fun s => s.RIP = 0x129b1e) (shrR64Effect 0x129b1e 4 9 7)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x129b1e 4 9 7).toInstrSpec (shr_r64_imm8_effect_step 0x129b1e 0x49 0xe9 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129b22 [0x48, 0xC1, 0xEF, 0x06] (fun s => s.RIP = 0x129b22) (shrR64Effect 0x129b22 4 7 6)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x129b22 4 7 6).toInstrSpec (shr_r64_imm8_effect_step 0x129b22 0x48 0xef 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x129b26 [0x4C, 0x09, 0xCF] (fun s => s.RIP = 0x129b26) (orR64R64Effect 0x129b26 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x129b26 7 9).toInstrSpec (or_r64_r64_effect_step 0x129b26 0x4c 0xcf (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129b29 [0x4C, 0x21, 0xC7] (fun s => s.RIP = 0x129b29) (andR64R64Effect 0x129b29 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x129b29 7 8).toInstrSpec (and_r64_r64_effect_step 0x129b29 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129b2c [0x48, 0x01, 0xF9] (fun s => s.RIP = 0x129b2c) (addR64R64Effect 0x129b2c 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129b2c 1 7).toInstrSpec (add_r64_r64_effect_step 0x129b2c 0x48 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b18) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b1b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 57), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b1e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 59), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b22) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 59), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b26) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 59), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b29) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 59), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b2c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 59), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b2f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 69) (by decide) rfl

theorem block_l129b13 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129b13 :=
  Rest.liftedBlock (rest_l129b13 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129b13 x hx)

theorem rest_l129b2f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129b2f bytes_l129b2f) (entryMap (live .l129b2f))
      8 0x129b2f bytes_l129b2f b_l129b2f := by
  have f0 : InstrSpec 0x129b2f [0x48, 0x89, 0xCF] (fun s => s.RIP = 0x129b2f) (movR64R64Effect 0x129b2f 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x129b2f 7 1).toInstrSpec (mov_r64_r64_effect_step 0x129b2f 0x48 0xcf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129b32 [0x48, 0x21, 0xF7] (fun s => s.RIP = 0x129b32) (andR64R64Effect 0x129b32 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x129b32 7 6).toInstrSpec (and_r64_r64_effect_step 0x129b32 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129b35 [0x48, 0xC1, 0xE9, 0x08] (fun s => s.RIP = 0x129b35) (shrR64Effect 0x129b35 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x129b35 4 1 8).toInstrSpec (shr_r64_imm8_effect_step 0x129b35 0x48 0xe9 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129b39 [0x48, 0x21, 0xF1] (fun s => s.RIP = 0x129b39) (andR64R64Effect 0x129b39 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x129b39 1 6).toInstrSpec (and_r64_r64_effect_step 0x129b39 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129b3c [0x48, 0x01, 0xF9] (fun s => s.RIP = 0x129b3c) (addR64R64Effect 0x129b3c 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129b3c 1 7).toInstrSpec (add_r64_r64_effect_step 0x129b3c 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x129b3f [0x48, 0x0F, 0xAF, 0xCA] (fun s => s.RIP = 0x129b3f) (imulR64R64Effect 0x129b3f 4 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x129b3f 4 1 2).toInstrSpec (imul_r64_r64_effect_step 0x129b3f 0x48 (by decide) 0xca (by decide)) pre_rip
  have f6 : InstrSpec 0x129b43 [0x48, 0xC1, 0xE9, 0x30] (fun s => s.RIP = 0x129b43) (shrR64Effect 0x129b43 4 1 48)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x129b43 4 1 48).toInstrSpec (shr_r64_imm8_effect_step 0x129b43 0x48 0xe9 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129b47 [0x48, 0x01, 0xC8] (fun s => s.RIP = 0x129b47) (addR64R64Effect 0x129b47 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129b47 0 1).toInstrSpec (add_r64_r64_effect_step 0x129b47 0x48 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b32) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b35) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b39) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b3c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b3f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b43) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b47) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 65), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b4a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 69) (by decide) rfl

theorem block_l129b2f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129b2f :=
  Rest.liftedBlock (rest_l129b2f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129b2f x hx)

theorem rest_l129b4a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129b4a bytes_l129b4a) (entryMap (live .l129b4a))
      6 0x129b4a bytes_l129b4a b_l129b4a := by
  have f0 : InstrSpec 0x129b4a [0x5B] (PopPre 0x129b4a) (popR64Effect 0x129b4a 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129b4a 1 3).toInstrSpec (pop_r64_effect_step 0x129b4a 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129b4b [0x41, 0x5C] (PopPre 0x129b4b) (popR64Effect 0x129b4b 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129b4b 2 12).toInstrSpec (pop_r64_rex_effect_step 0x129b4b 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x129b4d [0x41, 0x5D] (PopPre 0x129b4d) (popR64Effect 0x129b4d 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129b4d 2 13).toInstrSpec (pop_r64_rex_effect_step 0x129b4d 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x129b4f [0x41, 0x5E] (PopPre 0x129b4f) (popR64Effect 0x129b4f 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129b4f 2 14).toInstrSpec (pop_r64_rex_effect_step 0x129b4f 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x129b51 [0x41, 0x5F] (PopPre 0x129b51) (popR64Effect 0x129b51 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129b51 2 15).toInstrSpec (pop_r64_rex_effect_step 0x129b51 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x129b53 [0xC3] (RetPre 0x129b53) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x129b53).toInstrSpec (ret_effect_step 0x129b53) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b4b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b4d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b4f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 59), (14, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b51) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 59), (14, 62), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129b53) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 59), (14, 62), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l129b4a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129b4a :=
  Rest.liftedBlock (rest_l129b4a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129b4a x hx)

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

theorem_by block_l1297a0_eval :
    program.runBlock (dialect code) ⟨.l1297a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1297b6_eval :
    program.runBlock (dialect code) ⟨.l1297b6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1297bb_eval :
    program.runBlock (dialect code) ⟨.l1297bb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1297c6_eval :
    program.runBlock (dialect code) ⟨.l1297c6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1297cf_eval :
    program.runBlock (dialect code) ⟨.l1297cf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1297d8_eval :
    program.runBlock (dialect code) ⟨.l1297d8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1297eb_eval :
    program.runBlock (dialect code) ⟨.l1297eb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1297f3_eval :
    program.runBlock (dialect code) ⟨.l1297f3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12980a_eval :
    program.runBlock (dialect code) ⟨.l12980a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129815_eval :
    program.runBlock (dialect code) ⟨.l129815, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129818_eval :
    program.runBlock (dialect code) ⟨.l129818, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129820_eval :
    program.runBlock (dialect code) ⟨.l129820, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129860_eval :
    program.runBlock (dialect code) ⟨.l129860, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129865_eval :
    program.runBlock (dialect code) ⟨.l129865, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129870_eval :
    program.runBlock (dialect code) ⟨.l129870, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129885_eval :
    program.runBlock (dialect code) ⟨.l129885, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129886_eval :
    program.runBlock (dialect code) ⟨.l129886, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1298a0_eval :
    program.runBlock (dialect code) ⟨.l1298a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1298e6_eval :
    program.runBlock (dialect code) ⟨.l1298e6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1298eb_eval :
    program.runBlock (dialect code) ⟨.l1298eb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129900_eval :
    program.runBlock (dialect code) ⟨.l129900, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129915_eval :
    program.runBlock (dialect code) ⟨.l129915, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129921_eval :
    program.runBlock (dialect code) ⟨.l129921, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12993c_eval :
    program.runBlock (dialect code) ⟨.l12993c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129950_eval :
    program.runBlock (dialect code) ⟨.l129950, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129964_eval :
    program.runBlock (dialect code) ⟨.l129964, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129978_eval :
    program.runBlock (dialect code) ⟨.l129978, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12998c_eval :
    program.runBlock (dialect code) ⟨.l12998c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1299a0_eval :
    program.runBlock (dialect code) ⟨.l1299a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1299b0_eval :
    program.runBlock (dialect code) ⟨.l1299b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1299b2_eval :
    program.runBlock (dialect code) ⟨.l1299b2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1299e0_eval :
    program.runBlock (dialect code) ⟨.l1299e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1299e3_eval :
    program.runBlock (dialect code) ⟨.l1299e3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129a14_eval :
    program.runBlock (dialect code) ⟨.l129a14, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129a1d_eval :
    program.runBlock (dialect code) ⟨.l129a1d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129a45_eval :
    program.runBlock (dialect code) ⟨.l129a45, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129a50_eval :
    program.runBlock (dialect code) ⟨.l129a50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129ac4_eval :
    program.runBlock (dialect code) ⟨.l129ac4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129ac9_eval :
    program.runBlock (dialect code) ⟨.l129ac9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129af1_eval :
    program.runBlock (dialect code) ⟨.l129af1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129b13_eval :
    program.runBlock (dialect code) ⟨.l129b13, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129b2f_eval :
    program.runBlock (dialect code) ⟨.l129b2f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129b4a_eval :
    program.runBlock (dialect code) ⟨.l129b4a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Sec1.LIR
