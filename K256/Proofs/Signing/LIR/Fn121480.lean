import K256.Proofs.Signing.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Signing.LIR.Generated.Values

namespace K256.Proofs.Signing.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR K256.Proofs.Verify.LIR

theorem rest_l121480 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121480 bytes_l121480) (entryMap (live .l121480))
      13 0x121480 bytes_l121480 b_l121480 := by
  have f0 : InstrSpec 0x121480 [0x55] (PushPre 0x121480 1) (pushR64Effect 0x121480 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x121480 1 5).toInstrSpec (push_r64_effect_step 0x121480 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x121481 [0x41, 0x57] (PushPre 0x121481 2) (pushR64Effect 0x121481 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x121481 2 15).toInstrSpec (push_r64_rex_effect_step 0x121481 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x121483 [0x41, 0x56] (PushPre 0x121483 2) (pushR64Effect 0x121483 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x121483 2 14).toInstrSpec (push_r64_rex_effect_step 0x121483 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x121485 [0x41, 0x54] (PushPre 0x121485 2) (pushR64Effect 0x121485 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x121485 2 12).toInstrSpec (push_r64_rex_effect_step 0x121485 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x121487 [0x53] (PushPre 0x121487 1) (pushR64Effect 0x121487 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x121487 1 3).toInstrSpec (push_r64_effect_step 0x121487 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x121488 [0x48, 0x83, 0xEC, 0x60] (fun s => s.RIP = 0x121488) (subR64Imm8Effect 0x121488 4 0x60)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x121488 4 0x60).toInstrSpec (sub_r64_imm8_effect_step 0x121488 0x48 0xec 0x60 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12148c [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x12148c) (movR64R64Effect 0x12148c 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12148c 2 6).toInstrSpec (mov_r64_r64_effect_step 0x12148c 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12148f [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x12148f) (movR64R64Effect 0x12148f 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x12148f 3 7).toInstrSpec (mov_r64_r64_effect_step 0x12148f 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x121492 [0x0F, 0xB6, 0x06] (LoadPre 0x121492 (fun s => AddrMode.addr (.base 6 .none) s (0x121492 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x121492 3 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x121492 3 0 (.base 6 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x121492 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x121495 [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x121495) (movzxR32R8Effect 0x121495 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x121495 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x121495 0xc8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x121498 [0x8D, 0x71, 0xFE] (fun s => s.RIP = 0x121498) (leaR32Effect 0x121498 3 6 (.base 1 (.d8 0xfe)))
      [.gpr 1] [] [.reg 6, .rip] :=
    (leaR32Effect_footprint 0x121498 3 6 (.base 1 (.d8 0xfe))).toInstrSpec (lea_r32_effect_step 0x121498 6 (.base 1 (.d8 0xfe)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12149b [0x83, 0xFE, 0x04] (fun s => s.RIP = 0x12149b) (cmpR32Imm8Effect 0x12149b 3 6 0x4)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x12149b 3 6 0x4).toInstrSpec (cmp_r32_imm8_effect_step 0x12149b 0xfe 0x4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121481) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121483) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121485) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121487) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121488) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12148c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 65), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12148f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 65), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121492) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (2, 65), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121495) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 71), (2, 65), (3, 67), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121498) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 71), (2, 65), (3, 67), (4, 63), (5, 5), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12149b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 69), (1, 71), (2, 65), (3, 67), (4, 63), (5, 5), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12149e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 77) (jcc_rel8_effect_step 0x12149e 3 0x30) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l121480 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121480 :=
  Rest.liftedBlock (rest_l121480 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121480 x hx)

theorem rest_l1214a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1214a0 bytes_l1214a0) (entryMap (live .l1214a0))
      5 0x1214a0 bytes_l1214a0 b_l1214a0 := by
  have f0 : InstrSpec 0x1214a0 [0x4C, 0x8D, 0x72, 0x01] (fun s => s.RIP = 0x1214a0) (leaR64Effect 0x1214a0 14 (.base 2 (.d8 0x1)))
      [.gpr 2] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x1214a0 14 (.base 2 (.d8 0x1))).toInstrSpec (lea_r64_effect_step 0x1214a0 0x4c (by decide) 6 (.base 2 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1214a4 [0x89, 0xC1] (fun s => s.RIP = 0x1214a4) (movR32R32Effect 0x1214a4 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1214a4 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1214a4 0xc1 (by decide)) pre_rip
  have f2 : InstrSpec 0x1214a6 [0x80, 0xE1, 0x06] (fun s => s.RIP = 0x1214a6) (andR8Imm8Effect 0x1214a6 3 1 0x6)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x1214a6 3 1 0x6).toInstrSpec (and_r8_imm8_effect_step 0x1214a6 0xe1 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1214a9 [0x80, 0xF9, 0x02] (fun s => s.RIP = 0x1214a9) (cmpR8Imm8Effect 0x1214a9 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1214a9 3 1 0x2).toInstrSpec (cmp_r8_imm8_effect_step 0x1214a9 0xf9 0x2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214a4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214a6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214a9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214ac) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x1214ac 5 0x7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1214a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1214a0 :=
  Rest.liftedBlock (rest_l1214a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1214a0 x hx)

theorem rest_l1214ae [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1214ae bytes_l1214ae) (entryMap (live .l1214ae))
      3 0x1214ae bytes_l1214ae b_l1214ae := by
  have f0 : InstrSpec 0x1214ae [0x24, 0x01] (fun s => s.RIP = 0x1214ae) (andAlImm8Effect 0x1214ae 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x1214ae 0x1).toInstrSpec (and_al_imm8_effect_step 0x1214ae 0x1) pre_rip
  have f1 : InstrSpec 0x1214b0 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x1214b0) (movzxR32R8Effect 0x1214b0 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x1214b0 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x1214b0 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214b0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214b3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x1214b3 0x6 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1214ae [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1214ae :=
  Rest.liftedBlock (rest_l1214ae code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1214ae x hx)

theorem rest_l1214b5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1214b5 bytes_l1214b5) (entryMap (live .l1214b5))
      2 0x1214b5 bytes_l1214b5 b_l1214b5 := by
  have f0 : InstrSpec 0x1214b5 [0x3C, 0x05] (fun s => s.RIP = 0x1214b5) (cmpAlImm8Effect 0x1214b5 0x5)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x1214b5 0x5).toInstrSpec (cmp_al_imm8_effect_step 0x1214b5 0x5) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214b7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1214b7 5 0x3a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1214b5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1214b5 :=
  Rest.liftedBlock (rest_l1214b5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1214b5 x hx)

theorem rest_l1214b9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1214b9 bytes_l1214b9) (entryMap (live .l1214b9))
      1 0x1214b9 bytes_l1214b9 b_l1214b9 := by
  have f0 : InstrSpec 0x1214b9 [0x31, 0xFF] (fun s => s.RIP = 0x1214b9) (xorR32R32Effect 0x1214b9 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1214b9 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x1214b9 0xff (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214bb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1214b9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1214b9 :=
  Rest.liftedBlock (rest_l1214b9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1214b9 x hx)

theorem rest_l1214bb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1214bb bytes_l1214bb) (entryMap (live .l1214bb))
      1 0x1214bb bytes_l1214bb b_l1214bb := by
  have f0 : InstrSpec 0x1214bb [0xE8, 0x90, 0x68, 0x00, 0x00] (PushPre 0x1214bb 5) (callEffect (fun _ => 0x127d50) 0x1214c0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1214bb 0x127d50 0x1214c0).toInstrSpec (call_rel32_effect_step 0x1214bb 0x6890 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f0 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 55) (by decide) (by decide) rfl rfl

theorem block_l1214bb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1214bb :=
  Rest.liftedBlock (rest_l1214bb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1214bb x hx)

theorem rest_l1214c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1214c0 bytes_l1214c0) (entryMap (live .l1214c0))
      4 0x1214c0 bytes_l1214c0 b_l1214c0 := by
  have f0 : InstrSpec 0x1214c0 [0x0F, 0xB6, 0xD0] (fun s => s.RIP = 0x1214c0) (movzxR32R8Effect 0x1214c0 3 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x1214c0 3 2 0).toInstrSpec (movzx_r32_r8_effect_step 0x1214c0 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1214c3 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x1214c3) (movR64R64Effect 0x1214c3 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1214c3 7 4).toInstrSpec (mov_r64_r64_effect_step 0x1214c3 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1214c6 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1214c6) (movR64R64Effect 0x1214c6 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1214c6 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1214c6 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1214c9 [0xE8, 0xE2, 0xF0, 0xFF, 0xFF] (PushPre 0x1214c9 5) (callEffect (fun _ => 0x1205b0) 0x1214ce)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1214c9 0x1205b0 0x1214ce).toInstrSpec (call_rel32_effect_step 0x1214c9 0xfffff0e2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214c3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214c6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214c9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205b0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1214c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1214c0 :=
  Rest.liftedBlock (rest_l1214c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1214c0 x hx)

theorem rest_l1214ce [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1214ce bytes_l1214ce) (entryMap (live .l1214ce))
      1 0x1214ce bytes_l1214ce b_l1214ce := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x1214ce 0x32 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1214ce [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1214ce :=
  Rest.liftedBlock (rest_l1214ce code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1214ce x hx)

theorem rest_l1214d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1214d0 bytes_l1214d0) (entryMap (live .l1214d0))
      2 0x1214d0 bytes_l1214d0 b_l1214d0 := by
  have f0 : InstrSpec 0x1214d0 [0x85, 0xC9] (fun s => s.RIP = 0x1214d0) (testR32R32Effect 0x1214d0 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR32R32Effect_footprint 0x1214d0 2 1 1).toInstrSpec (test_r32_r32_effect_step 0x1214d0 0xc9 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214d2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1214d2 5 0xd1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1214d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1214d0 :=
  Rest.liftedBlock (rest_l1214d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1214d0 x hx)

theorem rest_l1214d8 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1214d8 bytes_l1214d8) (entryMap (live .l1214d8))
      6 0x1214d8 bytes_l1214d8 b_l1214d8 := by
  have f0 : InstrSpec 0x1214d8 [0xB9, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1214d8) (movR32Imm32Effect 0x1214d8 5 1 0xb)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1214d8 5 1 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x1214d8 0xb9 (by decide) 0xb) pre_rip
  have f1 : InstrSpec 0x1214dd [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x1214dd) (movR64R64Effect 0x1214dd 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1214dd 7 3).toInstrSpec (mov_r64_r64_effect_step 0x1214dd 0x48 0xdf (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1214e0 [0x48, 0xC7, 0xC6, 0xA8, 0x33, 0x20, 0x00] (fun s => s.RIP = 0x1214e0) (movR64Imm32Effect 0x1214e0 6 0x2033a8)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x1214e0 6 0x2033a8).toInstrSpec (mov_r64_imm32_effect_step 0x1214e0 0x48 0xc6 (by decide) (by decide) (by decide) 0x2033a8) pre_rip
  have f3 : InstrSpec 0x1214e7 [0xF3, 0x48, 0xA5] (RepPre 0x1214e7 (RepMovsqPre 0x1214e7)) (repMovsqEffect 0x1214e7)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x1214e7).toInstrSpecOfRuns (rep_movsq_runs hstride 0x1214e7 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x1214ea [0xC6, 0x43, 0x58, 0x01] (StorePre 0x1214ea 4 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x1214ea + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1214ea (.base 3 (.d8 0x58)) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1214ea (.base 3 (.d8 0x58)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x1214ea (.base 3 (.d8 0x58)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214dd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214e0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214e7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 61) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (6, 59), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214ea) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (6, 59), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214ee) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 64) (jmp_rel32_effect_step 0x1214ee 0xa6 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1214d8 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1214d8 :=
  Rest.liftedBlock (rest_l1214d8 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1214d8 x hx)

theorem rest_l1214f3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1214f3 bytes_l1214f3) (entryMap (live .l1214f3))
      4 0x1214f3 bytes_l1214f3 b_l1214f3 := by
  have f0 : InstrSpec 0x1214f3 [0x48, 0x83, 0xC2, 0x21] (fun s => s.RIP = 0x1214f3) (addR64Imm8Effect 0x1214f3 2 0x21)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1214f3 2 0x21).toInstrSpec (add_r64_imm8_effect_step 0x1214f3 0x48 0xc2 0x21 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1214f7 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x1214f7) (movR64R64Effect 0x1214f7 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1214f7 7 4).toInstrSpec (mov_r64_r64_effect_step 0x1214f7 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1214fa [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1214fa) (movR64R64Effect 0x1214fa 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1214fa 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1214fa 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1214fd [0xE8, 0x7E, 0xE2, 0xFF, 0xFF] (PushPre 0x1214fd 5) (callEffect (fun _ => 0x11f780) 0x121502)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1214fd 0x11f780 0x121502).toInstrSpec (call_rel32_effect_step 0x1214fd 0xffffe27e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214f7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214fa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1214fd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11f780) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1214f3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1214f3 :=
  Rest.liftedBlock (rest_l1214f3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1214f3 x hx)

theorem rest_l121502_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x121502 bytes_l121502) [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]
      20 0x121551 bytes_l121502_1 b_l121502_1 := by
  have f20 : InstrSpec 0x121551 [0x4C, 0x8B, 0x64, 0x24, 0x40] (LoadPre 0x121551 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x121551 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121551 12 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x121551 12 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x121551 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x121556 [0x49, 0x21, 0xD4] (fun s => s.RIP = 0x121556) (andR64R64Effect 0x121556 12 2)
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x121556 12 2).toInstrSpec (and_r64_r64_effect_step 0x121556 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x121559 [0x48, 0x23, 0x54, 0x24, 0x48] (LoadPre 0x121559 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x121559 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x121559 2 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (andR64M64Effect_footprint 0x121559 2 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (and_r64_m64_effect_step 0x121559 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x12155e [0x89, 0xC5] (fun s => s.RIP = 0x12155e) (movR32R32Effect 0x12155e 2 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x12155e 2 5 0).toInstrSpec (mov_r32_r32_effect_step 0x12155e 0xc5 (by decide)) pre_rip
  have f24 : InstrSpec 0x121560 [0x40, 0xF6, 0xDD] (fun s => s.RIP = 0x121560) (negR8Effect 0x121560 3 5)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (negR8Effect_footprint 0x121560 3 5).toInstrSpec (neg_r8_rex_effect_step 0x121560 0x40 0xdd (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x121563 [0x80, 0xF1, 0x01] (fun s => s.RIP = 0x121563) (xorR8Imm8Effect 0x121563 3 1 0x1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR8Imm8Effect_footprint 0x121563 3 1 0x1).toInstrSpec (xor_r8_imm8_effect_step 0x121563 0xf1 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x121566 [0x40, 0x20, 0xE9] (fun s => s.RIP = 0x121566) (andR8R8Effect 0x121566 3 1 5)
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (andR8R8Effect_footprint 0x121566 3 1 5).toInstrSpec (and_r8_r8_rex_effect_step 0x121566 0x40 0xe9 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x121569 [0x80, 0xF1, 0x01] (fun s => s.RIP = 0x121569) (xorR8Imm8Effect 0x121569 3 1 0x1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR8Imm8Effect_footprint 0x121569 3 1 0x1).toInstrSpec (xor_r8_imm8_effect_step 0x121569 0xf1 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x12156c [0x48, 0x89, 0x33] (StorePre 0x12156c 3 (fun s => AddrMode.addr (.base 3 .none) s (0x12156c + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x12156c 6 (.base 3 .none))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12156c 6 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x12156c 0x48 (by decide) 6 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x12156f [0x48, 0x89, 0x7B, 0x08] (StorePre 0x12156f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12156f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12156f 7 (.base 3 (.d8 0x8)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12156f 7 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12156f 0x48 (by decide) 7 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x121573 [0x4C, 0x89, 0x43, 0x10] (StorePre 0x121573 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x121573 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x121573 8 (.base 3 (.d8 0x10)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x121573 8 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x121573 0x4c (by decide) 0 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x121577 [0x4C, 0x89, 0x4B, 0x18] (StorePre 0x121577 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x121577 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x121577 9 (.base 3 (.d8 0x18)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x121577 9 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x121577 0x4c (by decide) 1 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x12157b [0x4C, 0x89, 0x53, 0x20] (StorePre 0x12157b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x12157b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12157b 10 (.base 3 (.d8 0x20)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12157b 10 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x12157b 0x4c (by decide) 2 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x12157f [0x4C, 0x89, 0x5B, 0x28] (StorePre 0x12157f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x12157f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12157f 11 (.base 3 (.d8 0x28)))
      [.gpr 11, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12157f 11 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x12157f 0x4c (by decide) 3 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x121583 [0x4C, 0x89, 0x73, 0x30] (StorePre 0x121583 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x121583 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x121583 14 (.base 3 (.d8 0x30)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x121583 14 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x121583 0x4c (by decide) 6 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x121587 [0x4C, 0x89, 0x7B, 0x38] (StorePre 0x121587 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x121587 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x121587 15 (.base 3 (.d8 0x38)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x121587 15 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x121587 0x4c (by decide) 7 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x12158b [0x4C, 0x89, 0x63, 0x40] (StorePre 0x12158b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x12158b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12158b 12 (.base 3 (.d8 0x40)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12158b 12 (.base 3 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x12158b 0x4c (by decide) 4 (.base 3 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x12158f [0x48, 0x89, 0x53, 0x48] (StorePre 0x12158f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x12158f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12158f 2 (.base 3 (.d8 0x48)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12158f 2 (.base 3 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x12158f 0x48 (by decide) 2 (.base 3 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x121593 [0x88, 0x4B, 0x50] (StorePre 0x121593 3 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x121593 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x121593 3 1 (.base 3 (.d8 0x50)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x121593 3 1 (.base 3 (.d8 0x50))).toInstrSpec (mov_m8_r8_effect_step 0x121593 1 (by decide) (.base 3 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x121596 [0x88, 0x43, 0x58] (StorePre 0x121596 3 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x121596 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x121596 3 0 (.base 3 (.d8 0x58)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x121596 3 0 (.base 3 (.d8 0x58))).toInstrSpec (mov_m8_r8_effect_step 0x121596 0 (by decide) (.base 3 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 93), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121556) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121559) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 53), (1, 55), (2, 97), (3, 3), (4, 4), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12155e) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 53), (1, 55), (2, 97), (3, 3), (4, 4), (5, 99), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121560) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 53), (1, 55), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121563) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 53), (1, 103), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121566) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 53), (1, 105), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121569) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 53), (1, 107), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12156c) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.exec (n := 109) (ρ' := [(0, 53), (1, 107), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12156f) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 53), (1, 107), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121573) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.exec (n := 111) (ρ' := [(0, 53), (1, 107), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121577) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 53), (1, 107), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12157b) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 53), (1, 107), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12157f) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 114) (RestInside.exec (n := 114) (ρ' := [(0, 53), (1, 107), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121583) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 53), (1, 107), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121587) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.exec (n := 116) (ρ' := [(0, 53), (1, 107), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12158b) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 117) (RestInside.exec (n := 117) (ρ' := [(0, 53), (1, 107), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12158f) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 118) (RestInside.exec (n := 118) (ρ' := [(0, 53), (1, 107), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121593) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 119) (RestInside.exec (n := 119) (ρ' := [(0, 53), (1, 107), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121596) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 120) (RestInside.exec (n := 120) (ρ' := [(0, 53), (1, 107), (2, 97), (3, 3), (4, 4), (5, 101), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (12, 95), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121599) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 121) (by decide) rfl

theorem rest_l121502 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121502 bytes_l121502) (entryMap (live .l121502))
      40 0x121502 bytes_l121502 b_l121502 := by
  have f0 : InstrSpec 0x121502 [0x0F, 0xB6, 0x44, 0x24, 0x58] (LoadPre 0x121502 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x121502 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x121502 5 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x121502 5 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (movzx_r32_m8_effect_step 0x121502 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x121507 [0x0F, 0xB6, 0x4C, 0x24, 0x50] (LoadPre 0x121507 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x121507 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x121507 5 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x121507 5 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (movzx_r32_m8_effect_step 0x121507 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12150c [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x12150c) (movR64R64Effect 0x12150c 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12150c 2 0).toInstrSpec (mov_r64_r64_effect_step 0x12150c 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12150f [0x48, 0xF7, 0xDA] (fun s => s.RIP = 0x12150f) (negR64Effect 0x12150f 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR64Effect_footprint 0x12150f 2).toInstrSpec (neg_r64_effect_step 0x12150f 0x48 0xda (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x121512 [0x48, 0x8B, 0x34, 0x24] (LoadPre 0x121512 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x121512 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x121512 6 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x121512 6 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x121512 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x121516 [0x48, 0x21, 0xD6] (fun s => s.RIP = 0x121516) (andR64R64Effect 0x121516 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x121516 6 2).toInstrSpec (and_r64_r64_effect_step 0x121516 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x121519 [0x48, 0x8B, 0x7C, 0x24, 0x08] (LoadPre 0x121519 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x121519 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121519 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x121519 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x121519 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x12151e [0x48, 0x21, 0xD7] (fun s => s.RIP = 0x12151e) (andR64R64Effect 0x12151e 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x12151e 7 2).toInstrSpec (and_r64_r64_effect_step 0x12151e 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x121521 [0x4C, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x121521 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x121521 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121521 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x121521 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x121521 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x121526 [0x49, 0x21, 0xD0] (fun s => s.RIP = 0x121526) (andR64R64Effect 0x121526 8 2)
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x121526 8 2).toInstrSpec (and_r64_r64_effect_step 0x121526 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x121529 [0x4C, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x121529 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121529 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121529 9 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x121529 9 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x121529 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x12152e [0x49, 0x21, 0xD1] (fun s => s.RIP = 0x12152e) (andR64R64Effect 0x12152e 9 2)
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x12152e 9 2).toInstrSpec (and_r64_r64_effect_step 0x12152e 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x121531 [0x4C, 0x8B, 0x54, 0x24, 0x20] (LoadPre 0x121531 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x121531 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121531 10 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x121531 10 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x121531 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x121536 [0x49, 0x21, 0xD2] (fun s => s.RIP = 0x121536) (andR64R64Effect 0x121536 10 2)
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x121536 10 2).toInstrSpec (and_r64_r64_effect_step 0x121536 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x121539 [0x4C, 0x8B, 0x5C, 0x24, 0x28] (LoadPre 0x121539 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x121539 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121539 11 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x121539 11 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x121539 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x12153e [0x49, 0x21, 0xD3] (fun s => s.RIP = 0x12153e) (andR64R64Effect 0x12153e 11 2)
      [.gpr 11, .gpr 2] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x12153e 11 2).toInstrSpec (and_r64_r64_effect_step 0x12153e 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x121541 [0x4C, 0x8B, 0x74, 0x24, 0x30] (LoadPre 0x121541 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x121541 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121541 14 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x121541 14 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x121541 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x121546 [0x49, 0x21, 0xD6] (fun s => s.RIP = 0x121546) (andR64R64Effect 0x121546 14 2)
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x121546 14 2).toInstrSpec (and_r64_r64_effect_step 0x121546 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x121549 [0x4C, 0x8B, 0x7C, 0x24, 0x38] (LoadPre 0x121549 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x121549 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121549 15 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x121549 15 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x121549 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x12154e [0x49, 0x21, 0xD7] (fun s => s.RIP = 0x12154e) (andR64R64Effect 0x12154e 15 2)
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x12154e 15 2).toInstrSpec (and_r64_r64_effect_step 0x12154e 0x49 0xd7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121507) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12150c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12150f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121512) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 61), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121516) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121519) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 65), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12151e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121521) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (8, 69), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121526) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (8, 71), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121529) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (8, 71), (9, 73), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12152e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (8, 71), (9, 75), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121531) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (8, 71), (9, 75), (10, 77), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121536) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121539) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 81), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12153e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121541) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (13, 13), (14, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121546) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (13, 13), (14, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121549) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (13, 13), (14, 87), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12154e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (6, 63), (7, 67), (8, 71), (9, 75), (10, 79), (11, 83), (13, 13), (14, 87), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121551) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l121502_1 code

theorem block_l121502 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121502 :=
  Rest.liftedBlock (rest_l121502 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121502 x hx)

theorem rest_l121599 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121599 bytes_l121599) (entryMap (live .l121599))
      8 0x121599 bytes_l121599 b_l121599 := by
  have f0 : InstrSpec 0x121599 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x121599) (movR64R64Effect 0x121599 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x121599 0 3).toInstrSpec (mov_r64_r64_effect_step 0x121599 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12159c [0x48, 0x83, 0xC4, 0x60] (fun s => s.RIP = 0x12159c) (addR64Imm8Effect 0x12159c 4 0x60)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12159c 4 0x60).toInstrSpec (add_r64_imm8_effect_step 0x12159c 0x48 0xc4 0x60 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1215a0 [0x5B] (PopPre 0x1215a0) (popR64Effect 0x1215a0 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1215a0 1 3).toInstrSpec (pop_r64_effect_step 0x1215a0 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1215a1 [0x41, 0x5C] (PopPre 0x1215a1) (popR64Effect 0x1215a1 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1215a1 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1215a1 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1215a3 [0x41, 0x5E] (PopPre 0x1215a3) (popR64Effect 0x1215a3 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1215a3 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1215a3 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1215a5 [0x41, 0x5F] (PopPre 0x1215a5) (popR64Effect 0x1215a5 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1215a5 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1215a5 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1215a7 [0x5D] (PopPre 0x1215a7) (popR64Effect 0x1215a7 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1215a7 1 5).toInstrSpec (pop_r64_effect_step 0x1215a7 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1215a8 [0xC3] (RetPre 0x1215a8) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1215a8).toInstrSpec (ret_effect_step 0x1215a8) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12159c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215a0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215a1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215a3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215a5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 63), (15, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215a7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 63), (15, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215a8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 63), (15, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l121599 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121599 :=
  Rest.liftedBlock (rest_l121599 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121599 x hx)

theorem rest_l1215a9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1215a9 bytes_l1215a9) (entryMap (live .l1215a9))
      7 0x1215a9 bytes_l1215a9 b_l1215a9 := by
  have f0 : InstrSpec 0x1215a9 [0xC7, 0x04, 0x24, 0x03, 0x00, 0x00, 0x00] (StorePre 0x1215a9 7 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1215a9 + BitVec.ofNat 64 7)) 4) (movM32Imm32Effect 0x1215a9 7 (.sib 4 none 0 .none) 0x3)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1215a9 7 (.sib 4 none 0 .none) 0x3).toInstrSpec (mov_m32_imm32_effect_step 0x1215a9 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x3) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1215b0 [0x48, 0x89, 0xE2] (fun s => s.RIP = 0x1215b0) (movR64R64Effect 0x1215b0 2 4)
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1215b0 2 4).toInstrSpec (mov_r64_r64_effect_step 0x1215b0 0x48 0xe2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1215b3 [0xBE, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1215b3) (movR32Imm32Effect 0x1215b3 5 6 0xb)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1215b3 5 6 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x1215b3 0xbe (by decide) 0xb) pre_rip
  have f3 : InstrSpec 0x1215b8 [0x48, 0xC7, 0xC7, 0x30, 0x2E, 0x20, 0x00] (fun s => s.RIP = 0x1215b8) (movR64Imm32Effect 0x1215b8 7 0x202e30)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x1215b8 7 0x202e30).toInstrSpec (mov_r64_imm32_effect_step 0x1215b8 0x48 0xc7 (by decide) (by decide) (by decide) 0x202e30) pre_rip
  have f4 : InstrSpec 0x1215bf [0x48, 0xC7, 0xC1, 0x10, 0x2E, 0x20, 0x00] (fun s => s.RIP = 0x1215bf) (movR64Imm32Effect 0x1215bf 1 0x202e10)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x1215bf 1 0x202e10).toInstrSpec (mov_r64_imm32_effect_step 0x1215bf 0x48 0xc1 (by decide) (by decide) (by decide) 0x202e10) pre_rip
  have f5 : InstrSpec 0x1215c6 [0x49, 0xC7, 0xC0, 0x40, 0x2E, 0x20, 0x00] (fun s => s.RIP = 0x1215c6) (movR64Imm32Effect 0x1215c6 8 0x202e40)
      [] [] [.reg 8, .rip] :=
    (movR64Imm32Effect_footprint 0x1215c6 8 0x202e40).toInstrSpec (mov_r64_imm32_effect_step 0x1215c6 0x49 0xc0 (by decide) (by decide) (by decide) 0x202e40) pre_rip
  have f6 : InstrSpec 0x1215cd [0xE8, 0xCE, 0x7F, 0x00, 0x00] (PushPre 0x1215cd 5) (callEffect (fun _ => 0x1295a0) 0x1215d2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1215cd 0x1295a0 0x1215d2).toInstrSpec (call_rel32_effect_step 0x1215cd 0x7fce (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x1215b0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 54), (4, 4), (5, 5)]) (p' := 0x1215b3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56)]) (p' := 0x1215b8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x1215bf) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x1215c6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x1215cd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 60), (2, 54), (4, 64), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x1295a0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l1215a9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1215a9 :=
  Rest.liftedBlock (rest_l1215a9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1215a9 x hx)

theorem rest_l1215d2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1215d2 bytes_l1215d2) (entryMap (live .l1215d2))
      2 0x1215d2 bytes_l1215d2 b_l1215d2 := by
  have f0 : InstrSpec 0x1215d2 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1215d2) (fun _ => nopEffect 0x1215d2 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1215d2 10).toInstrSpec (nop_m_effect_step 0x1215d2 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1215dc [0x0F, 0x1F, 0x40, 0x00] (fun s => s.RIP = 0x1215dc) (fun _ => nopEffect 0x1215dc 4)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1215dc 4).toInstrSpec (nop_m_effect_step 0x1215dc [] (by decide) (by decide) (.base 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215dc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215e0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1215d2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1215d2 :=
  Rest.liftedBlock (rest_l1215d2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1215d2 x hx)

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

theorem_by block_l121480_eval :
    program.runBlock (dialect code) ⟨.l121480, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1214a0_eval :
    program.runBlock (dialect code) ⟨.l1214a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1214ae_eval :
    program.runBlock (dialect code) ⟨.l1214ae, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1214b5_eval :
    program.runBlock (dialect code) ⟨.l1214b5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1214b9_eval :
    program.runBlock (dialect code) ⟨.l1214b9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1214bb_eval :
    program.runBlock (dialect code) ⟨.l1214bb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1214c0_eval :
    program.runBlock (dialect code) ⟨.l1214c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1214ce_eval :
    program.runBlock (dialect code) ⟨.l1214ce, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1214d0_eval :
    program.runBlock (dialect code) ⟨.l1214d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1214d8_eval :
    program.runBlock (dialect code) ⟨.l1214d8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1214f3_eval :
    program.runBlock (dialect code) ⟨.l1214f3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121502_eval :
    program.runBlock (dialect code) ⟨.l121502, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121599_eval :
    program.runBlock (dialect code) ⟨.l121599, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1215a9_eval :
    program.runBlock (dialect code) ⟨.l1215a9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1215d2_eval :
    program.runBlock (dialect code) ⟨.l1215d2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
