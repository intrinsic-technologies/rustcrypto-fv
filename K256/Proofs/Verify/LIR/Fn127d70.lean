import K256.Proofs.Verify.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

theorem rest_l127d70 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127d70 bytes_l127d70) (entryMap (live .l127d70))
      13 0x127d70 bytes_l127d70 b_l127d70 := by
  have f0 : InstrSpec 0x127d70 [0x55] (PushPre 0x127d70 1) (pushR64Effect 0x127d70 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x127d70 1 5).toInstrSpec (push_r64_effect_step 0x127d70 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x127d71 [0x41, 0x57] (PushPre 0x127d71 2) (pushR64Effect 0x127d71 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x127d71 2 15).toInstrSpec (push_r64_rex_effect_step 0x127d71 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x127d73 [0x41, 0x56] (PushPre 0x127d73 2) (pushR64Effect 0x127d73 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x127d73 2 14).toInstrSpec (push_r64_rex_effect_step 0x127d73 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x127d75 [0x41, 0x55] (PushPre 0x127d75 2) (pushR64Effect 0x127d75 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x127d75 2 13).toInstrSpec (push_r64_rex_effect_step 0x127d75 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x127d77 [0x41, 0x54] (PushPre 0x127d77 2) (pushR64Effect 0x127d77 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x127d77 2 12).toInstrSpec (push_r64_rex_effect_step 0x127d77 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x127d79 [0x53] (PushPre 0x127d79 1) (pushR64Effect 0x127d79 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x127d79 1 3).toInstrSpec (push_r64_effect_step 0x127d79 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x127d7a [0x48, 0x83, 0xEC, 0x18] (fun s => s.RIP = 0x127d7a) (subR64Imm8Effect 0x127d7a 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x127d7a 4 0x18).toInstrSpec (sub_r64_imm8_effect_step 0x127d7a 0x48 0xec 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x127d7e [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x127d7e) (movR64R64Effect 0x127d7e 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x127d7e 14 2).toInstrSpec (mov_r64_r64_effect_step 0x127d7e 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x127d81 [0x89, 0xCA] (fun s => s.RIP = 0x127d81) (movR32R32Effect 0x127d81 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x127d81 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x127d81 0xca (by decide)) pre_rip
  have f9 : InstrSpec 0x127d83 [0xC1, 0xE2, 0x06] (fun s => s.RIP = 0x127d83) (shlR32Effect 0x127d83 3 2 6)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x127d83 3 2 6).toInstrSpec (shl_r32_imm8_effect_step 0x127d83 0xe2 0x6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x127d86 [0xB0, 0x03] (fun s => s.RIP = 0x127d86) (movR8Imm8Effect 0x127d86 2 0 0x3)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x127d86 2 0 0x3).toInstrSpec (mov_r8_imm8_effect_step 0x127d86 0xb0 (by decide) 0x3) pre_rip
  have f11 : InstrSpec 0x127d88 [0x44, 0x39, 0xC2] (fun s => s.RIP = 0x127d88) (cmpR32R32Effect 0x127d88 3 2 8)
      [.gpr 2, .gpr 8] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x127d88 3 2 8).toInstrSpec (cmp_r32_r32_rex_effect_step 0x127d88 0x44 0xc2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d71) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d73) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d75) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d77) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d79) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d7a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d7e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d81) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 69), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d83) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 71), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d86) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 1), (2, 71), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d88) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 73), (1, 1), (2, 71), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (16, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d8b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 77) (jcc_rel32_effect_step 0x127d8b 2 0xe5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127d70 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127d70 :=
  Rest.liftedBlock (rest_l127d70 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127d70 x hx)

theorem rest_l127d91 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127d91 bytes_l127d91) (entryMap (live .l127d91))
      13 0x127d91 bytes_l127d91 b_l127d91 := by
  have f0 : InstrSpec 0x127d91 [0x44, 0x89, 0xC3] (fun s => s.RIP = 0x127d91) (movR32R32Effect 0x127d91 3 3 8)
      [.gpr 8] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x127d91 3 3 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x127d91 0x44 0xc3 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127d94 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x127d94 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x127d94 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127d94 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x127d94 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x127d94 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127d99 [0x44, 0x89, 0xC0] (fun s => s.RIP = 0x127d99) (movR32R32Effect 0x127d99 3 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x127d99 3 0 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x127d99 0x44 0xc0 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127d9c [0xC1, 0xE8, 0x03] (fun s => s.RIP = 0x127d9c) (shrR32Effect 0x127d9c 3 0 3)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x127d9c 3 0 3).toInstrSpec (shr_r32_imm8_effect_step 0x127d9c 0xe8 0x3 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127d9f [0x45, 0x89, 0xC5] (fun s => s.RIP = 0x127d9f) (movR32R32Effect 0x127d9f 3 13 8)
      [.gpr 8] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x127d9f 3 13 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x127d9f 0x45 0xc5 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x127da2 [0x41, 0x83, 0xE5, 0x07] (fun s => s.RIP = 0x127da2) (andR32Imm8Effect 0x127da2 4 13 0x7)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x127da2 4 13 0x7).toInstrSpec (and_r32_imm8_rex_effect_step 0x127da2 0x41 0xe5 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x127da6 [0x41, 0x83, 0xC5, 0x07] (fun s => s.RIP = 0x127da6) (addR32Imm8Effect 0x127da6 4 13 0x7)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (addR32Imm8Effect_footprint 0x127da6 4 13 0x7).toInstrSpec (add_r32_imm8_rex_effect_step 0x127da6 0x41 0xc5 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x127daa [0x41, 0xC1, 0xED, 0x03] (fun s => s.RIP = 0x127daa) (shrR32Effect 0x127daa 4 13 3)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR32Effect_footprint 0x127daa 4 13 3).toInstrSpec (shr_r32_imm8_rex_effect_step 0x127daa 0x41 0xed 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x127dae [0x41, 0x01, 0xC5] (fun s => s.RIP = 0x127dae) (addR32R32Effect 0x127dae 3 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (addR32R32Effect_footprint 0x127dae 3 13 0).toInstrSpec (add_r32_r32_rex_effect_step 0x127dae 0x41 0xc5 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x127db1 [0x4C, 0x39, 0xEE] (fun s => s.RIP = 0x127db1) (cmpR64R64Effect 0x127db1 6 13)
      [.gpr 6, .gpr 13] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x127db1 6 13).toInstrSpec (cmp_r64_r64_effect_step 0x127db1 0x4c 0xee (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x127db4 [0x4C, 0x0F, 0x42, 0xEE] (fun s => s.RIP = 0x127db4) (atFlags (condHolds 2) (cmovR64R64Effect 0x127db4 4 13 6))
      [.gpr 13, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 13, .rip] :=
    (cmovR64R64Effect_footprint 0x127db4 4 13 6 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x127db4 2 0x4c (by decide) 0xee (by decide) c)) pre_rip
  have f11 : InstrSpec 0x127db8 [0x4D, 0x85, 0xED] (fun s => s.RIP = 0x127db8) (testR64R64Effect 0x127db8 13 13)
      [.gpr 13, .gpr 13] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x127db8 13 13).toInstrSpec (test_r64_r64_effect_step 0x127db8 0x4d 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d94) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d99) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d9c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d9f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 60), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127da2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 62), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127da6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 64), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127daa) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 66), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127dae) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 68), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127db1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 68), (14, 14), (15, 15), (16, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127db4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 72), (14, 14), (15, 15), (16, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127db8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 72), (14, 14), (15, 15), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127dbb) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 76) (jcc_rel32_effect_step 0x127dbb 4 0x8f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127d91 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127d91 :=
  Rest.liftedBlock (rest_l127d91 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127d91 x hx)

theorem rest_l127dc1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127dc1 bytes_l127dc1) (entryMap (live .l127dc1))
      7 0x127dc1 bytes_l127dc1 b_l127dc1 := by
  have f0 : InstrSpec 0x127dc1 [0x49, 0x8D, 0x6D, 0x07] (fun s => s.RIP = 0x127dc1) (leaR64Effect 0x127dc1 5 (.base 13 (.d8 0x7)))
      [.gpr 13] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x127dc1 5 (.base 13 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x127dc1 0x49 (by decide) 5 (.base 13 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127dc5 [0x48, 0xC1, 0xED, 0x03] (fun s => s.RIP = 0x127dc5) (shrR64Effect 0x127dc5 4 5 3)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR64Effect_footprint 0x127dc5 4 5 3).toInstrSpec (shr_r64_imm8_effect_step 0x127dc5 0x48 0xed 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127dc9 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x127dc9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x127dc9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127dc9 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x127dc9 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x127dc9 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x127dce [0x48, 0x39, 0xE8] (fun s => s.RIP = 0x127dce) (cmpR64R64Effect 0x127dce 0 5)
      [.gpr 0, .gpr 5] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x127dce 0 5).toInstrSpec (cmp_r64_r64_effect_step 0x127dce 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127dd1 [0x48, 0x0F, 0x42, 0xE8] (fun s => s.RIP = 0x127dd1) (atFlags (condHolds 2) (cmovR64R64Effect 0x127dd1 4 5 0))
      [.gpr 5, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .rip] :=
    (cmovR64R64Effect_footprint 0x127dd1 4 5 0 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x127dd1 2 0x48 (by decide) 0xe8 (by decide) c)) pre_rip
  have f5 : InstrSpec 0x127dd5 [0x48, 0x85, 0xED] (fun s => s.RIP = 0x127dd5) (testR64R64Effect 0x127dd5 5 5)
      [.gpr 5, .gpr 5] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x127dd5 5 5).toInstrSpec (test_r64_r64_effect_step 0x127dd5 0x48 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127dc5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127dc9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127dce) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127dd1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127dd5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127dd8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 65) (jcc_rel8_effect_step 0x127dd8 4 0x76) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127dc1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127dc1 :=
  Rest.liftedBlock (rest_l127dc1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127dc1 x hx)

theorem rest_l127dda [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127dda bytes_l127dda) (entryMap (live .l127dda))
      5 0x127dda bytes_l127dda b_l127dda := by
  have f0 : InstrSpec 0x127dda [0x49, 0x89, 0xFC] (fun s => s.RIP = 0x127dda) (movR64R64Effect 0x127dda 12 7)
      [.gpr 7] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x127dda 12 7).toInstrSpec (mov_r64_r64_effect_step 0x127dda 0x49 0xfc (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127ddd [0x49, 0x01, 0xF4] (fun s => s.RIP = 0x127ddd) (addR64R64Effect 0x127ddd 12 6)
      [.gpr 12, .gpr 6] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x127ddd 12 6).toInstrSpec (add_r64_r64_effect_step 0x127ddd 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127de0 [0x48, 0xC1, 0xE5, 0x03] (fun s => s.RIP = 0x127de0) (shlR64Effect 0x127de0 4 5 3)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shlR64Effect_footprint 0x127de0 4 5 3).toInstrSpec (shl_r64_imm8_effect_step 0x127de0 0x48 0xe5 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127de4 [0x45, 0x31, 0xFF] (fun s => s.RIP = 0x127de4) (xorR32R32Effect 0x127de4 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127de4 3 15 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x127de4 0x45 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127ddd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127de0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127de4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127de7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 61) (jmp_rel8_effect_step 0x127de7 0x45 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l127dda [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127dda :=
  Rest.liftedBlock (rest_l127dda code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127dda x hx)

theorem rest_l127df0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127df0 bytes_l127df0) (entryMap (live .l127df0))
      9 0x127df0 bytes_l127df0 b_l127df0 := by
  have f0 : InstrSpec 0x127df0 [0x4C, 0x89, 0xE9] (fun s => s.RIP = 0x127df0) (movR64R64Effect 0x127df0 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x127df0 1 13).toInstrSpec (mov_r64_r64_effect_step 0x127df0 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127df3 [0x48, 0x29, 0xC1] (fun s => s.RIP = 0x127df3) (subR64R64Effect 0x127df3 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x127df3 1 0).toInstrSpec (sub_r64_r64_effect_step 0x127df3 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127df6 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x127df6) (movR64R64Effect 0x127df6 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x127df6 2 13).toInstrSpec (mov_r64_r64_effect_step 0x127df6 0x4c 0xea (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127df9 [0x48, 0x29, 0xCA] (fun s => s.RIP = 0x127df9) (subR64R64Effect 0x127df9 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x127df9 2 1).toInstrSpec (sub_r64_r64_effect_step 0x127df9 0x48 0xca (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127dfc [0x4C, 0x01, 0xE6] (fun s => s.RIP = 0x127dfc) (addR64R64Effect 0x127dfc 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x127dfc 6 12).toInstrSpec (add_r64_r64_effect_step 0x127dfc 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x127dff [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x127dff) (leaR64Effect 0x127dff 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x127dff 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x127dff 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x127e04 [0x48, 0x29, 0xD7] (fun s => s.RIP = 0x127e04) (subR64R64Effect 0x127e04 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (subR64R64Effect_footprint 0x127e04 7 2).toInstrSpec (sub_r64_r64_effect_step 0x127e04 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x127e07 [0x48, 0x83, 0xC7, 0x08] (fun s => s.RIP = 0x127e07) (addR64Imm8Effect 0x127e07 7 0x8)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x127e07 7 0x8).toInstrSpec (add_r64_imm8_effect_step 0x127e07 0x48 0xc7 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x127e0b [0xFF, 0x15, 0xBF, 0xBF, 0x0D, 0x00] (GoesTo (CallMemPre 0x127e0b (.rip 0xdbfbf)) (callEffect (callMemPtr 0x127e0b (.rip 0xdbfbf)) (0x127e0b + BitVec.ofNat 64 (callMemLen (.rip 0xdbfbf)))) 0x12a820) (callEffect (callMemPtr 0x127e0b (.rip 0xdbfbf)) (0x127e0b + BitVec.ofNat 64 (callMemLen (.rip 0xdbfbf))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x127e0b (.rip 0xdbfbf)).toInstrSpec (call_m64_effect_step 0x127e0b (.rip 0xdbfbf) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127df3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127df6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127df9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127dfc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127dff) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e04) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e07) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 67), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e0b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 69), (5, 5), (6, 61), (7, 67), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l127df0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127df0 :=
  Rest.liftedBlock (rest_l127df0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127df0 x hx)

theorem rest_l127e11 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127e11 bytes_l127e11) (entryMap (live .l127e11))
      2 0x127e11 bytes_l127e11 b_l127e11 := by
  have f0 : InstrSpec 0x127e11 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x127e11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x127e11 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127e11 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x127e11 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x127e11 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127e16 [0x48, 0x0F, 0xC8] (fun s => s.RIP = 0x127e16) (bswapR64Effect 0x127e16 3 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR64Effect_footprint 0x127e16 3 0).toInstrSpec (bswap_r64_effect_step 0x127e16 0x48 (by decide) 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e16) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e19) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l127e11 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127e11 :=
  Rest.liftedBlock (rest_l127e11 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127e11 x hx)

theorem rest_l127e19 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127e19 bytes_l127e19) (entryMap (live .l127e19))
      6 0x127e19 bytes_l127e19 b_l127e19 := by
  have f0 : InstrSpec 0x127e19 [0x4B, 0x89, 0x04, 0x3E] (StorePre 0x127e19 4 (fun s => AddrMode.addr (.sib 14 (some 15) 0 .none) s (0x127e19 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127e19 0 (.sib 14 (some 15) 0 .none))
      [.gpr 0, .gpr 14, .gpr 15] [] [.rip] :=
    (movM64R64Effect_footprint 0x127e19 0 (.sib 14 (some 15) 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x127e19 0x4b (by decide) 0 (.sib 14 (some 15) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127e1d [0x49, 0x83, 0xC7, 0x08] (fun s => s.RIP = 0x127e1d) (addR64Imm8Effect 0x127e1d 15 0x8)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x127e1d 15 0x8).toInstrSpec (add_r64_imm8_effect_step 0x127e1d 0x49 0xc7 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127e21 [0x49, 0x83, 0xC5, 0xF8] (fun s => s.RIP = 0x127e21) (addR64Imm8Effect 0x127e21 13 0xf8)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x127e21 13 0xf8).toInstrSpec (add_r64_imm8_effect_step 0x127e21 0x49 0xc5 0xf8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127e25 [0x49, 0x83, 0xC4, 0xF8] (fun s => s.RIP = 0x127e25) (addR64Imm8Effect 0x127e25 12 0xf8)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x127e25 12 0xf8).toInstrSpec (add_r64_imm8_effect_step 0x127e25 0x49 0xc4 0xf8 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127e29 [0x4C, 0x39, 0xFD] (fun s => s.RIP = 0x127e29) (cmpR64R64Effect 0x127e29 5 15)
      [.gpr 5, .gpr 15] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x127e29 5 15).toInstrSpec (cmp_r64_r64_effect_step 0x127e29 0x4c 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e1d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e21) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 56), (14, 14), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e25) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 56), (14, 14), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e29) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 56), (14, 14), (15, 54), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e2c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel8_effect_step 0x127e2c 4 0x22) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127e19 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127e19 :=
  Rest.liftedBlock (rest_l127e19 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127e19 x hx)

theorem rest_l127e2e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127e2e bytes_l127e2e) (entryMap (live .l127e2e))
      7 0x127e2e bytes_l127e2e b_l127e2e := by
  have f0 : InstrSpec 0x127e2e [0x49, 0x83, 0xFD, 0x08] (fun s => s.RIP = 0x127e2e) (cmpR64Imm8Effect 0x127e2e 13 0x8)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x127e2e 13 0x8).toInstrSpec (cmp_r64_imm8_effect_step 0x127e2e 0x49 0xfd 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127e32 [0xB8, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127e32) (movR32Imm32Effect 0x127e32 5 0 0x8)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x127e32 5 0 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x127e32 0xb8 (by decide) 0x8) pre_rip
  have f2 : InstrSpec 0x127e37 [0x49, 0x0F, 0x42, 0xC5] (fun s => s.RIP = 0x127e37) (atFlags (condHolds 2) (cmovR64R64Effect 0x127e37 4 0 13))
      [.gpr 0, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (cmovR64R64Effect_footprint 0x127e37 4 0 13 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x127e37 2 0x49 (by decide) 0xc5 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x127e3b [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x127e3b) (movR64R64Effect 0x127e3b 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x127e3b 6 0).toInstrSpec (mov_r64_r64_effect_step 0x127e3b 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127e3e [0x48, 0xF7, 0xDE] (fun s => s.RIP = 0x127e3e) (negR64Effect 0x127e3e 6)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (negR64Effect_footprint 0x127e3e 6).toInstrSpec (neg_r64_effect_step 0x127e3e 0x48 0xde (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x127e41 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x127e41 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x127e41 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x127e41 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x127e41 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x127e41 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e32) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e37) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e3b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e3e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 61), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e41) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 61), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e4a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 65) (jcc_rel8_effect_step 0x127e4a 5 0xa4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127e2e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127e2e :=
  Rest.liftedBlock (rest_l127e2e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127e2e x hx)

theorem rest_l127e4c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127e4c bytes_l127e4c) (entryMap (live .l127e4c))
      2 0x127e4c bytes_l127e4c b_l127e4c := by
  have f0 : InstrSpec 0x127e4c [0x31, 0xC0] (fun s => s.RIP = 0x127e4c) (xorR32R32Effect 0x127e4c 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127e4c 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x127e4c 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e4e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x127e4e 0xc9 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l127e4c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127e4c :=
  Rest.liftedBlock (rest_l127e4c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127e4c x hx)

theorem rest_l127e50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127e50 bytes_l127e50) (entryMap (live .l127e50))
      4 0x127e50 bytes_l127e50 b_l127e50 := by
  have f0 : InstrSpec 0x127e50 [0x89, 0xD9] (fun s => s.RIP = 0x127e50) (movR32R32Effect 0x127e50 2 1 3)
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x127e50 2 1 3).toInstrSpec (mov_r32_r32_effect_step 0x127e50 0xd9 (by decide)) pre_rip
  have f1 : InstrSpec 0x127e52 [0xB0, 0xFF] (fun s => s.RIP = 0x127e52) (movR8Imm8Effect 0x127e52 2 0 0xff)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x127e52 2 0 0xff).toInstrSpec (mov_r8_imm8_effect_step 0x127e52 0xb0 (by decide) 0xff) pre_rip
  have f2 : InstrSpec 0x127e54 [0x83, 0xE1, 0x3F] (fun s => s.RIP = 0x127e54) (andR32Imm8Effect 0x127e54 3 1 0x3f)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x127e54 3 1 0x3f).toInstrSpec (and_r32_imm8_effect_step 0x127e54 0xe1 0x3f (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e52) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e54) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e57) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x127e57 4 0x1d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127e50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127e50 :=
  Rest.liftedBlock (rest_l127e50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127e50 x hx)

theorem rest_l127e59 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127e59 bytes_l127e59) (entryMap (live .l127e59))
      4 0x127e59 bytes_l127e59 b_l127e59 := by
  have f0 : InstrSpec 0x127e59 [0xC1, 0xEB, 0x06] (fun s => s.RIP = 0x127e59) (shrR32Effect 0x127e59 3 3 6)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR32Effect_footprint 0x127e59 3 3 6).toInstrSpec (shr_r32_imm8_effect_step 0x127e59 0xeb 0x6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127e5c [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x127e5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x127e5c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127e5c 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x127e5c 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x127e5c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x127e61 [0x48, 0x39, 0xDE] (fun s => s.RIP = 0x127e61) (cmpR64R64Effect 0x127e61 6 3)
      [.gpr 6, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x127e61 6 3).toInstrSpec (cmp_r64_r64_effect_step 0x127e61 0x48 0xde (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e5c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e61) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e64) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x127e64 6 0x1f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127e59 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127e59 :=
  Rest.liftedBlock (rest_l127e59 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127e59 x hx)

theorem rest_l127e66 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127e66 bytes_l127e66) (entryMap (live .l127e66))
      5 0x127e66 bytes_l127e66 b_l127e66 := by
  have f0 : InstrSpec 0x127e66 [0x49, 0x8B, 0x14, 0xDE] (LoadPre 0x127e66 (fun s => AddrMode.addr (.sib 14 (some 3) 3 .none) s (0x127e66 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127e66 2 (.sib 14 (some 3) 3 .none))
      [.gpr 14, .gpr 3] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x127e66 2 (.sib 14 (some 3) 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x127e66 0x49 (by decide) 2 (.sib 14 (some 3) 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127e6a [0xF6, 0xD9] (fun s => s.RIP = 0x127e6a) (negR8Effect 0x127e6a 2 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR8Effect_footprint 0x127e6a 2 1).toInstrSpec (neg_r8_effect_step 0x127e6a 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127e6c [0x48, 0xD3, 0xE2] (fun s => s.RIP = 0x127e6c) (shlR64ClEffect 0x127e6c 3 2)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x127e6c 3 2).toInstrSpec (shl_r64_cl_effect_step 0x127e6c 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127e6f [0x48, 0xD3, 0xEA] (fun s => s.RIP = 0x127e6f) (shrR64ClEffect 0x127e6f 3 2)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x127e6f 3 2).toInstrSpec (shr_r64_cl_effect_step 0x127e6f 0x48 0xea (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127e72 [0x49, 0x89, 0x14, 0xDE] (StorePre 0x127e72 4 (fun s => AddrMode.addr (.sib 14 (some 3) 3 .none) s (0x127e72 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127e72 2 (.sib 14 (some 3) 3 .none))
      [.gpr 2, .gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x127e72 2 (.sib 14 (some 3) 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x127e72 0x49 (by decide) 2 (.sib 14 (some 3) 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e6a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e6c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e6f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e72) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e76) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l127e66 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127e66 :=
  Rest.liftedBlock (rest_l127e66 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127e66 x hx)

theorem rest_l127e76 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127e76 bytes_l127e76) (entryMap (live .l127e76))
      8 0x127e76 bytes_l127e76 b_l127e76 := by
  have f0 : InstrSpec 0x127e76 [0x48, 0x83, 0xC4, 0x18] (fun s => s.RIP = 0x127e76) (addR64Imm8Effect 0x127e76 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x127e76 4 0x18).toInstrSpec (add_r64_imm8_effect_step 0x127e76 0x48 0xc4 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127e7a [0x5B] (PopPre 0x127e7a) (popR64Effect 0x127e7a 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x127e7a 1 3).toInstrSpec (pop_r64_effect_step 0x127e7a 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x127e7b [0x41, 0x5C] (PopPre 0x127e7b) (popR64Effect 0x127e7b 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x127e7b 2 12).toInstrSpec (pop_r64_rex_effect_step 0x127e7b 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x127e7d [0x41, 0x5D] (PopPre 0x127e7d) (popR64Effect 0x127e7d 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x127e7d 2 13).toInstrSpec (pop_r64_rex_effect_step 0x127e7d 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x127e7f [0x41, 0x5E] (PopPre 0x127e7f) (popR64Effect 0x127e7f 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x127e7f 2 14).toInstrSpec (pop_r64_rex_effect_step 0x127e7f 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x127e81 [0x41, 0x5F] (PopPre 0x127e81) (popR64Effect 0x127e81 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x127e81 2 15).toInstrSpec (pop_r64_rex_effect_step 0x127e81 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x127e83 [0x5D] (PopPre 0x127e83) (popR64Effect 0x127e83 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x127e83 1 5).toInstrSpec (pop_r64_effect_step 0x127e83 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x127e84 [0xC3] (RetPre 0x127e84) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127e84).toInstrSpec (ret_effect_step 0x127e84) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e7a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e7b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e7d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e7f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e81) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e83) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e84) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l127e76 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127e76 :=
  Rest.liftedBlock (rest_l127e76 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127e76 x hx)

theorem rest_l127e85 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127e85 bytes_l127e85) (entryMap (live .l127e85))
      3 0x127e85 bytes_l127e85 b_l127e85 := by
  have f0 : InstrSpec 0x127e85 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x127e85) (movR64R64Effect 0x127e85 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x127e85 7 3).toInstrSpec (mov_r64_r64_effect_step 0x127e85 0x48 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127e88 [0x48, 0xC7, 0xC2, 0xD0, 0x39, 0x20, 0x00] (fun s => s.RIP = 0x127e88) (movR64Imm32Effect 0x127e88 2 0x2039d0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x127e88 2 0x2039d0).toInstrSpec (mov_r64_imm32_effect_step 0x127e88 0x48 0xc2 (by decide) (by decide) (by decide) 0x2039d0) pre_rip
  have f2 : InstrSpec 0x127e8f [0xE8, 0x5E, 0x17, 0x00, 0x00] (PushPre 0x127e8f 5) (callEffect (fun _ => 0x1295f2) 0x127e94)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x127e8f 0x1295f2 0x127e94).toInstrSpec (call_rel32_effect_step 0x127e8f 0x175e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x127e88) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x127e8f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 57), (5, 5), (6, 6), (7, 53)]) (p' := 0x1295f2) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l127e85 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127e85 :=
  Rest.liftedBlock (rest_l127e85 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127e85 x hx)

theorem rest_l127e94 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127e94 bytes_l127e94) (entryMap (live .l127e94))
      2 0x127e94 bytes_l127e94 b_l127e94 := by
  have f0 : InstrSpec 0x127e94 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127e94) (fun _ => nopEffect 0x127e94 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x127e94 10).toInstrSpec (nop_m_effect_step 0x127e94 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127e9e [0x66, 0x90] (fun s => s.RIP = 0x127e9e) (fun _ => nopEffect 0x127e9e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x127e9e 2).toInstrSpec (nop_66_effect_step 0x127e9e) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127e9e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127ea0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l127e94 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127e94 :=
  Rest.liftedBlock (rest_l127e94 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127e94 x hx)

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

theorem_by block_l127d70_eval :
    program.runBlock (dialect code) ⟨.l127d70, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127d91_eval :
    program.runBlock (dialect code) ⟨.l127d91, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127dc1_eval :
    program.runBlock (dialect code) ⟨.l127dc1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127dda_eval :
    program.runBlock (dialect code) ⟨.l127dda, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127df0_eval :
    program.runBlock (dialect code) ⟨.l127df0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127e11_eval :
    program.runBlock (dialect code) ⟨.l127e11, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127e19_eval :
    program.runBlock (dialect code) ⟨.l127e19, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127e2e_eval :
    program.runBlock (dialect code) ⟨.l127e2e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127e4c_eval :
    program.runBlock (dialect code) ⟨.l127e4c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127e50_eval :
    program.runBlock (dialect code) ⟨.l127e50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127e59_eval :
    program.runBlock (dialect code) ⟨.l127e59, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127e66_eval :
    program.runBlock (dialect code) ⟨.l127e66, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127e76_eval :
    program.runBlock (dialect code) ⟨.l127e76, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127e85_eval :
    program.runBlock (dialect code) ⟨.l127e85, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127e94_eval :
    program.runBlock (dialect code) ⟨.l127e94, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
