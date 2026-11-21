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

theorem rest_l1107b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1107b0 bytes_l1107b0) (entryMap (live .l1107b0))
      19 0x1107b0 bytes_l1107b0 b_l1107b0 := by
  have f0 : InstrSpec 0x1107b0 [0x55] (PushPre 0x1107b0 1) (pushR64Effect 0x1107b0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1107b0 1 5).toInstrSpec (push_r64_effect_step 0x1107b0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1107b1 [0x41, 0x57] (PushPre 0x1107b1 2) (pushR64Effect 0x1107b1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1107b1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1107b1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1107b3 [0x41, 0x56] (PushPre 0x1107b3 2) (pushR64Effect 0x1107b3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1107b3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1107b3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1107b5 [0x41, 0x55] (PushPre 0x1107b5 2) (pushR64Effect 0x1107b5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1107b5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1107b5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1107b7 [0x41, 0x54] (PushPre 0x1107b7 2) (pushR64Effect 0x1107b7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1107b7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1107b7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1107b9 [0x53] (PushPre 0x1107b9 1) (pushR64Effect 0x1107b9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1107b9 1 3).toInstrSpec (push_r64_effect_step 0x1107b9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1107ba [0x48, 0x83, 0xEC, 0x58] (fun s => s.RIP = 0x1107ba) (subR64Imm8Effect 0x1107ba 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1107ba 4 0x58).toInstrSpec (sub_r64_imm8_effect_step 0x1107ba 0x48 0xec 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1107be [0x4D, 0x89, 0xCC] (fun s => s.RIP = 0x1107be) (movR64R64Effect 0x1107be 12 9)
      [.gpr 9] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1107be 12 9).toInstrSpec (mov_r64_r64_effect_step 0x1107be 0x4d 0xcc (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1107c1 [0x4D, 0x89, 0xC5] (fun s => s.RIP = 0x1107c1) (movR64R64Effect 0x1107c1 13 8)
      [.gpr 8] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1107c1 13 8).toInstrSpec (mov_r64_r64_effect_step 0x1107c1 0x4d 0xc5 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1107c4 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x1107c4) (movR64R64Effect 0x1107c4 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1107c4 0 1).toInstrSpec (mov_r64_r64_effect_step 0x1107c4 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1107c7 [0x49, 0x89, 0xF7] (fun s => s.RIP = 0x1107c7) (movR64R64Effect 0x1107c7 15 6)
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1107c7 15 6).toInstrSpec (mov_r64_r64_effect_step 0x1107c7 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1107ca [0x48, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x1107ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1107ca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1107ca 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1107ca 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1107ca 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1107cf [0xBB, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1107cf) (movR32Imm32Effect 0x1107cf 5 3 0x1)
      [] [] [.reg 3, .rip] :=
    (movR32Imm32Effect_footprint 0x1107cf 5 3 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1107cf 0xbb (by decide) 0x1) pre_rip
  have f13 : InstrSpec 0x1107d4 [0x44, 0x89, 0xE1] (fun s => s.RIP = 0x1107d4) (movR32R32Effect 0x1107d4 3 1 12)
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1107d4 3 1 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x1107d4 0x44 0xe1 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1107d7 [0x48, 0xD3, 0xE3] (fun s => s.RIP = 0x1107d7) (shlR64ClEffect 0x1107d7 3 3)
      [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x1107d7 3 3).toInstrSpec (shl_r64_cl_effect_step 0x1107d7 0x48 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1107da [0x48, 0x8D, 0x7C, 0x24, 0x30] (fun s => s.RIP = 0x1107da) (leaR64Effect 0x1107da 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1107da 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x1107da 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1107df [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x1107df) (movR64R64Effect 0x1107df 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1107df 6 2).toInstrSpec (mov_r64_r64_effect_step 0x1107df 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1107e2 [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x1107e2) (movR64R64Effect 0x1107e2 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1107e2 2 0).toInstrSpec (mov_r64_r64_effect_step 0x1107e2 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1107e5 [0xE8, 0xF6, 0x39, 0x01, 0x00] (PushPre 0x1107e5 5) (callEffect (fun _ => 0x1241e0) 0x1107ea)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1107e5 0x1241e0 0x1107ea).toInstrSpec (call_rel32_effect_step 0x1107e5 0x139f6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107b1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107b3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107b5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107b7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107b9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107ba) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107be) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107c1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (13, 69), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107c4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (13, 69), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107c7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (13, 69), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107ca) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (13, 69), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107cf) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 76), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (13, 69), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107d4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 71), (1, 78), (2, 2), (3, 76), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (13, 69), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107d7) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 71), (1, 78), (2, 2), (3, 80), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (13, 69), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107da) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 71), (1, 78), (2, 2), (3, 80), (4, 65), (5, 5), (6, 6), (7, 82), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (13, 69), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107df) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 71), (1, 78), (2, 2), (3, 80), (4, 65), (5, 5), (6, 84), (7, 82), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (13, 69), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107e2) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 71), (1, 78), (2, 86), (3, 80), (4, 65), (5, 5), (6, 84), (7, 82), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (13, 69), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107e5) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 71), (1, 78), (2, 86), (3, 80), (4, 88), (5, 5), (6, 84), (7, 82), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (13, 69), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1241e0) f18 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 90) (by decide) (by decide) rfl rfl

theorem block_l1107b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1107b0 :=
  Rest.liftedBlock (rest_l1107b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1107b0 x hx)

theorem rest_l1107ea [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1107ea bytes_l1107ea) (entryMap (live .l1107ea))
      4 0x1107ea bytes_l1107ea b_l1107ea := by
  have f0 : InstrSpec 0x1107ea [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x1107ea) (xorR32R32Effect 0x1107ea 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1107ea 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x1107ea 0x45 0xf6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1107ed [0x4C, 0x89, 0x6C, 0x24, 0x18] (StorePre 0x1107ed 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1107ed + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1107ed 13 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1107ed 13 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1107ed 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1107f2 [0x4D, 0x85, 0xED] (fun s => s.RIP = 0x1107f2) (testR64R64Effect 0x1107f2 13 13)
      [.gpr 13, .gpr 13] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1107f2 13 13).toInstrSpec (test_r64_r64_effect_step 0x1107f2 0x4d 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107ed) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107f2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107f5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel32_effect_step 0x1107f5 4 0x15a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1107ea [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1107ea :=
  Rest.liftedBlock (rest_l1107ea code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1107ea x hx)

theorem rest_l1107fb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1107fb bytes_l1107fb) (entryMap (live .l1107fb))
      12 0x1107fb bytes_l1107fb b_l1107fb := by
  have f0 : InstrSpec 0x1107fb [0x4C, 0x89, 0x3C, 0x24] (StorePre 0x1107fb 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1107fb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1107fb 15 (.sib 4 none 0 .none))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1107fb 15 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1107fb 0x4c (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1107ff [0x48, 0x8D, 0x43, 0xFF] (fun s => s.RIP = 0x1107ff) (leaR64Effect 0x1107ff 0 (.base 3 (.d8 0xff)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1107ff 0 (.base 3 (.d8 0xff))).toInstrSpec (lea_r64_effect_step 0x1107ff 0x48 (by decide) 0 (.base 3 (.d8 0xff)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x110803 [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x110803 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x110803 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110803 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110803 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x110803 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x110808 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x110808) (movR64R64Effect 0x110808 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x110808 0 3).toInstrSpec (mov_r64_r64_effect_step 0x110808 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11080b [0x48, 0xD1, 0xE8] (fun s => s.RIP = 0x11080b) (shrR64Effect 0x11080b 3 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x11080b 3 0 1).toInstrSpec (shr_r64_one_effect_step 0x11080b 0x48 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11080e [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x11080e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11080e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11080e 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11080e 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x11080e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x110813 [0x0F, 0xB6, 0xC3] (fun s => s.RIP = 0x110813) (movzxR32R8Effect 0x110813 3 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x110813 3 0 3).toInstrSpec (movzx_r32_r8_effect_step 0x110813 0xc3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x110816 [0x89, 0x44, 0x24, 0x0C] (StorePre 0x110816 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x110816 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x110816 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x110816 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x110816 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x11081a [0x31, 0xED] (fun s => s.RIP = 0x11081a) (xorR32R32Effect 0x11081a 2 5 5)
      [.gpr 5, .gpr 5] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11081a 2 5 5).toInstrSpec (xor_r32_r32_effect_step 0x11081a 0xed (by decide)) pre_rip
  have f9 : InstrSpec 0x11081c [0x45, 0x31, 0xFF] (fun s => s.RIP = 0x11081c) (xorR32R32Effect 0x11081c 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11081c 3 15 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x11081c 0x45 0xff (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11081f [0x45, 0x31, 0xED] (fun s => s.RIP = 0x11081f) (xorR32R32Effect 0x11081f 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11081f 3 13 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x11081f 0x45 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1107ff) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110803) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110808) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11080b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11080e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110813) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110816) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11081a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (2, 2), (3, 3), (4, 4), (5, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11081c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 62), (2, 2), (3, 3), (4, 4), (5, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11081f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (2, 2), (3, 3), (4, 4), (5, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 69), (14, 14), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110822) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 71) (jmp_rel8_effect_step 0x110822 0x23 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1107fb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1107fb :=
  Rest.liftedBlock (rest_l1107fb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1107fb x hx)

theorem rest_l110830 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110830 bytes_l110830) (entryMap (live .l110830))
      1 0x110830 bytes_l110830 b_l110830 := by
  have f0 : InstrSpec 0x110830 [0x49, 0xFF, 0xC6] (fun s => s.RIP = 0x110830) (incR64Effect 0x110830 14)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (incR64Effect_footprint 0x110830 14).toInstrSpec (inc_r64_effect_step 0x110830 0x49 0xc6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110833) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l110830 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110830 :=
  Rest.liftedBlock (rest_l110830 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110830 x hx)

theorem rest_l110833 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110833 bytes_l110833) (entryMap (live .l110833))
      5 0x110833 bytes_l110833 b_l110833 := by
  have f0 : InstrSpec 0x110833 [0x49, 0x01, 0xEF] (fun s => s.RIP = 0x110833) (addR64R64Effect 0x110833 15 5)
      [.gpr 15, .gpr 5] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110833 15 5).toInstrSpec (add_r64_r64_effect_step 0x110833 0x49 0xef (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110836 [0x4C, 0x89, 0xFD] (fun s => s.RIP = 0x110836) (movR64R64Effect 0x110836 5 15)
      [.gpr 15] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x110836 5 15).toInstrSpec (mov_r64_r64_effect_step 0x110836 0x4c 0xfd (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x110839 [0x48, 0xF7, 0xDD] (fun s => s.RIP = 0x110839) (negR64Effect 0x110839 5)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (negR64Effect_footprint 0x110839 5).toInstrSpec (neg_r64_effect_step 0x110839 0x48 0xdd (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11083c [0x4C, 0x3B, 0x7C, 0x24, 0x18] (LoadPre 0x11083c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11083c + BitVec.ofNat 64 5)) 8) (cmpR64M64Effect 0x11083c 15 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 15, .gpr 4] [] [.flags, .rip] :=
    (cmpR64M64Effect_footprint 0x11083c 15 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (cmp_r64_m64_effect_step 0x11083c 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110836) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110839) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11083c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110841) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel32_effect_step 0x110841 3 0xf3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110833 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110833 :=
  Rest.liftedBlock (rest_l110833 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110833 x hx)

theorem rest_l110847 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110847 bytes_l110847) (entryMap (live .l110847))
      6 0x110847 bytes_l110847 b_l110847 := by
  have f0 : InstrSpec 0x110847 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x110847) (movR64R64Effect 0x110847 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x110847 6 15).toInstrSpec (mov_r64_r64_effect_step 0x110847 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11084a [0x48, 0xC1, 0xEE, 0x06] (fun s => s.RIP = 0x11084a) (shrR64Effect 0x11084a 4 6 6)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x11084a 4 6 6).toInstrSpec (shr_r64_imm8_effect_step 0x11084a 0x48 0xee 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11084e [0x44, 0x89, 0xFB] (fun s => s.RIP = 0x11084e) (movR32R32Effect 0x11084e 3 3 15)
      [.gpr 15] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x11084e 3 3 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x11084e 0x44 0xfb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x110851 [0x83, 0xE3, 0x3F] (fun s => s.RIP = 0x110851) (andR32Imm8Effect 0x110851 3 3 0x3f)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x110851 3 3 0x3f).toInstrSpec (and_r32_imm8_effect_step 0x110851 0xe3 0x3f (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x110854 [0x48, 0x8D, 0x7C, 0x24, 0x30] (fun s => s.RIP = 0x110854) (leaR64Effect 0x110854 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x110854 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x110854 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x110859 [0xE8, 0xA2, 0x38, 0x01, 0x00] (PushPre 0x110859 5) (callEffect (fun _ => 0x124100) 0x11085e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x110859 0x124100 0x11085e).toInstrSpec (call_rel32_effect_step 0x110859 0x138a2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11084a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11084e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 57), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110851) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 2), (3, 59), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110854) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 2), (3, 59), (4, 4), (5, 5), (6, 55), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110859) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (2, 2), (3, 59), (4, 63), (5, 5), (6, 55), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124100) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l110847 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110847 :=
  Rest.liftedBlock (rest_l110847 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110847 x hx)

theorem rest_l11085e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11085e bytes_l11085e) (entryMap (live .l11085e))
      3 0x11085e bytes_l11085e b_l11085e := by
  have f0 : InstrSpec 0x11085e [0x4A, 0x8D, 0x0C, 0x23] (fun s => s.RIP = 0x11085e) (leaR64Effect 0x11085e 1 (.sib 3 (some 12) 0 .none))
      [.gpr 3, .gpr 12] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x11085e 1 (.sib 3 (some 12) 0 .none)).toInstrSpec (lea_r64_effect_step 0x11085e 0x4a (by decide) 1 (.sib 3 (some 12) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110862 [0x48, 0x83, 0xF9, 0x40] (fun s => s.RIP = 0x110862) (cmpR64Imm8Effect 0x110862 1 0x40)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x110862 1 0x40).toInstrSpec (cmp_r64_imm8_effect_step 0x110862 0x48 0xf9 0x40 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110862) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110866) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x110866 3 0x18) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11085e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11085e :=
  Rest.liftedBlock (rest_l11085e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11085e x hx)

theorem rest_l110868 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110868 bytes_l110868) (entryMap (live .l110868))
      4 0x110868 bytes_l110868 b_l110868 := by
  have f0 : InstrSpec 0x110868 [0x89, 0xD9] (fun s => s.RIP = 0x110868) (movR32R32Effect 0x110868 2 1 3)
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x110868 2 1 3).toInstrSpec (mov_r32_r32_effect_step 0x110868 0xd9 (by decide)) pre_rip
  have f1 : InstrSpec 0x11086a [0x48, 0xD3, 0xE8] (fun s => s.RIP = 0x11086a) (shrR64ClEffect 0x11086a 3 0)
      [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x11086a 3 0).toInstrSpec (shr_r64_cl_effect_step 0x11086a 0x48 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11086d [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x11086d) (movR64R64Effect 0x11086d 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11086d 2 0).toInstrSpec (mov_r64_r64_effect_step 0x11086d 0x48 0xc2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11086a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11086d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110870) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel8_effect_step 0x110870 0x1b (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l110868 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110868 :=
  Rest.liftedBlock (rest_l110868 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110868 x hx)

theorem rest_l110880 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110880 bytes_l110880) (entryMap (live .l110880))
      5 0x110880 bytes_l110880 b_l110880 := by
  have f0 : InstrSpec 0x110880 [0x89, 0xD9] (fun s => s.RIP = 0x110880) (movR32R32Effect 0x110880 2 1 3)
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x110880 2 1 3).toInstrSpec (mov_r32_r32_effect_step 0x110880 0xd9 (by decide)) pre_rip
  have f1 : InstrSpec 0x110882 [0x48, 0xD3, 0xE8] (fun s => s.RIP = 0x110882) (shrR64ClEffect 0x110882 3 0)
      [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x110882 3 0).toInstrSpec (shr_r64_cl_effect_step 0x110882 0x48 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x110885 [0x89, 0xE9] (fun s => s.RIP = 0x110885) (movR32R32Effect 0x110885 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x110885 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x110885 0xe9 (by decide)) pre_rip
  have f3 : InstrSpec 0x110887 [0x48, 0xD3, 0xE2] (fun s => s.RIP = 0x110887) (shlR64ClEffect 0x110887 3 2)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x110887 3 2).toInstrSpec (shl_r64_cl_effect_step 0x110887 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11088a [0x48, 0x09, 0xC2] (fun s => s.RIP = 0x11088a) (orR64R64Effect 0x11088a 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11088a 2 0).toInstrSpec (or_r64_r64_effect_step 0x11088a 0x48 0xc2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110882) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110885) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110887) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11088a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11088d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 63) (by decide) rfl

theorem block_l110880 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110880 :=
  Rest.liftedBlock (rest_l110880 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110880 x hx)

theorem rest_l11088d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11088d bytes_l11088d) (entryMap (live .l11088d))
      5 0x11088d bytes_l11088d b_l11088d := by
  have f0 : InstrSpec 0x11088d [0x48, 0x23, 0x54, 0x24, 0x28] (LoadPre 0x11088d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11088d + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x11088d 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (andR64M64Effect_footprint 0x11088d 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (and_r64_m64_effect_step 0x11088d 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x110892 [0x4C, 0x01, 0xEA] (fun s => s.RIP = 0x110892) (addR64R64Effect 0x110892 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110892 2 13).toInstrSpec (add_r64_r64_effect_step 0x110892 0x4c 0xea (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x110895 [0xF6, 0xC2, 0x01] (fun s => s.RIP = 0x110895) (testR8Imm8LowEffect 0x110895 2 0x1)
      [.gpr 2] [] [.flags, .rip] :=
    (testR8Imm8LowEffect_footprint 0x110895 2 0x1).toInstrSpec (test_r8_imm8_low_effect_step 0x110895 0xc2 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x110898 [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x110898 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x110898 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110898 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x110898 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x110898 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110892) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110895) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110898) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11089d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x11089d 5 0x31) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11088d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11088d :=
  Rest.liftedBlock (rest_l11088d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11088d x hx)

theorem rest_l11089f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11089f bytes_l11089f) (entryMap (live .l11089f))
      2 0x11089f bytes_l11089f b_l11089f := by
  have f0 : InstrSpec 0x11089f [0x4C, 0x39, 0x34, 0x24] (LoadPre 0x11089f (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11089f + BitVec.ofNat 64 4)) 8) (cmpMREffect 0x11089f 4 64 14 (.sib 4 none 0 .none))
      [.gpr 14, .gpr 4] [] [.flags, .rip] :=
    (cmpMREffect64_footprint 0x11089f 4 14 (.sib 4 none 0 .none)).toInstrSpec (cmp_m64_r64_effect_step 0x11089f 0x4c (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108a3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x1108a3 6 0xd1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11089f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11089f :=
  Rest.liftedBlock (rest_l11089f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11089f x hx)

theorem rest_l1108a9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1108a9 bytes_l1108a9) (entryMap (live .l1108a9))
      7 0x1108a9 bytes_l1108a9 b_l1108a9 := by
  have f0 : InstrSpec 0x1108a9 [0x42, 0xC6, 0x04, 0x36, 0x00] (StorePre 0x1108a9 5 (fun s => AddrMode.addr (.sib 6 (some 14) 0 .none) s (0x1108a9 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1108a9 (.sib 6 (some 14) 0 .none) 0x0)
      [.gpr 6, .gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x1108a9 (.sib 6 (some 14) 0 .none) 0x0).toInstrSpec (mov_m8_imm8_rex_effect_step 0x1108a9 0x42 (by decide) (.sib 6 (some 14) 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1108ae [0x49, 0xFF, 0xC6] (fun s => s.RIP = 0x1108ae) (incR64Effect 0x1108ae 14)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (incR64Effect_footprint 0x1108ae 14).toInstrSpec (inc_r64_effect_step 0x1108ae 0x49 0xc6 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1108b1 [0x49, 0xFF, 0xC7] (fun s => s.RIP = 0x1108b1) (incR64Effect 0x1108b1 15)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (incR64Effect_footprint 0x1108b1 15).toInstrSpec (inc_r64_effect_step 0x1108b1 0x49 0xc7 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1108b4 [0x4C, 0x89, 0xFD] (fun s => s.RIP = 0x1108b4) (movR64R64Effect 0x1108b4 5 15)
      [.gpr 15] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1108b4 5 15).toInstrSpec (mov_r64_r64_effect_step 0x1108b4 0x4c 0xfd (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1108b7 [0x48, 0xF7, 0xDD] (fun s => s.RIP = 0x1108b7) (negR64Effect 0x1108b7 5)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (negR64Effect_footprint 0x1108b7 5).toInstrSpec (neg_r64_effect_step 0x1108b7 0x48 0xdd (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1108ba [0x4C, 0x3B, 0x7C, 0x24, 0x18] (LoadPre 0x1108ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1108ba + BitVec.ofNat 64 5)) 8) (cmpR64M64Effect 0x1108ba 15 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 15, .gpr 4] [] [.flags, .rip] :=
    (cmpR64M64Effect_footprint 0x1108ba 15 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (cmp_r64_m64_effect_step 0x1108ba 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108ae) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108b1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 54), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108b4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 54), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108b7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 60), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 54), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108ba) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 60), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 54), (15, 56), (16, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108bf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x1108bf 2 0x86) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1108a9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1108a9 :=
  Rest.liftedBlock (rest_l1108a9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1108a9 x hx)

theorem rest_l1108c1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1108c1 bytes_l1108c1) (entryMap (live .l1108c1))
      1 0x1108c1 bytes_l1108c1 b_l1108c1 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x1108c1 0x77 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1108c1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1108c1 :=
  Rest.liftedBlock (rest_l1108c1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1108c1 x hx)

theorem rest_l1108d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1108d0 bytes_l1108d0) (entryMap (live .l1108d0))
      3 0x1108d0 bytes_l1108d0 b_l1108d0 := by
  have f0 : InstrSpec 0x1108d0 [0x48, 0x8B, 0x04, 0x24] (LoadPre 0x1108d0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1108d0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1108d0 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1108d0 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1108d0 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1108d4 [0x4C, 0x29, 0xF0] (fun s => s.RIP = 0x1108d4) (subR64R64Effect 0x1108d4 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1108d4 0 14).toInstrSpec (sub_r64_r64_effect_step 0x1108d4 0x4c 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108d4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 57) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 56), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108d7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x1108d7 6 0xb0) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1108d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1108d0 :=
  Rest.liftedBlock (rest_l1108d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1108d0 x hx)

theorem rest_l1108dd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1108dd bytes_l1108dd) (entryMap (live .l1108dd))
      13 0x1108dd bytes_l1108dd b_l1108dd := by
  have f0 : InstrSpec 0x1108dd [0x45, 0x31, 0xED] (fun s => s.RIP = 0x1108dd) (xorR32R32Effect 0x1108dd 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1108dd 3 13 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x1108dd 0x45 0xed (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1108e0 [0x48, 0x3B, 0x54, 0x24, 0x20] (LoadPre 0x1108e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1108e0 + BitVec.ofNat 64 5)) 8) (cmpR64M64Effect 0x1108e0 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 2, .gpr 4] [] [.flags, .rip] :=
    (cmpR64M64Effect_footprint 0x1108e0 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (cmp_r64_m64_effect_step 0x1108e0 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1108e5 [0x41, 0x0F, 0x93, 0xC5] (fun s => s.RIP = 0x1108e5) (atFlags (condHolds 3) (setccR8Effect 0x1108e5 4 13))
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 13, .rip] :=
    (setccR8Effect_footprint 0x1108e5 4 13 3).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1108e5 3 0x41 (by decide) 0xc5 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x1108e9 [0xB9, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1108e9) (movR32Imm32Effect 0x1108e9 5 1 0x0)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1108e9 5 1 0x0).toInstrSpec (mov_r32_imm32_effect_step 0x1108e9 0xb9 (by decide) 0x0) pre_rip
  have f4 : InstrSpec 0x1108ee [0x0F, 0x43, 0x4C, 0x24, 0x0C] (LoadPre 0x1108ee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1108ee + BitVec.ofNat 64 5)) 4) (atFlags (condHolds 3) (cmovR32M32Effect 0x1108ee 5 1 (.sib 4 none 0 (.d8 0xc))))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 1, .rip] :=
    (cmovR32M32Effect_footprint 0x1108ee 5 1 (.sib 4 none 0 (.d8 0xc)) 3).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_m32_effect_step 0x1108ee 3 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1108f3 [0x28, 0xCA] (fun s => s.RIP = 0x1108f3) (subR8R8Effect 0x1108f3 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (subR8R8Effect_footprint 0x1108f3 2 2 1).toInstrSpec (sub_r8_r8_effect_step 0x1108f3 0xca (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1108f5 [0x42, 0x88, 0x14, 0x36] (StorePre 0x1108f5 4 (fun s => AddrMode.addr (.sib 6 (some 14) 0 .none) s (0x1108f5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1108f5 4 2 (.sib 6 (some 14) 0 .none))
      [.gpr 2, .gpr 6, .gpr 14] [] [.rip] :=
    (movM8R8Effect_footprint 0x1108f5 4 2 (.sib 6 (some 14) 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x1108f5 0x42 (by decide) 2 (.sib 6 (some 14) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1108f9 [0x48, 0x03, 0x6C, 0x24, 0x18] (LoadPre 0x1108f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1108f9 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1108f9 5 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 5, .gpr 4] [] [.reg 5, .flags, .rip] :=
    (addR64M64Effect_footprint 0x1108f9 5 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (add_r64_m64_effect_step 0x1108f9 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1108fe [0x4C, 0x29, 0xED] (fun s => s.RIP = 0x1108fe) (subR64R64Effect 0x1108fe 5 13)
      [.gpr 5, .gpr 13] [] [.reg 5, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1108fe 5 13).toInstrSpec (sub_r64_r64_effect_step 0x1108fe 0x4c 0xed (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x110901 [0x4C, 0x39, 0xE5] (fun s => s.RIP = 0x110901) (cmpR64R64Effect 0x110901 5 12)
      [.gpr 5, .gpr 12] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x110901 5 12).toInstrSpec (cmp_r64_r64_effect_step 0x110901 0x4c 0xe5 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x110904 [0x49, 0x0F, 0x43, 0xEC] (fun s => s.RIP = 0x110904) (atFlags (condHolds 3) (cmovR64R64Effect 0x110904 4 5 12))
      [.gpr 5, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .rip] :=
    (cmovR64R64Effect_footprint 0x110904 4 5 12 3).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x110904 3 0x49 (by decide) 0xec (by decide) c)) pre_rip
  have f11 : InstrSpec 0x110908 [0x48, 0x83, 0xFD, 0x02] (fun s => s.RIP = 0x110908) (cmpR64Imm8Effect 0x110908 5 0x2)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x110908 5 0x2).toInstrSpec (cmp_r64_imm8_effect_step 0x110908 0x48 0xfd 0x2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108e0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108e5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108e9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108ee) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108f3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 61), (2, 63), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108f5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 61), (2, 63), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108f9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 61), (2, 63), (4, 4), (5, 66), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1108fe) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 61), (2, 63), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110901) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 61), (2, 63), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (16, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110904) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 61), (2, 63), (4, 4), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (16, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110908) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 61), (2, 63), (4, 4), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11090c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 76) (jcc_rel32_effect_step 0x11090c 2 0xffffff1e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1108dd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1108dd :=
  Rest.liftedBlock (rest_l1108dd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1108dd x hx)

theorem rest_l110912 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110912 bytes_l110912) (entryMap (live .l110912))
      4 0x110912 bytes_l110912 b_l110912 := by
  have f0 : InstrSpec 0x110912 [0x49, 0x8D, 0x0C, 0x2E] (fun s => s.RIP = 0x110912) (leaR64Effect 0x110912 1 (.sib 14 (some 5) 0 .none))
      [.gpr 14, .gpr 5] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x110912 1 (.sib 14 (some 5) 0 .none)).toInstrSpec (lea_r64_effect_step 0x110912 0x49 (by decide) 1 (.sib 14 (some 5) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110916 [0x49, 0x01, 0xF6] (fun s => s.RIP = 0x110916) (addR64R64Effect 0x110916 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110916 14 6).toInstrSpec (add_r64_r64_effect_step 0x110916 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x110919 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x110919) (movR32Imm32Effect 0x110919 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x110919 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x110919 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x11091e [0x66, 0x90] (fun s => s.RIP = 0x11091e) (fun _ => nopEffect 0x11091e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x11091e 2).toInstrSpec (nop_66_effect_step 0x11091e) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110916) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110919) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11091e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110920) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l110912 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110912 :=
  Rest.liftedBlock (rest_l110912 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110912 x hx)

theorem rest_l110920 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110920 bytes_l110920) (entryMap (live .l110920))
      2 0x110920 bytes_l110920 b_l110920 := by
  have f0 : InstrSpec 0x110920 [0x48, 0x39, 0xD0] (fun s => s.RIP = 0x110920) (cmpR64R64Effect 0x110920 0 2)
      [.gpr 0, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x110920 0 2).toInstrSpec (cmp_r64_r64_effect_step 0x110920 0x48 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110923) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x110923 4 0x42) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110920 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110920 :=
  Rest.liftedBlock (rest_l110920 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110920 x hx)

theorem rest_l110925 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110925 bytes_l110925) (entryMap (live .l110925))
      4 0x110925 bytes_l110925 b_l110925 := by
  have f0 : InstrSpec 0x110925 [0x41, 0xC6, 0x04, 0x16, 0x00] (StorePre 0x110925 5 (fun s => AddrMode.addr (.sib 14 (some 2) 0 .none) s (0x110925 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x110925 (.sib 14 (some 2) 0 .none) 0x0)
      [.gpr 14, .gpr 2] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x110925 (.sib 14 (some 2) 0 .none) 0x0).toInstrSpec (mov_m8_imm8_rex_effect_step 0x110925 0x41 (by decide) (.sib 14 (some 2) 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11092a [0x48, 0xFF, 0xC2] (fun s => s.RIP = 0x11092a) (incR64Effect 0x11092a 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (incR64Effect_footprint 0x11092a 2).toInstrSpec (inc_r64_effect_step 0x11092a 0x48 0xc2 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11092d [0x48, 0x39, 0xD5] (fun s => s.RIP = 0x11092d) (cmpR64R64Effect 0x11092d 5 2)
      [.gpr 5, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11092d 5 2).toInstrSpec (cmp_r64_r64_effect_step 0x11092d 0x48 0xd5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11092a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 54), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11092d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 54), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110930) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x110930 5 0xee) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l110925 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110925 :=
  Rest.liftedBlock (rest_l110925 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110925 x hx)

theorem rest_l110932 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110932 bytes_l110932) (entryMap (live .l110932))
      2 0x110932 bytes_l110932 b_l110932 := by
  have f0 : InstrSpec 0x110932 [0x49, 0x89, 0xCE] (fun s => s.RIP = 0x110932) (movR64R64Effect 0x110932 14 1)
      [.gpr 1] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x110932 14 1).toInstrSpec (mov_r64_r64_effect_step 0x110932 0x49 0xce (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110935) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x110935 0xfffffef9 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l110932 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110932 :=
  Rest.liftedBlock (rest_l110932 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110932 x hx)

theorem rest_l11093a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11093a bytes_l11093a) (entryMap (live .l11093a))
      2 0x11093a bytes_l11093a b_l11093a := by
  have f0 : InstrSpec 0x11093a [0x4D, 0x85, 0xED] (fun s => s.RIP = 0x11093a) (testR64R64Effect 0x11093a 13 13)
      [.gpr 13, .gpr 13] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x11093a 13 13).toInstrSpec (test_r64_r64_effect_step 0x11093a 0x4d 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11093d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x11093d 4 0x16) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11093a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11093a :=
  Rest.liftedBlock (rest_l11093a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11093a x hx)

theorem rest_l11093f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11093f bytes_l11093f) (entryMap (live .l11093f))
      3 0x11093f bytes_l11093f b_l11093f := by
  have f0 : InstrSpec 0x11093f [0x48, 0x8B, 0x34, 0x24] (LoadPre 0x11093f (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11093f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11093f 6 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11093f 6 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11093f 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x110943 [0x49, 0x39, 0xF6] (fun s => s.RIP = 0x110943) (cmpR64R64Effect 0x110943 14 6)
      [.gpr 14, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x110943 14 6).toInstrSpec (cmp_r64_r64_effect_step 0x110943 0x49 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110943) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110946) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x110946 3 0x58) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11093f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11093f :=
  Rest.liftedBlock (rest_l11093f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11093f x hx)

theorem rest_l110948 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110948 bytes_l110948) (entryMap (live .l110948))
      3 0x110948 bytes_l110948 b_l110948 := by
  have f0 : InstrSpec 0x110948 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x110948 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x110948 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110948 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x110948 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x110948 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11094d [0x42, 0xC6, 0x04, 0x30, 0x01] (StorePre 0x11094d 5 (fun s => AddrMode.addr (.sib 0 (some 14) 0 .none) s (0x11094d + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x11094d (.sib 0 (some 14) 0 .none) 0x1)
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x11094d (.sib 0 (some 14) 0 .none) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x11094d 0x42 (by decide) (.sib 0 (some 14) 0 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x110952 [0x49, 0xFF, 0xC6] (fun s => s.RIP = 0x110952) (incR64Effect 0x110952 14)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (incR64Effect_footprint 0x110952 14).toInstrSpec (inc_r64_effect_step 0x110952 0x49 0xc6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11094d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110952) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110955) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l110948 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110948 :=
  Rest.liftedBlock (rest_l110948 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110948 x hx)

theorem rest_l110955 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110955 bytes_l110955) (entryMap (live .l110955))
      9 0x110955 bytes_l110955 b_l110955 := by
  have f0 : InstrSpec 0x110955 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x110955) (movR64R64Effect 0x110955 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x110955 0 14).toInstrSpec (mov_r64_r64_effect_step 0x110955 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110958 [0x48, 0x83, 0xC4, 0x58] (fun s => s.RIP = 0x110958) (addR64Imm8Effect 0x110958 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x110958 4 0x58).toInstrSpec (add_r64_imm8_effect_step 0x110958 0x48 0xc4 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11095c [0x5B] (PopPre 0x11095c) (popR64Effect 0x11095c 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11095c 1 3).toInstrSpec (pop_r64_effect_step 0x11095c 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x11095d [0x41, 0x5C] (PopPre 0x11095d) (popR64Effect 0x11095d 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11095d 2 12).toInstrSpec (pop_r64_rex_effect_step 0x11095d 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x11095f [0x41, 0x5D] (PopPre 0x11095f) (popR64Effect 0x11095f 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11095f 2 13).toInstrSpec (pop_r64_rex_effect_step 0x11095f 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x110961 [0x41, 0x5E] (PopPre 0x110961) (popR64Effect 0x110961 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110961 2 14).toInstrSpec (pop_r64_rex_effect_step 0x110961 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x110963 [0x41, 0x5F] (PopPre 0x110963) (popR64Effect 0x110963 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110963 2 15).toInstrSpec (pop_r64_rex_effect_step 0x110963 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x110965 [0x5D] (PopPre 0x110965) (popR64Effect 0x110965 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110965 1 5).toInstrSpec (pop_r64_effect_step 0x110965 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x110966 [0xC3] (RetPre 0x110966) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x110966).toInstrSpec (ret_effect_step 0x110966) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110958) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11095c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11095d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11095f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110961) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110963) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110965) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110966) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l110955 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110955 :=
  Rest.liftedBlock (rest_l110955 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110955 x hx)

theorem rest_l110967 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110967 bytes_l110967) (entryMap (live .l110967))
      4 0x110967 bytes_l110967 b_l110967 := by
  have f0 : InstrSpec 0x110967 [0x48, 0x8B, 0x3C, 0x24] (LoadPre 0x110967 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110967 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110967 7 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x110967 7 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x110967 0x48 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11096b [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x11096b) (movR64R64Effect 0x11096b 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11096b 6 7).toInstrSpec (mov_r64_r64_effect_step 0x11096b 0x48 0xfe (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11096e [0x48, 0xC7, 0xC2, 0x30, 0x2D, 0x20, 0x00] (fun s => s.RIP = 0x11096e) (movR64Imm32Effect 0x11096e 2 0x202d30)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x11096e 2 0x202d30).toInstrSpec (mov_r64_imm32_effect_step 0x11096e 0x48 0xc2 (by decide) (by decide) (by decide) 0x202d30) pre_rip
  have f3 : InstrSpec 0x110975 [0xE8, 0x78, 0x8C, 0x01, 0x00] (PushPre 0x110975 5) (callEffect (fun _ => 0x1295f2) 0x11097a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x110975 0x1295f2 0x11097a).toInstrSpec (call_rel32_effect_step 0x110975 0x18c78 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x11096b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x11096e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x110975) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x1295f2) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l110967 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110967 :=
  Rest.liftedBlock (rest_l110967 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110967 x hx)

theorem rest_l11097a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11097a bytes_l11097a) (entryMap (live .l11097a))
      4 0x11097a bytes_l11097a b_l11097a := by
  have f0 : InstrSpec 0x11097a [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11097a) (movR64R64Effect 0x11097a 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11097a 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11097a 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11097d [0x48, 0x8B, 0x34, 0x24] (LoadPre 0x11097d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11097d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11097d 6 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11097d 6 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11097d 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x110981 [0x48, 0xC7, 0xC2, 0x00, 0x2D, 0x20, 0x00] (fun s => s.RIP = 0x110981) (movR64Imm32Effect 0x110981 2 0x202d00)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x110981 2 0x202d00).toInstrSpec (mov_r64_imm32_effect_step 0x110981 0x48 0xc2 (by decide) (by decide) (by decide) 0x202d00) pre_rip
  have f3 : InstrSpec 0x110988 [0xE8, 0x65, 0x8C, 0x01, 0x00] (PushPre 0x110988 5) (callEffect (fun _ => 0x1295f2) 0x11098d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x110988 0x1295f2 0x11098d).toInstrSpec (call_rel32_effect_step 0x110988 0x18c65 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53), (14, 14)]) (p' := 0x11097d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53), (14, 14)]) (p' := 0x110981) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53), (14, 14)]) (p' := 0x110988) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53), (14, 14)]) (p' := 0x1295f2) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l11097a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11097a :=
  Rest.liftedBlock (rest_l11097a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11097a x hx)

theorem rest_l11098d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11098d bytes_l11098d) (entryMap (live .l11098d))
      4 0x11098d bytes_l11098d b_l11098d := by
  have f0 : InstrSpec 0x11098d [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11098d) (movR64R64Effect 0x11098d 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11098d 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11098d 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110990 [0x48, 0x8B, 0x34, 0x24] (LoadPre 0x110990 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110990 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110990 6 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x110990 6 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x110990 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x110994 [0x48, 0xC7, 0xC2, 0x18, 0x2D, 0x20, 0x00] (fun s => s.RIP = 0x110994) (movR64Imm32Effect 0x110994 2 0x202d18)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x110994 2 0x202d18).toInstrSpec (mov_r64_imm32_effect_step 0x110994 0x48 0xc2 (by decide) (by decide) (by decide) 0x202d18) pre_rip
  have f3 : InstrSpec 0x11099b [0xE8, 0x52, 0x8C, 0x01, 0x00] (PushPre 0x11099b 5) (callEffect (fun _ => 0x1295f2) 0x1109a0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11099b 0x1295f2 0x1109a0).toInstrSpec (call_rel32_effect_step 0x11099b 0x18c52 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53), (14, 14)]) (p' := 0x110990) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53), (14, 14)]) (p' := 0x110994) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53), (14, 14)]) (p' := 0x11099b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53), (14, 14)]) (p' := 0x1295f2) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l11098d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11098d :=
  Rest.liftedBlock (rest_l11098d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11098d x hx)

theorem rest_l1109a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1109a0 bytes_l1109a0) (entryMap (live .l1109a0))
      3 0x1109a0 bytes_l1109a0 b_l1109a0 := by
  have f0 : InstrSpec 0x1109a0 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1109a0) (movR64R64Effect 0x1109a0 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1109a0 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1109a0 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1109a3 [0x48, 0xC7, 0xC2, 0xE8, 0x2C, 0x20, 0x00] (fun s => s.RIP = 0x1109a3) (movR64Imm32Effect 0x1109a3 2 0x202ce8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x1109a3 2 0x202ce8).toInstrSpec (mov_r64_imm32_effect_step 0x1109a3 0x48 0xc2 (by decide) (by decide) (by decide) 0x202ce8) pre_rip
  have f2 : InstrSpec 0x1109aa [0xE8, 0x43, 0x8C, 0x01, 0x00] (PushPre 0x1109aa 5) (callEffect (fun _ => 0x1295f2) 0x1109af)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1109aa 0x1295f2 0x1109af).toInstrSpec (call_rel32_effect_step 0x1109aa 0x18c43 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53), (14, 14)]) (p' := 0x1109a3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (14, 14)]) (p' := 0x1109aa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53), (14, 14)]) (p' := 0x1295f2) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1109a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1109a0 :=
  Rest.liftedBlock (rest_l1109a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1109a0 x hx)

theorem rest_l1109af [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1109af bytes_l1109af) (entryMap (live .l1109af))
      1 0x1109af bytes_l1109af b_l1109af := by
  have f0 : InstrSpec 0x1109af [0x90] (fun s => s.RIP = 0x1109af) (fun _ => nopEffect 0x1109af 1)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1109af 1).toInstrSpec (nop_effect_step 0x1109af) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1109b0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l1109af [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1109af :=
  Rest.liftedBlock (rest_l1109af code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1109af x hx)

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

theorem_by block_l1107b0_eval :
    program.runBlock (dialect code) ⟨.l1107b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1107ea_eval :
    program.runBlock (dialect code) ⟨.l1107ea, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1107fb_eval :
    program.runBlock (dialect code) ⟨.l1107fb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110830_eval :
    program.runBlock (dialect code) ⟨.l110830, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110833_eval :
    program.runBlock (dialect code) ⟨.l110833, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110847_eval :
    program.runBlock (dialect code) ⟨.l110847, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11085e_eval :
    program.runBlock (dialect code) ⟨.l11085e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110868_eval :
    program.runBlock (dialect code) ⟨.l110868, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110880_eval :
    program.runBlock (dialect code) ⟨.l110880, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11088d_eval :
    program.runBlock (dialect code) ⟨.l11088d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11089f_eval :
    program.runBlock (dialect code) ⟨.l11089f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1108a9_eval :
    program.runBlock (dialect code) ⟨.l1108a9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1108c1_eval :
    program.runBlock (dialect code) ⟨.l1108c1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1108d0_eval :
    program.runBlock (dialect code) ⟨.l1108d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1108dd_eval :
    program.runBlock (dialect code) ⟨.l1108dd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110912_eval :
    program.runBlock (dialect code) ⟨.l110912, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110920_eval :
    program.runBlock (dialect code) ⟨.l110920, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110925_eval :
    program.runBlock (dialect code) ⟨.l110925, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110932_eval :
    program.runBlock (dialect code) ⟨.l110932, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11093a_eval :
    program.runBlock (dialect code) ⟨.l11093a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11093f_eval :
    program.runBlock (dialect code) ⟨.l11093f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110948_eval :
    program.runBlock (dialect code) ⟨.l110948, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110955_eval :
    program.runBlock (dialect code) ⟨.l110955, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110967_eval :
    program.runBlock (dialect code) ⟨.l110967, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11097a_eval :
    program.runBlock (dialect code) ⟨.l11097a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11098d_eval :
    program.runBlock (dialect code) ⟨.l11098d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1109a0_eval :
    program.runBlock (dialect code) ⟨.l1109a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1109af_eval :
    program.runBlock (dialect code) ⟨.l1109af, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
