import K256.Proofs.Ecdh.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Ecdh.LIR.Generated.Values

namespace K256.Proofs.Ecdh.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR

theorem rest_l11c510_1 [Bindings] (code : CodeMap) :
    Rest (n := 95) code lifted (codeRange 0x11c510 bytes_l11c510) [(0, 87), (1, 83), (2, 2), (3, 71), (4, 65), (5, 67), (6, 81), (7, 82), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 93), (14, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x11c54c bytes_l11c510_1 b_l11c510_1 := by
  have f20 : InstrSpec 0x11c54c [0x31, 0xFF] (fun s => s.RIP = 0x11c54c) (xorR32R32Effect 0x11c54c 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c54c 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x11c54c 0xff (by decide)) pre_rip
  have f21 : InstrSpec 0x11c54e [0x41, 0x80, 0xFD, 0x01] (fun s => s.RIP = 0x11c54e) (cmpR8Imm8Effect 0x11c54e 4 13 0x1)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x11c54e 4 13 0x1).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x11c54e 0x41 0xfd 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x11c552 [0x40, 0x0F, 0x94, 0xC7] (fun s => s.RIP = 0x11c552) (atFlags (condHolds 4) (setccR8Effect 0x11c552 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x11c552 4 7 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11c552 4 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f23 : InstrSpec 0x11c556 [0xE8, 0xF5, 0xB7, 0x00, 0x00] (PushPre 0x11c556 5) (callEffect (fun _ => 0x127d50) 0x11c55b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c556 0x127d50 0x11c55b).toInstrSpec (call_rel32_effect_step 0x11c556 0xb7f5 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f20 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 87), (1, 83), (2, 2), (3, 71), (4, 65), (5, 67), (6, 81), (7, 95), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 93), (14, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c54e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f21 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 87), (1, 83), (2, 2), (3, 71), (4, 65), (5, 67), (6, 81), (7, 95), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 93), (14, 73), (15, 69), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c552) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f22 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 87), (1, 83), (2, 2), (3, 71), (4, 65), (5, 67), (6, 81), (7, 99), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 93), (14, 73), (15, 69), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c556) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f23 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 87), (1, 83), (2, 2), (3, 71), (4, 101), (5, 67), (6, 81), (7, 99), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 93), (14, 73), (15, 69), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f23 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 103) (by decide) (by decide) rfl rfl

theorem rest_l11c510 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c510 bytes_l11c510) (entryMap (live .l11c510))
      24 0x11c510 bytes_l11c510 b_l11c510 := by
  have f0 : InstrSpec 0x11c510 [0x55] (PushPre 0x11c510 1) (pushR64Effect 0x11c510 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c510 1 5).toInstrSpec (push_r64_effect_step 0x11c510 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x11c511 [0x41, 0x57] (PushPre 0x11c511 2) (pushR64Effect 0x11c511 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c511 2 15).toInstrSpec (push_r64_rex_effect_step 0x11c511 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x11c513 [0x41, 0x56] (PushPre 0x11c513 2) (pushR64Effect 0x11c513 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c513 2 14).toInstrSpec (push_r64_rex_effect_step 0x11c513 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x11c515 [0x41, 0x55] (PushPre 0x11c515 2) (pushR64Effect 0x11c515 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c515 2 13).toInstrSpec (push_r64_rex_effect_step 0x11c515 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x11c517 [0x41, 0x54] (PushPre 0x11c517 2) (pushR64Effect 0x11c517 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c517 2 12).toInstrSpec (push_r64_rex_effect_step 0x11c517 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x11c519 [0x53] (PushPre 0x11c519 1) (pushR64Effect 0x11c519 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c519 1 3).toInstrSpec (push_r64_effect_step 0x11c519 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x11c51a [0x48, 0x81, 0xEC, 0x68, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11c51a) (subR64Imm32Effect 0x11c51a 4 0x168)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x11c51a 4 0x168).toInstrSpec (sub_r64_imm32_effect_step 0x11c51a 0x48 0xec 0x168 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11c521 [0x89, 0xD5] (fun s => s.RIP = 0x11c521) (movR32R32Effect 0x11c521 2 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x11c521 2 5 2).toInstrSpec (mov_r32_r32_effect_step 0x11c521 0xd5 (by decide)) pre_rip
  have f8 : InstrSpec 0x11c523 [0x49, 0x89, 0xF7] (fun s => s.RIP = 0x11c523) (movR64R64Effect 0x11c523 15 6)
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x11c523 15 6).toInstrSpec (mov_r64_r64_effect_step 0x11c523 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11c526 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x11c526) (movR64R64Effect 0x11c526 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x11c526 3 7).toInstrSpec (mov_r64_r64_effect_step 0x11c526 0x48 0xfb (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11c529 [0x49, 0x89, 0xE6] (fun s => s.RIP = 0x11c529) (movR64R64Effect 0x11c529 14 4)
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x11c529 14 4).toInstrSpec (mov_r64_r64_effect_step 0x11c529 0x49 0xe6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11c52c [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c52c) (movR32Imm32Effect 0x11c52c 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11c52c 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11c52c 0xb9 (by decide) 0xf) pre_rip
  have f12 : InstrSpec 0x11c531 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11c531) (movR64R64Effect 0x11c531 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c531 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11c531 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11c534 [0x48, 0xC7, 0xC6, 0x58, 0x32, 0x20, 0x00] (fun s => s.RIP = 0x11c534) (movR64Imm32Effect 0x11c534 6 0x203258)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x11c534 6 0x203258).toInstrSpec (mov_r64_imm32_effect_step 0x11c534 0x48 0xc6 (by decide) (by decide) (by decide) 0x203258) pre_rip
  have f14 : InstrSpec 0x11c53b [0xF3, 0x48, 0xA5] (RepPre 0x11c53b (RepMovsqPre 0x11c53b)) (repMovsqEffect 0x11c53b)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11c53b).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11c53b 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f15 : InstrSpec 0x11c53e [0x89, 0xE8] (fun s => s.RIP = 0x11c53e) (movR32R32Effect 0x11c53e 2 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x11c53e 2 0 5).toInstrSpec (mov_r32_r32_effect_step 0x11c53e 0xe8 (by decide)) pre_rip
  have f16 : InstrSpec 0x11c540 [0xC0, 0xF8, 0x07] (fun s => s.RIP = 0x11c540) (sarR8Effect 0x11c540 3 0 7)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (sarR8Effect_footprint 0x11c540 3 0 7).toInstrSpec (sar_r8_imm8_effect_step 0x11c540 0xf8 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x11c543 [0x41, 0x89, 0xED] (fun s => s.RIP = 0x11c543) (movR32R32Effect 0x11c543 3 13 5)
      [.gpr 5] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x11c543 3 13 5).toInstrSpec (mov_r32_r32_rex_effect_step 0x11c543 0x41 0xed (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11c546 [0x41, 0x30, 0xC5] (fun s => s.RIP = 0x11c546) (xorR8R8Effect 0x11c546 3 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR8R8Effect_footprint 0x11c546 3 13 0).toInstrSpec (xor_r8_r8_rex_effect_step 0x11c546 0x41 0xc5 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11c549 [0x41, 0x28, 0xC5] (fun s => s.RIP = 0x11c549) (subR8R8Effect 0x11c549 3 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (subR8R8Effect_footprint 0x11c549 3 13 0).toInstrSpec (sub_r8_r8_rex_effect_step 0x11c549 0x41 0xc5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c511) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c513) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c515) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c517) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c519) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c51a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c521) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c523) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c526) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 2), (3, 71), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c529) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(2, 2), (3, 71), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c52c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 75), (2, 2), (3, 71), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c531) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 75), (2, 2), (3, 71), (4, 65), (5, 67), (6, 6), (7, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c534) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 75), (2, 2), (3, 71), (4, 65), (5, 67), (6, 79), (7, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c53b) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 82) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 83) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(1, 83), (2, 2), (3, 71), (4, 65), (5, 67), (6, 81), (7, 82), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c53e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 83), (2, 2), (3, 71), (4, 65), (5, 67), (6, 81), (7, 82), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c540) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 83), (2, 2), (3, 71), (4, 65), (5, 67), (6, 81), (7, 82), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c543) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f17 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 87), (1, 83), (2, 2), (3, 71), (4, 65), (5, 67), (6, 81), (7, 82), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 89), (14, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c546) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f18 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 87), (1, 83), (2, 2), (3, 71), (4, 65), (5, 67), (6, 81), (7, 82), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 91), (14, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c549) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f19 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 87), (1, 83), (2, 2), (3, 71), (4, 65), (5, 67), (6, 81), (7, 82), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 93), (14, 73), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c54c) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11c510_1 code

theorem block_l11c510 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c510 :=
  Rest.liftedBlock (rest_l11c510 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c510 x hx)

theorem rest_l11c55b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c55b bytes_l11c55b) (entryMap (live .l11c55b))
      6 0x11c55b bytes_l11c55b b_l11c55b := by
  have f0 : InstrSpec 0x11c55b [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x11c55b) (movzxR32R8Effect 0x11c55b 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x11c55b 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x11c55b 0xc8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c55e [0x4C, 0x8D, 0xA4, 0x24, 0xF0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c55e) (leaR64Effect 0x11c55e 12 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x11c55e 12 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (lea_r64_effect_step 0x11c55e 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c566 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11c566) (movR64R64Effect 0x11c566 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c566 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11c566 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c569 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x11c569) (movR64R64Effect 0x11c569 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c569 6 14).toInstrSpec (mov_r64_r64_effect_step 0x11c569 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11c56c [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x11c56c) (movR64R64Effect 0x11c56c 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11c56c 2 15).toInstrSpec (mov_r64_r64_effect_step 0x11c56c 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11c56f [0xE8, 0x4C, 0x37, 0xFF, 0xFF] (PushPre 0x11c56f 5) (callEffect (fun _ => 0x10fcc0) 0x11c574)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c56f 0x10fcc0 0x11c574).toInstrSpec (call_rel32_effect_step 0x11c56f 0xffff374c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c55e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c566) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (7, 57), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c569) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c56c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c56f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 63), (5, 5), (6, 59), (7, 57), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc0) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l11c55b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c55b :=
  Rest.liftedBlock (rest_l11c55b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c55b x hx)

theorem rest_l11c574 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c574 bytes_l11c574) (entryMap (live .l11c574))
      8 0x11c574 bytes_l11c574 b_l11c574 := by
  have f0 : InstrSpec 0x11c574 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c574) (movR32Imm32Effect 0x11c574 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11c574 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11c574 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11c579 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11c579) (movR64R64Effect 0x11c579 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c579 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11c579 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c57c [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11c57c) (movR64R64Effect 0x11c57c 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c57c 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11c57c 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c57f [0xF3, 0x48, 0xA5] (RepPre 0x11c57f (RepMovsqPre 0x11c57f)) (repMovsqEffect 0x11c57f)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11c57f).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11c57f 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11c582 [0x31, 0xFF] (fun s => s.RIP = 0x11c582) (xorR32R32Effect 0x11c582 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c582 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x11c582 0xff (by decide)) pre_rip
  have f5 : InstrSpec 0x11c584 [0x41, 0x80, 0xFD, 0x02] (fun s => s.RIP = 0x11c584) (cmpR8Imm8Effect 0x11c584 4 13 0x2)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x11c584 4 13 0x2).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x11c584 0x41 0xfd 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11c588 [0x40, 0x0F, 0x94, 0xC7] (fun s => s.RIP = 0x11c588) (atFlags (condHolds 4) (setccR8Effect 0x11c588 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x11c588 4 7 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11c588 4 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x11c58c [0xE8, 0xBF, 0xB7, 0x00, 0x00] (PushPre 0x11c58c 5) (callEffect (fun _ => 0x127d50) 0x11c591)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c58c 0x127d50 0x11c591).toInstrSpec (call_rel32_effect_step 0x11c58c 0xb7bf (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c579) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c57c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c57f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 61) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c582) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c584) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c588) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c58c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l11c574 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c574 :=
  Rest.liftedBlock (rest_l11c574 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c574 x hx)

theorem rest_l11c591 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c591 bytes_l11c591) (entryMap (live .l11c591))
      5 0x11c591 bytes_l11c591 b_l11c591 := by
  have f0 : InstrSpec 0x11c591 [0x49, 0x8D, 0x57, 0x78] (fun s => s.RIP = 0x11c591) (leaR64Effect 0x11c591 2 (.base 15 (.d8 0x78)))
      [.gpr 15] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x11c591 2 (.base 15 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x11c591 0x49 (by decide) 2 (.base 15 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c595 [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x11c595) (movzxR32R8Effect 0x11c595 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x11c595 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x11c595 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c598 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11c598) (movR64R64Effect 0x11c598 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c598 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11c598 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c59b [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x11c59b) (movR64R64Effect 0x11c59b 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c59b 6 14).toInstrSpec (mov_r64_r64_effect_step 0x11c59b 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11c59e [0xE8, 0x1D, 0x37, 0xFF, 0xFF] (PushPre 0x11c59e 5) (callEffect (fun _ => 0x10fcc0) 0x11c5a3)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c59e 0x10fcc0 0x11c5a3).toInstrSpec (call_rel32_effect_step 0x11c59e 0xffff371d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c595) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c598) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c59b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c59e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l11c591 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c591 :=
  Rest.liftedBlock (rest_l11c591 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c591 x hx)

theorem rest_l11c5a3 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c5a3 bytes_l11c5a3) (entryMap (live .l11c5a3))
      8 0x11c5a3 bytes_l11c5a3 b_l11c5a3 := by
  have f0 : InstrSpec 0x11c5a3 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c5a3) (movR32Imm32Effect 0x11c5a3 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11c5a3 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11c5a3 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11c5a8 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11c5a8) (movR64R64Effect 0x11c5a8 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c5a8 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11c5a8 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c5ab [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11c5ab) (movR64R64Effect 0x11c5ab 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c5ab 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11c5ab 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c5ae [0xF3, 0x48, 0xA5] (RepPre 0x11c5ae (RepMovsqPre 0x11c5ae)) (repMovsqEffect 0x11c5ae)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11c5ae).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11c5ae 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11c5b1 [0x31, 0xFF] (fun s => s.RIP = 0x11c5b1) (xorR32R32Effect 0x11c5b1 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c5b1 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x11c5b1 0xff (by decide)) pre_rip
  have f5 : InstrSpec 0x11c5b3 [0x41, 0x80, 0xFD, 0x03] (fun s => s.RIP = 0x11c5b3) (cmpR8Imm8Effect 0x11c5b3 4 13 0x3)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x11c5b3 4 13 0x3).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x11c5b3 0x41 0xfd 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11c5b7 [0x40, 0x0F, 0x94, 0xC7] (fun s => s.RIP = 0x11c5b7) (atFlags (condHolds 4) (setccR8Effect 0x11c5b7 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x11c5b7 4 7 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11c5b7 4 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x11c5bb [0xE8, 0x90, 0xB7, 0x00, 0x00] (PushPre 0x11c5bb 5) (callEffect (fun _ => 0x127d50) 0x11c5c0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c5bb 0x127d50 0x11c5c0).toInstrSpec (call_rel32_effect_step 0x11c5bb 0xb790 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5a8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5ab) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5ae) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 61) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5b1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5b3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5b7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5bb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l11c5a3 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c5a3 :=
  Rest.liftedBlock (rest_l11c5a3 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c5a3 x hx)

theorem rest_l11c5c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c5c0 bytes_l11c5c0) (entryMap (live .l11c5c0))
      5 0x11c5c0 bytes_l11c5c0 b_l11c5c0 := by
  have f0 : InstrSpec 0x11c5c0 [0x49, 0x8D, 0x97, 0xF0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c5c0) (leaR64Effect 0x11c5c0 2 (.base 15 (.d32 0xf0)))
      [.gpr 15] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x11c5c0 2 (.base 15 (.d32 0xf0))).toInstrSpec (lea_r64_effect_step 0x11c5c0 0x49 (by decide) 2 (.base 15 (.d32 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c5c7 [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x11c5c7) (movzxR32R8Effect 0x11c5c7 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x11c5c7 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x11c5c7 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c5ca [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11c5ca) (movR64R64Effect 0x11c5ca 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c5ca 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11c5ca 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c5cd [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x11c5cd) (movR64R64Effect 0x11c5cd 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c5cd 6 14).toInstrSpec (mov_r64_r64_effect_step 0x11c5cd 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11c5d0 [0xE8, 0xEB, 0x36, 0xFF, 0xFF] (PushPre 0x11c5d0 5) (callEffect (fun _ => 0x10fcc0) 0x11c5d5)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c5d0 0x10fcc0 0x11c5d5).toInstrSpec (call_rel32_effect_step 0x11c5d0 0xffff36eb (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5c7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5ca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5cd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5d0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l11c5c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c5c0 :=
  Rest.liftedBlock (rest_l11c5c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c5c0 x hx)

theorem rest_l11c5d5 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c5d5 bytes_l11c5d5) (entryMap (live .l11c5d5))
      8 0x11c5d5 bytes_l11c5d5 b_l11c5d5 := by
  have f0 : InstrSpec 0x11c5d5 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c5d5) (movR32Imm32Effect 0x11c5d5 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11c5d5 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11c5d5 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11c5da [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11c5da) (movR64R64Effect 0x11c5da 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c5da 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11c5da 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c5dd [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11c5dd) (movR64R64Effect 0x11c5dd 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c5dd 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11c5dd 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c5e0 [0xF3, 0x48, 0xA5] (RepPre 0x11c5e0 (RepMovsqPre 0x11c5e0)) (repMovsqEffect 0x11c5e0)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11c5e0).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11c5e0 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11c5e3 [0x31, 0xFF] (fun s => s.RIP = 0x11c5e3) (xorR32R32Effect 0x11c5e3 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c5e3 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x11c5e3 0xff (by decide)) pre_rip
  have f5 : InstrSpec 0x11c5e5 [0x41, 0x80, 0xFD, 0x04] (fun s => s.RIP = 0x11c5e5) (cmpR8Imm8Effect 0x11c5e5 4 13 0x4)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x11c5e5 4 13 0x4).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x11c5e5 0x41 0xfd 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11c5e9 [0x40, 0x0F, 0x94, 0xC7] (fun s => s.RIP = 0x11c5e9) (atFlags (condHolds 4) (setccR8Effect 0x11c5e9 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x11c5e9 4 7 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11c5e9 4 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x11c5ed [0xE8, 0x5E, 0xB7, 0x00, 0x00] (PushPre 0x11c5ed 5) (callEffect (fun _ => 0x127d50) 0x11c5f2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c5ed 0x127d50 0x11c5f2).toInstrSpec (call_rel32_effect_step 0x11c5ed 0xb75e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5da) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5dd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5e0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 61) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5e3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5e5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5e9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5ed) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l11c5d5 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c5d5 :=
  Rest.liftedBlock (rest_l11c5d5 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c5d5 x hx)

theorem rest_l11c5f2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c5f2 bytes_l11c5f2) (entryMap (live .l11c5f2))
      5 0x11c5f2 bytes_l11c5f2 b_l11c5f2 := by
  have f0 : InstrSpec 0x11c5f2 [0x49, 0x8D, 0x97, 0x68, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11c5f2) (leaR64Effect 0x11c5f2 2 (.base 15 (.d32 0x168)))
      [.gpr 15] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x11c5f2 2 (.base 15 (.d32 0x168))).toInstrSpec (lea_r64_effect_step 0x11c5f2 0x49 (by decide) 2 (.base 15 (.d32 0x168)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c5f9 [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x11c5f9) (movzxR32R8Effect 0x11c5f9 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x11c5f9 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x11c5f9 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c5fc [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11c5fc) (movR64R64Effect 0x11c5fc 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c5fc 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11c5fc 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c5ff [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x11c5ff) (movR64R64Effect 0x11c5ff 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c5ff 6 14).toInstrSpec (mov_r64_r64_effect_step 0x11c5ff 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11c602 [0xE8, 0xB9, 0x36, 0xFF, 0xFF] (PushPre 0x11c602 5) (callEffect (fun _ => 0x10fcc0) 0x11c607)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c602 0x10fcc0 0x11c607).toInstrSpec (call_rel32_effect_step 0x11c602 0xffff36b9 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5f9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5fc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c5ff) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c602) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l11c5f2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c5f2 :=
  Rest.liftedBlock (rest_l11c5f2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c5f2 x hx)

theorem rest_l11c607 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c607 bytes_l11c607) (entryMap (live .l11c607))
      8 0x11c607 bytes_l11c607 b_l11c607 := by
  have f0 : InstrSpec 0x11c607 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c607) (movR32Imm32Effect 0x11c607 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11c607 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11c607 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11c60c [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11c60c) (movR64R64Effect 0x11c60c 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c60c 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11c60c 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c60f [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11c60f) (movR64R64Effect 0x11c60f 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c60f 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11c60f 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c612 [0xF3, 0x48, 0xA5] (RepPre 0x11c612 (RepMovsqPre 0x11c612)) (repMovsqEffect 0x11c612)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11c612).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11c612 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11c615 [0x31, 0xFF] (fun s => s.RIP = 0x11c615) (xorR32R32Effect 0x11c615 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c615 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x11c615 0xff (by decide)) pre_rip
  have f5 : InstrSpec 0x11c617 [0x41, 0x80, 0xFD, 0x05] (fun s => s.RIP = 0x11c617) (cmpR8Imm8Effect 0x11c617 4 13 0x5)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x11c617 4 13 0x5).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x11c617 0x41 0xfd 0x5 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11c61b [0x40, 0x0F, 0x94, 0xC7] (fun s => s.RIP = 0x11c61b) (atFlags (condHolds 4) (setccR8Effect 0x11c61b 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x11c61b 4 7 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11c61b 4 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x11c61f [0xE8, 0x2C, 0xB7, 0x00, 0x00] (PushPre 0x11c61f 5) (callEffect (fun _ => 0x127d50) 0x11c624)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c61f 0x127d50 0x11c624).toInstrSpec (call_rel32_effect_step 0x11c61f 0xb72c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c60c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c60f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c612) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 61) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c615) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c617) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c61b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c61f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l11c607 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c607 :=
  Rest.liftedBlock (rest_l11c607 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c607 x hx)

theorem rest_l11c624 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c624 bytes_l11c624) (entryMap (live .l11c624))
      5 0x11c624 bytes_l11c624 b_l11c624 := by
  have f0 : InstrSpec 0x11c624 [0x49, 0x8D, 0x97, 0xE0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11c624) (leaR64Effect 0x11c624 2 (.base 15 (.d32 0x1e0)))
      [.gpr 15] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x11c624 2 (.base 15 (.d32 0x1e0))).toInstrSpec (lea_r64_effect_step 0x11c624 0x49 (by decide) 2 (.base 15 (.d32 0x1e0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c62b [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x11c62b) (movzxR32R8Effect 0x11c62b 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x11c62b 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x11c62b 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c62e [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11c62e) (movR64R64Effect 0x11c62e 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c62e 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11c62e 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c631 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x11c631) (movR64R64Effect 0x11c631 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c631 6 14).toInstrSpec (mov_r64_r64_effect_step 0x11c631 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11c634 [0xE8, 0x87, 0x36, 0xFF, 0xFF] (PushPre 0x11c634 5) (callEffect (fun _ => 0x10fcc0) 0x11c639)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c634 0x10fcc0 0x11c639).toInstrSpec (call_rel32_effect_step 0x11c634 0xffff3687 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c62b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c62e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c631) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c634) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l11c624 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c624 :=
  Rest.liftedBlock (rest_l11c624 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c624 x hx)

theorem rest_l11c639 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c639 bytes_l11c639) (entryMap (live .l11c639))
      8 0x11c639 bytes_l11c639 b_l11c639 := by
  have f0 : InstrSpec 0x11c639 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c639) (movR32Imm32Effect 0x11c639 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11c639 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11c639 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11c63e [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11c63e) (movR64R64Effect 0x11c63e 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c63e 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11c63e 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c641 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11c641) (movR64R64Effect 0x11c641 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c641 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11c641 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c644 [0xF3, 0x48, 0xA5] (RepPre 0x11c644 (RepMovsqPre 0x11c644)) (repMovsqEffect 0x11c644)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11c644).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11c644 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11c647 [0x31, 0xFF] (fun s => s.RIP = 0x11c647) (xorR32R32Effect 0x11c647 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c647 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x11c647 0xff (by decide)) pre_rip
  have f5 : InstrSpec 0x11c649 [0x41, 0x80, 0xFD, 0x06] (fun s => s.RIP = 0x11c649) (cmpR8Imm8Effect 0x11c649 4 13 0x6)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x11c649 4 13 0x6).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x11c649 0x41 0xfd 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11c64d [0x40, 0x0F, 0x94, 0xC7] (fun s => s.RIP = 0x11c64d) (atFlags (condHolds 4) (setccR8Effect 0x11c64d 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x11c64d 4 7 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11c64d 4 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x11c651 [0xE8, 0xFA, 0xB6, 0x00, 0x00] (PushPre 0x11c651 5) (callEffect (fun _ => 0x127d50) 0x11c656)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c651 0x127d50 0x11c656).toInstrSpec (call_rel32_effect_step 0x11c651 0xb6fa (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c63e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c641) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c644) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 61) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c647) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c649) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c64d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c651) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l11c639 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c639 :=
  Rest.liftedBlock (rest_l11c639 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c639 x hx)

theorem rest_l11c656 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c656 bytes_l11c656) (entryMap (live .l11c656))
      5 0x11c656 bytes_l11c656 b_l11c656 := by
  have f0 : InstrSpec 0x11c656 [0x49, 0x8D, 0x97, 0x58, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x11c656) (leaR64Effect 0x11c656 2 (.base 15 (.d32 0x258)))
      [.gpr 15] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x11c656 2 (.base 15 (.d32 0x258))).toInstrSpec (lea_r64_effect_step 0x11c656 0x49 (by decide) 2 (.base 15 (.d32 0x258)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c65d [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x11c65d) (movzxR32R8Effect 0x11c65d 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x11c65d 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x11c65d 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c660 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11c660) (movR64R64Effect 0x11c660 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c660 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11c660 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c663 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x11c663) (movR64R64Effect 0x11c663 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c663 6 14).toInstrSpec (mov_r64_r64_effect_step 0x11c663 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11c666 [0xE8, 0x55, 0x36, 0xFF, 0xFF] (PushPre 0x11c666 5) (callEffect (fun _ => 0x10fcc0) 0x11c66b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c666 0x10fcc0 0x11c66b).toInstrSpec (call_rel32_effect_step 0x11c666 0xffff3655 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c65d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c660) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c663) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c666) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l11c656 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c656 :=
  Rest.liftedBlock (rest_l11c656 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c656 x hx)

theorem rest_l11c66b [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c66b bytes_l11c66b) (entryMap (live .l11c66b))
      8 0x11c66b bytes_l11c66b b_l11c66b := by
  have f0 : InstrSpec 0x11c66b [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c66b) (movR32Imm32Effect 0x11c66b 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11c66b 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11c66b 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11c670 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11c670) (movR64R64Effect 0x11c670 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c670 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11c670 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c673 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11c673) (movR64R64Effect 0x11c673 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c673 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11c673 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c676 [0xF3, 0x48, 0xA5] (RepPre 0x11c676 (RepMovsqPre 0x11c676)) (repMovsqEffect 0x11c676)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11c676).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11c676 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11c679 [0x31, 0xFF] (fun s => s.RIP = 0x11c679) (xorR32R32Effect 0x11c679 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c679 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x11c679 0xff (by decide)) pre_rip
  have f5 : InstrSpec 0x11c67b [0x41, 0x80, 0xFD, 0x07] (fun s => s.RIP = 0x11c67b) (cmpR8Imm8Effect 0x11c67b 4 13 0x7)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x11c67b 4 13 0x7).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x11c67b 0x41 0xfd 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11c67f [0x40, 0x0F, 0x94, 0xC7] (fun s => s.RIP = 0x11c67f) (atFlags (condHolds 4) (setccR8Effect 0x11c67f 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x11c67f 4 7 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11c67f 4 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x11c683 [0xE8, 0xC8, 0xB6, 0x00, 0x00] (PushPre 0x11c683 5) (callEffect (fun _ => 0x127d50) 0x11c688)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c683 0x127d50 0x11c688).toInstrSpec (call_rel32_effect_step 0x11c683 0xb6c8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c670) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c673) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c676) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 61) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c679) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c67b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c67f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c683) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l11c66b [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c66b :=
  Rest.liftedBlock (rest_l11c66b hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c66b x hx)

theorem rest_l11c688 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c688 bytes_l11c688) (entryMap (live .l11c688))
      5 0x11c688 bytes_l11c688 b_l11c688 := by
  have f0 : InstrSpec 0x11c688 [0x49, 0x8D, 0x97, 0xD0, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x11c688) (leaR64Effect 0x11c688 2 (.base 15 (.d32 0x2d0)))
      [.gpr 15] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x11c688 2 (.base 15 (.d32 0x2d0))).toInstrSpec (lea_r64_effect_step 0x11c688 0x49 (by decide) 2 (.base 15 (.d32 0x2d0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c68f [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x11c68f) (movzxR32R8Effect 0x11c68f 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x11c68f 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x11c68f 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c692 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11c692) (movR64R64Effect 0x11c692 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c692 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11c692 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c695 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x11c695) (movR64R64Effect 0x11c695 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c695 6 14).toInstrSpec (mov_r64_r64_effect_step 0x11c695 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11c698 [0xE8, 0x23, 0x36, 0xFF, 0xFF] (PushPre 0x11c698 5) (callEffect (fun _ => 0x10fcc0) 0x11c69d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c698 0x10fcc0 0x11c69d).toInstrSpec (call_rel32_effect_step 0x11c698 0xffff3623 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c68f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c692) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c695) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c698) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc0) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l11c688 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c688 :=
  Rest.liftedBlock (rest_l11c688 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c688 x hx)

theorem rest_l11c69d [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c69d bytes_l11c69d) (entryMap (live .l11c69d))
      8 0x11c69d bytes_l11c69d b_l11c69d := by
  have f0 : InstrSpec 0x11c69d [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c69d) (movR32Imm32Effect 0x11c69d 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11c69d 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11c69d 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11c6a2 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11c6a2) (movR64R64Effect 0x11c6a2 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c6a2 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11c6a2 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c6a5 [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11c6a5) (movR64R64Effect 0x11c6a5 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c6a5 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11c6a5 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c6a8 [0xF3, 0x48, 0xA5] (RepPre 0x11c6a8 (RepMovsqPre 0x11c6a8)) (repMovsqEffect 0x11c6a8)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11c6a8).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11c6a8 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11c6ab [0x31, 0xFF] (fun s => s.RIP = 0x11c6ab) (xorR32R32Effect 0x11c6ab 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c6ab 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x11c6ab 0xff (by decide)) pre_rip
  have f5 : InstrSpec 0x11c6ad [0x41, 0x80, 0xFD, 0x08] (fun s => s.RIP = 0x11c6ad) (cmpR8Imm8Effect 0x11c6ad 4 13 0x8)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x11c6ad 4 13 0x8).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x11c6ad 0x41 0xfd 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11c6b1 [0x40, 0x0F, 0x94, 0xC7] (fun s => s.RIP = 0x11c6b1) (atFlags (condHolds 4) (setccR8Effect 0x11c6b1 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x11c6b1 4 7 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11c6b1 4 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x11c6b5 [0xE8, 0x96, 0xB6, 0x00, 0x00] (PushPre 0x11c6b5 5) (callEffect (fun _ => 0x127d50) 0x11c6ba)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c6b5 0x127d50 0x11c6ba).toInstrSpec (call_rel32_effect_step 0x11c6b5 0xb696 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6a2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6a5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6a8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 61) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6ab) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6ad) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6b1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6b5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l11c69d [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c69d :=
  Rest.liftedBlock (rest_l11c69d hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c69d x hx)

theorem rest_l11c6ba [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c6ba bytes_l11c6ba) (entryMap (live .l11c6ba))
      6 0x11c6ba bytes_l11c6ba b_l11c6ba := by
  have f0 : InstrSpec 0x11c6ba [0x49, 0x81, 0xC7, 0x48, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x11c6ba) (addR64Imm32Effect 0x11c6ba 15 0x348)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x11c6ba 15 0x348).toInstrSpec (add_r64_imm32_effect_step 0x11c6ba 0x49 0xc7 0x348 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c6c1 [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x11c6c1) (movzxR32R8Effect 0x11c6c1 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x11c6c1 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x11c6c1 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c6c4 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x11c6c4) (movR64R64Effect 0x11c6c4 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c6c4 7 12).toInstrSpec (mov_r64_r64_effect_step 0x11c6c4 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c6c7 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x11c6c7) (movR64R64Effect 0x11c6c7 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c6c7 6 14).toInstrSpec (mov_r64_r64_effect_step 0x11c6c7 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11c6ca [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x11c6ca) (movR64R64Effect 0x11c6ca 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11c6ca 2 15).toInstrSpec (mov_r64_r64_effect_step 0x11c6ca 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11c6cd [0xE8, 0xEE, 0x35, 0xFF, 0xFF] (PushPre 0x11c6cd 5) (callEffect (fun _ => 0x10fcc0) 0x11c6d2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c6cd 0x10fcc0 0x11c6d2).toInstrSpec (call_rel32_effect_step 0x11c6cd 0xffff35ee (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6c4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (7, 57), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6c7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6ca) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6cd) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 63), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc0) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l11c6ba [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c6ba :=
  Rest.liftedBlock (rest_l11c6ba code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c6ba x hx)

theorem rest_l11c6d2 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c6d2 bytes_l11c6d2) (entryMap (live .l11c6d2))
      7 0x11c6d2 bytes_l11c6d2 b_l11c6d2 := by
  have f0 : InstrSpec 0x11c6d2 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c6d2) (movR32Imm32Effect 0x11c6d2 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11c6d2 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11c6d2 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11c6d7 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11c6d7) (movR64R64Effect 0x11c6d7 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c6d7 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11c6d7 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c6da [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x11c6da) (movR64R64Effect 0x11c6da 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c6da 6 12).toInstrSpec (mov_r64_r64_effect_step 0x11c6da 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c6dd [0xF3, 0x48, 0xA5] (RepPre 0x11c6dd (RepMovsqPre 0x11c6dd)) (repMovsqEffect 0x11c6dd)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11c6dd).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11c6dd 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11c6e0 [0x40, 0xC0, 0xED, 0x07] (fun s => s.RIP = 0x11c6e0) (shrR8Effect 0x11c6e0 4 5 7)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR8Effect_footprint 0x11c6e0 4 5 7).toInstrSpec (shr_r8_imm8_rex_effect_step 0x11c6e0 0x40 0xed 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11c6e4 [0x40, 0x0F, 0xB6, 0xFD] (fun s => s.RIP = 0x11c6e4) (movzxR32R8Effect 0x11c6e4 4 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x11c6e4 4 7 5).toInstrSpec (movzx_r32_r8_rex_effect_step 0x11c6e4 0x40 (by decide) 0xfd (by decide)) pre_rip
  have f6 : InstrSpec 0x11c6e8 [0xE8, 0x63, 0xB6, 0x00, 0x00] (PushPre 0x11c6e8 5) (callEffect (fun _ => 0x127d50) 0x11c6ed)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c6e8 0x127d50 0x11c6ed).toInstrSpec (call_rel32_effect_step 0x11c6e8 0xb663 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6d7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6da) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6dd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6e0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 60), (2, 2), (3, 3), (4, 4), (5, 62), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6e4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 60), (2, 2), (3, 3), (4, 4), (5, 62), (6, 59), (7, 64), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6e8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 60), (2, 2), (3, 3), (4, 66), (5, 62), (6, 59), (7, 64), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l11c6d2 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c6d2 :=
  Rest.liftedBlock (rest_l11c6d2 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c6d2 x hx)

theorem rest_l11c6ed_3 [Bindings] (code : CodeMap) :
    Rest (n := 158) code lifted (codeRange 0x11c6ed bytes_l11c6ed) [(0, 0), (1, 150), (2, 154), (3, 3), (4, 4), (5, 5), (6, 131), (7, 156), (8, 113), (9, 135), (10, 143), (12, 12), (13, 13), (14, 14), (15, 152), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x11c83d bytes_l11c6ed_3 b_l11c6ed_3 := by
  have f60 : InstrSpec 0x11c83d [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x11c83d) (movR64R64Effect 0x11c83d 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c83d 6 14).toInstrSpec (mov_r64_r64_effect_step 0x11c83d 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x11c840 [0xE8, 0x7B, 0x34, 0xFF, 0xFF] (PushPre 0x11c840 5) (callEffect (fun _ => 0x10fcc0) 0x11c845)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11c840 0x10fcc0 0x11c845).toInstrSpec (call_rel32_effect_step 0x11c840 0xffff347b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f60 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 0), (1, 150), (2, 154), (3, 3), (4, 4), (5, 5), (6, 158), (7, 156), (8, 113), (9, 135), (10, 143), (12, 12), (13, 13), (14, 14), (15, 152), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c840) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f61 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 0), (1, 150), (2, 154), (3, 3), (4, 160), (5, 5), (6, 158), (7, 156), (8, 113), (9, 135), (10, 143), (12, 12), (13, 13), (14, 14), (15, 152), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcc0) f61 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 162) (by decide) (by decide) rfl rfl

theorem rest_l11c6ed_2 [Bindings] (code : CodeMap) :
    Rest (n := 123) code lifted (codeRange 0x11c6ed bytes_l11c6ed) [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 111), (7, 109), (8, 113), (9, 121), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]
      22 0x11c7dd bytes_l11c6ed_2 b_l11c6ed_2 := by
  have f40 : InstrSpec 0x11c7dd [0x49, 0x01, 0xF9] (fun s => s.RIP = 0x11c7dd) (addR64R64Effect 0x11c7dd 9 7)
      [.gpr 9, .gpr 7] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11c7dd 9 7).toInstrSpec (add_r64_r64_effect_step 0x11c7dd 0x49 0xf9 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x11c7e0 [0x4D, 0x89, 0xCA] (fun s => s.RIP = 0x11c7e0) (movR64R64Effect 0x11c7e0 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x11c7e0 10 9).toInstrSpec (mov_r64_r64_effect_step 0x11c7e0 0x4d 0xca (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x11c7e3 [0x49, 0xC1, 0xEA, 0x34] (fun s => s.RIP = 0x11c7e3) (shrR64Effect 0x11c7e3 4 10 52)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x11c7e3 4 10 52).toInstrSpec (shr_r64_imm8_effect_step 0x11c7e3 0x49 0xea 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x11c7e7 [0x4C, 0x2B, 0x54, 0x24, 0x40] (LoadPre 0x11c7e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11c7e7 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11c7e7 10 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 10, .gpr 4] [] [.reg 10, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11c7e7 10 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (sub_r64_m64_effect_step 0x11c7e7 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f44 : InstrSpec 0x11c7ec [0x4C, 0x21, 0xC6] (fun s => s.RIP = 0x11c7ec) (andR64R64Effect 0x11c7ec 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11c7ec 6 8).toInstrSpec (and_r64_r64_effect_step 0x11c7ec 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x11c7ef [0x49, 0x01, 0xFA] (fun s => s.RIP = 0x11c7ef) (addR64R64Effect 0x11c7ef 10 7)
      [.gpr 10, .gpr 7] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11c7ef 10 7).toInstrSpec (add_r64_r64_effect_step 0x11c7ef 0x49 0xfa (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x11c7f2 [0x4D, 0x21, 0xC1] (fun s => s.RIP = 0x11c7f2) (andR64R64Effect 0x11c7f2 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11c7f2 9 8).toInstrSpec (and_r64_r64_effect_step 0x11c7f2 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x11c7f5 [0x4C, 0x89, 0xD7] (fun s => s.RIP = 0x11c7f5) (movR64R64Effect 0x11c7f5 7 10)
      [.gpr 10] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c7f5 7 10).toInstrSpec (mov_r64_r64_effect_step 0x11c7f5 0x4c 0xd7 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x11c7f8 [0x48, 0xC1, 0xEF, 0x34] (fun s => s.RIP = 0x11c7f8) (shrR64Effect 0x11c7f8 4 7 52)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x11c7f8 4 7 52).toInstrSpec (shr_r64_imm8_effect_step 0x11c7f8 0x48 0xef 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x11c7fc [0x48, 0x01, 0xCF] (fun s => s.RIP = 0x11c7fc) (addR64R64Effect 0x11c7fc 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11c7fc 7 1).toInstrSpec (add_r64_r64_effect_step 0x11c7fc 0x48 0xcf (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x11c7ff [0x4D, 0x21, 0xC2] (fun s => s.RIP = 0x11c7ff) (andR64R64Effect 0x11c7ff 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11c7ff 10 8).toInstrSpec (and_r64_r64_effect_step 0x11c7ff 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x11c802 [0x48, 0x89, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x11c802 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11c802 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c802 2 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c802 2 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x11c802 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x11c80a [0x48, 0x89, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x11c80a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11c80a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c80a 6 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c80a 6 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x11c80a 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f53 : InstrSpec 0x11c812 [0x4C, 0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x11c812 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11c812 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c812 9 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c812 9 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x11c812 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x11c81a [0x4C, 0x89, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x11c81a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11c81a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c81a 10 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c81a 10 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x11c81a 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f55 : InstrSpec 0x11c822 [0x48, 0x89, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x11c822 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11c822 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c822 7 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c822 7 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x11c822 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x11c82a [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x11c82a) (movzxR32R8Effect 0x11c82a 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x11c82a 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x11c82a 0xc8 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x11c82d [0x4C, 0x8D, 0xBC, 0x24, 0xF0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c82d) (leaR64Effect 0x11c82d 15 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x11c82d 15 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (lea_r64_effect_step 0x11c82d 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x11c835 [0x48, 0x8D, 0x54, 0x24, 0x78] (fun s => s.RIP = 0x11c835) (leaR64Effect 0x11c835 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x11c835 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x11c835 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x11c83a [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x11c83a) (movR64R64Effect 0x11c83a 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c83a 7 15).toInstrSpec (mov_r64_r64_effect_step 0x11c83a 0x4c 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f40 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 111), (7, 109), (8, 113), (9, 123), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7e0) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f41 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 111), (7, 109), (8, 113), (9, 123), (10, 125), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7e3) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f42 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 111), (7, 109), (8, 113), (9, 123), (10, 127), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7e7) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f43 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 111), (7, 109), (8, 113), (9, 123), (10, 129), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7ec) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f44 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 131), (7, 109), (8, 113), (9, 123), (10, 129), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7ef) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f45 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 131), (7, 109), (8, 113), (9, 123), (10, 133), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7f2) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f46 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 131), (7, 109), (8, 113), (9, 135), (10, 133), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7f5) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f47 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 131), (7, 137), (8, 113), (9, 135), (10, 133), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7f8) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f48 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 131), (7, 139), (8, 113), (9, 135), (10, 133), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7fc) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f49 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 131), (7, 141), (8, 113), (9, 135), (10, 133), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7ff) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f50 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 131), (7, 141), (8, 113), (9, 135), (10, 143), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c802) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.exec (n := 145) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 131), (7, 141), (8, 113), (9, 135), (10, 143), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c80a) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 146) (RestInside.exec (n := 146) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 131), (7, 141), (8, 113), (9, 135), (10, 143), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c812) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 147) (RestInside.exec (n := 147) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 131), (7, 141), (8, 113), (9, 135), (10, 143), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c81a) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 148) (RestInside.exec (n := 148) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 131), (7, 141), (8, 113), (9, 135), (10, 143), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c822) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 149) (RestInside.exec (n := 149) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 131), (7, 141), (8, 113), (9, 135), (10, 143), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c82a) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f56 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 0), (1, 150), (2, 115), (3, 3), (4, 4), (5, 5), (6, 131), (7, 141), (8, 113), (9, 135), (10, 143), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c82d) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f57 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 0), (1, 150), (2, 115), (3, 3), (4, 4), (5, 5), (6, 131), (7, 141), (8, 113), (9, 135), (10, 143), (12, 12), (13, 13), (14, 14), (15, 152), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c835) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f58 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 0), (1, 150), (2, 154), (3, 3), (4, 4), (5, 5), (6, 131), (7, 141), (8, 113), (9, 135), (10, 143), (12, 12), (13, 13), (14, 14), (15, 152), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c83a) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f59 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 0), (1, 150), (2, 154), (3, 3), (4, 4), (5, 5), (6, 131), (7, 156), (8, 113), (9, 135), (10, 143), (12, 12), (13, 13), (14, 14), (15, 152), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c83d) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11c6ed_3 code

theorem rest_l11c6ed_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x11c6ed bytes_l11c6ed) [(0, 0), (1, 77), (2, 80), (3, 3), (4, 4), (5, 5), (6, 82), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]
      42 0x11c76d bytes_l11c6ed_1 b_l11c6ed_1 := by
  have f20 : InstrSpec 0x11c76d [0x48, 0x2B, 0x74, 0x24, 0x48] (LoadPre 0x11c76d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11c76d + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11c76d 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11c76d 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (sub_r64_m64_effect_step 0x11c76d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x11c772 [0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x11c772) (movR64Imm64Effect 0x11c772 1 0xffffffffffff)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x11c772 1 0xffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x11c772 0x48 0xb9 (by decide) (by decide) 0xffffffffffff) pre_rip
  have f22 : InstrSpec 0x11c77c [0x48, 0x21, 0xF1] (fun s => s.RIP = 0x11c77c) (andR64R64Effect 0x11c77c 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11c77c 1 6).toInstrSpec (and_r64_r64_effect_step 0x11c77c 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x11c77f [0x48, 0xC1, 0xEE, 0x30] (fun s => s.RIP = 0x11c77f) (shrR64Effect 0x11c77f 4 6 48)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x11c77f 4 6 48).toInstrSpec (shr_r64_imm8_effect_step 0x11c77f 0x48 0xee 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x11c783 [0x48, 0xBF, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c783) (movR64Imm64Effect 0x11c783 7 0x1000003d1)
      [] [] [.reg 7, .rip] :=
    (movR64Imm64Effect_footprint 0x11c783 7 0x1000003d1).toInstrSpec (mov_r64_imm64_effect_step 0x11c783 0x48 0xbf (by decide) (by decide) 0x1000003d1) pre_rip
  have f25 : InstrSpec 0x11c78d [0x48, 0x0F, 0xAF, 0xFE] (fun s => s.RIP = 0x11c78d) (imulR64R64Effect 0x11c78d 4 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x11c78d 4 7 6).toInstrSpec (imul_r64_r64_effect_step 0x11c78d 0x48 (by decide) 0xfe (by decide)) pre_rip
  have f26 : InstrSpec 0x11c791 [0x48, 0x2B, 0x7C, 0x24, 0x28] (LoadPre 0x11c791 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11c791 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11c791 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 7, .gpr 4] [] [.reg 7, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11c791 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (sub_r64_m64_effect_step 0x11c791 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x11c796 [0x48, 0x89, 0x94, 0x24, 0xE8, 0x00, 0x00, 0x00] (StorePre 0x11c796 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11c796 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c796 2 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c796 2 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x11c796 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x11c79e [0x48, 0xBA, 0xBC, 0xF0, 0xFF, 0xFF, 0xFB, 0xFF, 0x3F, 0x00] (fun s => s.RIP = 0x11c79e) (movR64Imm64Effect 0x11c79e 2 0x3ffffbfffff0bc)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x11c79e 2 0x3ffffbfffff0bc).toInstrSpec (mov_r64_imm64_effect_step 0x11c79e 0x48 0xba (by decide) (by decide) 0x3ffffbfffff0bc) pre_rip
  have f29 : InstrSpec 0x11c7a8 [0x48, 0x01, 0xFA] (fun s => s.RIP = 0x11c7a8) (addR64R64Effect 0x11c7a8 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11c7a8 2 7).toInstrSpec (add_r64_r64_effect_step 0x11c7a8 0x48 0xfa (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x11c7ab [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x11c7ab) (movR64R64Effect 0x11c7ab 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c7ab 6 2).toInstrSpec (mov_r64_r64_effect_step 0x11c7ab 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x11c7ae [0x48, 0xC1, 0xEE, 0x34] (fun s => s.RIP = 0x11c7ae) (shrR64Effect 0x11c7ae 4 6 52)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x11c7ae 4 6 52).toInstrSpec (shr_r64_imm8_effect_step 0x11c7ae 0x48 0xee 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x11c7b2 [0x48, 0x2B, 0x74, 0x24, 0x30] (LoadPre 0x11c7b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11c7b2 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11c7b2 6 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11c7b2 6 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (sub_r64_m64_effect_step 0x11c7b2 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x11c7b7 [0x48, 0xBF, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00] (fun s => s.RIP = 0x11c7b7) (movR64Imm64Effect 0x11c7b7 7 0x3ffffffffffffc)
      [] [] [.reg 7, .rip] :=
    (movR64Imm64Effect_footprint 0x11c7b7 7 0x3ffffffffffffc).toInstrSpec (mov_r64_imm64_effect_step 0x11c7b7 0x48 0xbf (by decide) (by decide) 0x3ffffffffffffc) pre_rip
  have f34 : InstrSpec 0x11c7c1 [0x48, 0x01, 0xFE] (fun s => s.RIP = 0x11c7c1) (addR64R64Effect 0x11c7c1 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11c7c1 6 7).toInstrSpec (add_r64_r64_effect_step 0x11c7c1 0x48 0xfe (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x11c7c4 [0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x11c7c4) (movR64Imm64Effect 0x11c7c4 8 0xfffffffffffff)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x11c7c4 8 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x11c7c4 0x49 0xb8 (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f36 : InstrSpec 0x11c7ce [0x4C, 0x21, 0xC2] (fun s => s.RIP = 0x11c7ce) (andR64R64Effect 0x11c7ce 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11c7ce 2 8).toInstrSpec (and_r64_r64_effect_step 0x11c7ce 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x11c7d1 [0x49, 0x89, 0xF1] (fun s => s.RIP = 0x11c7d1) (movR64R64Effect 0x11c7d1 9 6)
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x11c7d1 9 6).toInstrSpec (mov_r64_r64_effect_step 0x11c7d1 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x11c7d4 [0x49, 0xC1, 0xE9, 0x34] (fun s => s.RIP = 0x11c7d4) (shrR64Effect 0x11c7d4 4 9 52)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x11c7d4 4 9 52).toInstrSpec (shr_r64_imm8_effect_step 0x11c7d4 0x49 0xe9 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x11c7d8 [0x4C, 0x2B, 0x4C, 0x24, 0x38] (LoadPre 0x11c7d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11c7d8 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11c7d8 9 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 9, .gpr 4] [] [.reg 9, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11c7d8 9 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (sub_r64_m64_effect_step 0x11c7d8 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 77), (2, 80), (3, 3), (4, 4), (5, 5), (6, 84), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c772) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 86), (2, 80), (3, 3), (4, 4), (5, 5), (6, 84), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c77c) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 88), (2, 80), (3, 3), (4, 4), (5, 5), (6, 84), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c77f) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 88), (2, 80), (3, 3), (4, 4), (5, 5), (6, 90), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c783) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f24 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 0), (1, 88), (2, 80), (3, 3), (4, 4), (5, 5), (6, 90), (7, 92), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c78d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f25 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 0), (1, 88), (2, 80), (3, 3), (4, 4), (5, 5), (6, 90), (7, 94), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c791) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f26 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 0), (1, 88), (2, 80), (3, 3), (4, 4), (5, 5), (6, 90), (7, 96), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c796) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 0), (1, 88), (2, 80), (3, 3), (4, 4), (5, 5), (6, 90), (7, 96), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c79e) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 0), (1, 88), (2, 99), (3, 3), (4, 4), (5, 5), (6, 90), (7, 96), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7a8) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f29 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 0), (1, 88), (2, 101), (3, 3), (4, 4), (5, 5), (6, 90), (7, 96), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7ab) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f30 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 0), (1, 88), (2, 101), (3, 3), (4, 4), (5, 5), (6, 103), (7, 96), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7ae) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f31 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 0), (1, 88), (2, 101), (3, 3), (4, 4), (5, 5), (6, 105), (7, 96), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7b2) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f32 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 0), (1, 88), (2, 101), (3, 3), (4, 4), (5, 5), (6, 107), (7, 96), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7b7) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f33 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 0), (1, 88), (2, 101), (3, 3), (4, 4), (5, 5), (6, 107), (7, 109), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7c1) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f34 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 0), (1, 88), (2, 101), (3, 3), (4, 4), (5, 5), (6, 111), (7, 109), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7c4) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f35 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 0), (1, 88), (2, 101), (3, 3), (4, 4), (5, 5), (6, 111), (7, 109), (8, 113), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7ce) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 111), (7, 109), (8, 113), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7d1) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f37 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 111), (7, 109), (8, 113), (9, 117), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7d4) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f38 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 111), (7, 109), (8, 113), (9, 119), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7d8) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f39 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 0), (1, 88), (2, 115), (3, 3), (4, 4), (5, 5), (6, 111), (7, 109), (8, 113), (9, 121), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c7dd) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11c6ed_2 code

theorem rest_l11c6ed [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c6ed bytes_l11c6ed) (entryMap (live .l11c6ed))
      62 0x11c6ed bytes_l11c6ed b_l11c6ed := by
  have f0 : InstrSpec 0x11c6ed [0x48, 0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x11c6ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11c6ed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c6ed 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11c6ed 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x11c6ed 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c6f2 [0x48, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x11c6f2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11c6f2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c6f2 1 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c6f2 1 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x11c6f2 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x11c6fa [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x11c6fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11c6fa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c6fa 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11c6fa 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x11c6fa 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11c6ff [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x11c6ff 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11c6ff + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c6ff 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c6ff 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x11c6ff 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x11c707 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x11c707 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11c707 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c707 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11c707 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x11c707 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x11c70c [0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x11c70c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11c70c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c70c 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c70c 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x11c70c 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x11c714 [0x48, 0x8B, 0x0C, 0x24] (LoadPre 0x11c714 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11c714 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c714 1 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11c714 1 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11c714 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x11c718 [0x48, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x11c718 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c718 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c718 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11c718 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11c718 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x11c71d [0x48, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x11c71d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11c71d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c71d 2 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c71d 2 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x11c71d 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x11c725 [0x48, 0x89, 0x4C, 0x24, 0x78] (StorePre 0x11c725 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11c725 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c725 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c725 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x11c725 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x11c72a [0x48, 0x8B, 0x4C, 0x24, 0x50] (LoadPre 0x11c72a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11c72a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c72a 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11c72a 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x11c72a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x11c72f [0x48, 0x89, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x11c72f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11c72f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c72f 1 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c72f 1 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x11c72f 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x11c737 [0x48, 0x8B, 0x4C, 0x24, 0x58] (LoadPre 0x11c737 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11c737 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c737 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11c737 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x11c737 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x11c73c [0x48, 0x89, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x11c73c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11c73c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c73c 1 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c73c 1 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x11c73c 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x11c744 [0x48, 0x8B, 0x4C, 0x24, 0x60] (LoadPre 0x11c744 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11c744 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c744 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11c744 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x11c744 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x11c749 [0x48, 0x89, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x11c749 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11c749 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c749 1 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c749 1 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x11c749 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x11c751 [0x48, 0x8B, 0x4C, 0x24, 0x68] (LoadPre 0x11c751 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11c751 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c751 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11c751 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x11c751 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x11c756 [0x48, 0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00] (StorePre 0x11c756 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x11c756 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c756 1 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11c756 1 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x11c756 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x11c75e [0x48, 0x8B, 0x54, 0x24, 0x70] (LoadPre 0x11c75e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11c75e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c75e 2 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11c75e 2 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x11c75e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x11c763 [0x48, 0xBE, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x00] (fun s => s.RIP = 0x11c763) (movR64Imm64Effect 0x11c763 6 0x3fffffffffffc)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x11c763 6 0x3fffffffffffc).toInstrSpec (mov_r64_imm64_effect_step 0x11c763 0x48 0xbe (by decide) (by decide) 0x3fffffffffffc) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6f2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6fa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c6ff) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c707) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c70c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c714) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c718) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c71d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c725) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c72a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 68), (2, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c72f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 68), (2, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c737) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 71), (2, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c73c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 71), (2, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c744) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 74), (2, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c749) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 74), (2, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c751) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 77), (2, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c756) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 77), (2, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c75e) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 77), (2, 80), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c763) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 77), (2, 80), (3, 3), (4, 4), (5, 5), (6, 82), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c76d) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11c6ed_1 code

theorem block_l11c6ed [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c6ed :=
  Rest.liftedBlock (rest_l11c6ed code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c6ed x hx)

theorem rest_l11c845 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c845 bytes_l11c845) (entryMap (live .l11c845))
      16 0x11c845 bytes_l11c845 b_l11c845 := by
  have f0 : InstrSpec 0x11c845 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c845) (movR32Imm32Effect 0x11c845 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11c845 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11c845 0xb9 (by decide) 0xf) pre_rip
  have f1 : InstrSpec 0x11c84a [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11c84a) (movR64R64Effect 0x11c84a 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c84a 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11c84a 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c84d [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x11c84d) (movR64R64Effect 0x11c84d 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c84d 6 15).toInstrSpec (mov_r64_r64_effect_step 0x11c84d 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c850 [0xF3, 0x48, 0xA5] (RepPre 0x11c850 (RepMovsqPre 0x11c850)) (repMovsqEffect 0x11c850)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11c850).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11c850 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x11c853 [0xB9, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11c853) (movR32Imm32Effect 0x11c853 5 1 0xf)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11c853 5 1 0xf).toInstrSpec (mov_r32_imm32_effect_step 0x11c853 0xb9 (by decide) 0xf) pre_rip
  have f5 : InstrSpec 0x11c858 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x11c858) (movR64R64Effect 0x11c858 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c858 7 3).toInstrSpec (mov_r64_r64_effect_step 0x11c858 0x48 0xdf (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11c85b [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x11c85b) (movR64R64Effect 0x11c85b 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11c85b 6 14).toInstrSpec (mov_r64_r64_effect_step 0x11c85b 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11c85e [0xF3, 0x48, 0xA5] (RepPre 0x11c85e (RepMovsqPre 0x11c85e)) (repMovsqEffect 0x11c85e)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x11c85e).toInstrSpecOfRuns (rep_movsq_runs hstride 0x11c85e 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f8 : InstrSpec 0x11c861 [0x48, 0x81, 0xC4, 0x68, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11c861) (addR64Imm32Effect 0x11c861 4 0x168)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x11c861 4 0x168).toInstrSpec (add_r64_imm32_effect_step 0x11c861 0x48 0xc4 0x168 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11c868 [0x5B] (PopPre 0x11c868) (popR64Effect 0x11c868 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11c868 1 3).toInstrSpec (pop_r64_effect_step 0x11c868 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x11c869 [0x41, 0x5C] (PopPre 0x11c869) (popR64Effect 0x11c869 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11c869 2 12).toInstrSpec (pop_r64_rex_effect_step 0x11c869 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x11c86b [0x41, 0x5D] (PopPre 0x11c86b) (popR64Effect 0x11c86b 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11c86b 2 13).toInstrSpec (pop_r64_rex_effect_step 0x11c86b 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x11c86d [0x41, 0x5E] (PopPre 0x11c86d) (popR64Effect 0x11c86d 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11c86d 2 14).toInstrSpec (pop_r64_rex_effect_step 0x11c86d 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f13 : InstrSpec 0x11c86f [0x41, 0x5F] (PopPre 0x11c86f) (popR64Effect 0x11c86f 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11c86f 2 15).toInstrSpec (pop_r64_rex_effect_step 0x11c86f 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f14 : InstrSpec 0x11c871 [0x5D] (PopPre 0x11c871) (popR64Effect 0x11c871 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11c871 1 5).toInstrSpec (pop_r64_effect_step 0x11c871 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f15 : InstrSpec 0x11c872 [0xC3] (RetPre 0x11c872) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x11c872).toInstrSpec (ret_effect_step 0x11c872) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c84a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c84d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c850) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c853) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 60), (2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c858) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 60), (2, 2), (3, 3), (4, 4), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c85b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 60), (2, 2), (3, 3), (4, 4), (6, 64), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c85e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 68) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 3), (4, 4), (6, 66), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c861) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 3), (4, 70), (6, 66), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c868) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 72), (4, 73), (6, 66), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c869) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 72), (4, 76), (6, 66), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 75), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c86b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 79) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 72), (4, 79), (6, 66), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 75), (13, 78), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c86d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 82) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 72), (4, 82), (6, 66), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 75), (13, 78), (14, 81), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c86f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f13 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 85) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 72), (4, 85), (6, 66), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 75), (13, 78), (14, 81), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c871) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f14 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 88) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 72), (4, 88), (5, 87), (6, 66), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 75), (13, 78), (14, 81), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c872) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f15 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 91) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 92) (ρ' := [(0, 0), (1, 68), (2, 2), (3, 72), (4, 91), (5, 87), (6, 66), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 75), (13, 78), (14, 81), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) f15 (by decide) rfl rfl rfl (by decide)

theorem block_l11c845 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c845 :=
  Rest.liftedBlock (rest_l11c845 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c845 x hx)

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

theorem_by block_l11c510_eval :
    program.runBlock (dialect code) ⟨.l11c510, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c55b_eval :
    program.runBlock (dialect code) ⟨.l11c55b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c574_eval :
    program.runBlock (dialect code) ⟨.l11c574, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c591_eval :
    program.runBlock (dialect code) ⟨.l11c591, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c5a3_eval :
    program.runBlock (dialect code) ⟨.l11c5a3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c5c0_eval :
    program.runBlock (dialect code) ⟨.l11c5c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c5d5_eval :
    program.runBlock (dialect code) ⟨.l11c5d5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c5f2_eval :
    program.runBlock (dialect code) ⟨.l11c5f2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c607_eval :
    program.runBlock (dialect code) ⟨.l11c607, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c624_eval :
    program.runBlock (dialect code) ⟨.l11c624, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c639_eval :
    program.runBlock (dialect code) ⟨.l11c639, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c656_eval :
    program.runBlock (dialect code) ⟨.l11c656, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c66b_eval :
    program.runBlock (dialect code) ⟨.l11c66b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c688_eval :
    program.runBlock (dialect code) ⟨.l11c688, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c69d_eval :
    program.runBlock (dialect code) ⟨.l11c69d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c6ba_eval :
    program.runBlock (dialect code) ⟨.l11c6ba, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c6d2_eval :
    program.runBlock (dialect code) ⟨.l11c6d2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c6ed_eval :
    program.runBlock (dialect code) ⟨.l11c6ed, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c845_eval :
    program.runBlock (dialect code) ⟨.l11c845, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Ecdh.LIR
