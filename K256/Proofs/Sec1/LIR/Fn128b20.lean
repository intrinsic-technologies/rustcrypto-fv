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

theorem rest_l128b20_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x128b20 bytes_l128b20) [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]
      10 0x128b5a bytes_l128b20_1 b_l128b20_1 := by
  have f20 : InstrSpec 0x128b5a [0x85, 0xF6] (fun s => s.RIP = 0x128b5a) (testR32R32Effect 0x128b5a 2 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR32R32Effect_footprint 0x128b5a 2 6 6).toInstrSpec (test_r32_r32_effect_step 0x128b5a 0xf6 (by decide)) pre_rip
  have f21 : InstrSpec 0x128b5c [0xBE, 0x2D, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128b5c) (movR32Imm32Effect 0x128b5c 5 6 0x2d)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x128b5c 5 6 0x2d).toInstrSpec (mov_r32_imm32_effect_step 0x128b5c 0xbe (by decide) 0x2d) pre_rip
  have f22 : InstrSpec 0x128b61 [0x0F, 0x45, 0xF2] (fun s => s.RIP = 0x128b61) (atFlags (condHolds 5) (cmovR32R32Effect 0x128b61 3 6 2))
      [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 6, .rip] :=
    (cmovR32R32Effect_footprint 0x128b61 3 6 2 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x128b61 5 0xf2 (by decide) c)) pre_rip
  have f23 : InstrSpec 0x128b64 [0x89, 0x75, 0xD4] (StorePre 0x128b64 3 (fun s => AddrMode.addr (.base 5 (.d8 0xd4)) s (0x128b64 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x128b64 6 (.base 5 (.d8 0xd4)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x128b64 6 (.base 5 (.d8 0xd4))).toInstrSpec (mov_m32_r32_low_effect_step 0x128b64 6 (.base 5 (.d8 0xd4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x128b67 [0x41, 0xB9, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128b67) (movR32Imm32Effect 0x128b67 6 9 0x1)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x128b67 6 9 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x128b67 0x41 0xb9 (by decide) (by decide) 0x1) pre_rip
  have f25 : InstrSpec 0x128b6d [0x4C, 0x0F, 0x45, 0xC8] (fun s => s.RIP = 0x128b6d) (atFlags (condHolds 5) (cmovR64R64Effect 0x128b6d 4 9 0))
      [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 9, .rip] :=
    (cmovR64R64Effect_footprint 0x128b6d 4 9 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x128b6d 5 0x4c (by decide) 0xc8 (by decide) c)) pre_rip
  have f26 : InstrSpec 0x128b71 [0x4D, 0x01, 0xE9] (fun s => s.RIP = 0x128b71) (addR64R64Effect 0x128b71 9 13)
      [.gpr 9, .gpr 13] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x128b71 9 13).toInstrSpec (add_r64_r64_effect_step 0x128b71 0x4d 0xe9 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x128b74 [0x41, 0xF7, 0xC7, 0x00, 0x00, 0x80, 0x00] (fun s => s.RIP = 0x128b74) (testR32Imm32Effect 0x128b74 7 15 0x800000)
      [.gpr 15] [] [.flags, .rip] :=
    (testR32Imm32Effect_footprint 0x128b74 7 15 0x800000).toInstrSpec (test_r32_imm32_rex_effect_step 0x128b74 0x41 0xc7 0x800000 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x128b7b [0x48, 0x89, 0x4D, 0xB8] (StorePre 0x128b7b 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x128b7b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128b7b 1 (.base 5 (.d8 0xb8)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128b7b 1 (.base 5 (.d8 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x128b7b 0x48 (by decide) 1 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b5c) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 94), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b61) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f22 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b64) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b67) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 99), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b6d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 101), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b71) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 103), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b74) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 103), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 105), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b7b) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 103), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 105), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b7f) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 108) (jcc_rel8_effect_step 0x128b7f 5 0x5b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l128b20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128b20 bytes_l128b20) (entryMap (live .l128b20))
      30 0x128b20 bytes_l128b20 b_l128b20 := by
  have f0 : InstrSpec 0x128b20 [0x55] (PushPre 0x128b20 1) (pushR64Effect 0x128b20 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128b20 1 5).toInstrSpec (push_r64_effect_step 0x128b20 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x128b21 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x128b21) (movR64R64Effect 0x128b21 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x128b21 5 4).toInstrSpec (mov_r64_r64_effect_step 0x128b21 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128b24 [0x41, 0x57] (PushPre 0x128b24 2) (pushR64Effect 0x128b24 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128b24 2 15).toInstrSpec (push_r64_rex_effect_step 0x128b24 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x128b26 [0x41, 0x56] (PushPre 0x128b26 2) (pushR64Effect 0x128b26 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128b26 2 14).toInstrSpec (push_r64_rex_effect_step 0x128b26 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x128b28 [0x41, 0x55] (PushPre 0x128b28 2) (pushR64Effect 0x128b28 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128b28 2 13).toInstrSpec (push_r64_rex_effect_step 0x128b28 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x128b2a [0x41, 0x54] (PushPre 0x128b2a 2) (pushR64Effect 0x128b2a 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128b2a 2 12).toInstrSpec (push_r64_rex_effect_step 0x128b2a 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x128b2c [0x53] (PushPre 0x128b2c 1) (pushR64Effect 0x128b2c 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128b2c 1 3).toInstrSpec (push_r64_effect_step 0x128b2c 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x128b2d [0x48, 0x83, 0xEC, 0x48] (fun s => s.RIP = 0x128b2d) (subR64Imm8Effect 0x128b2d 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x128b2d 4 0x48).toInstrSpec (sub_r64_imm8_effect_step 0x128b2d 0x48 0xec 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x128b31 [0x4D, 0x89, 0xCD] (fun s => s.RIP = 0x128b31) (movR64R64Effect 0x128b31 13 9)
      [.gpr 9] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x128b31 13 9).toInstrSpec (mov_r64_r64_effect_step 0x128b31 0x4d 0xcd (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x128b34 [0x4C, 0x89, 0x45, 0xC0] (StorePre 0x128b34 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x128b34 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128b34 8 (.base 5 (.d8 0xc0)))
      [.gpr 8, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128b34 8 (.base 5 (.d8 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x128b34 0x4c (by decide) 0 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x128b38 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x128b38) (movR64R64Effect 0x128b38 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x128b38 14 2).toInstrSpec (mov_r64_r64_effect_step 0x128b38 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x128b3b [0x49, 0x89, 0xFC] (fun s => s.RIP = 0x128b3b) (movR64R64Effect 0x128b3b 12 7)
      [.gpr 7] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x128b3b 12 7).toInstrSpec (mov_r64_r64_effect_step 0x128b3b 0x49 0xfc (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x128b3e [0x44, 0x8B, 0x7F, 0x10] (LoadPre 0x128b3e (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x128b3e + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x128b3e 15 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x128b3e 15 (.base 7 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x128b3e 0x44 (by decide) 7 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x128b42 [0x44, 0x89, 0xF8] (fun s => s.RIP = 0x128b42) (movR32R32Effect 0x128b42 3 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x128b42 3 0 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x128b42 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x128b45 [0x25, 0x00, 0x00, 0x20, 0x00] (fun s => s.RIP = 0x128b45) (andEaxImm32Effect 0x128b45 0x200000)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x128b45 0x200000).toInstrSpec (and_eax_imm32_effect_step 0x128b45 0x200000) pre_rip
  have f15 : InstrSpec 0x128b4a [0x83, 0xF8, 0x01] (fun s => s.RIP = 0x128b4a) (cmpR32Imm8Effect 0x128b4a 3 0 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x128b4a 3 0 0x1).toInstrSpec (cmp_r32_imm8_effect_step 0x128b4a 0xf8 0x1 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x128b4d [0xBA, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128b4d) (movR32Imm32Effect 0x128b4d 5 2 0x0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x128b4d 5 2 0x0).toInstrSpec (mov_r32_imm32_effect_step 0x128b4d 0xba (by decide) 0x0) pre_rip
  have f17 : InstrSpec 0x128b52 [0x19, 0xD2] (fun s => s.RIP = 0x128b52) (atFlags StatusFlags.CF (sbbR32R32Effect 0x128b52 2 2 2))
      [.gpr 2, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (sbbR32R32Effect_footprint 0x128b52 2 2 2).toInstrSpec (StepEffect.atFlags fun c => (sbb_r32_r32_effect_step 0x128b52 0xd2 c (by decide))) pre_rip
  have f18 : InstrSpec 0x128b54 [0x83, 0xCA, 0x2B] (fun s => s.RIP = 0x128b54) (orR32Imm8Effect 0x128b54 3 2 0x2b)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (orR32Imm8Effect_footprint 0x128b54 3 2 0x2b).toInstrSpec (or_r32_imm8_effect_step 0x128b54 0xca 0x2b (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x128b57 [0xC1, 0xE8, 0x15] (fun s => s.RIP = 0x128b57) (shrR32Effect 0x128b57 3 0 21)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x128b57 3 0 21).toInstrSpec (shr_r32_imm8_effect_step 0x128b57 0xe8 0x15 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b21) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b24) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b26) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b28) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b2a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b2c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b2d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b31) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 69), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b34) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 69), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b38) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 69), (14, 72), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b3b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b3e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b42) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b45) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b4a) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (16, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b4d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 80), (1, 1), (2, 84), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (16, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b52) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 80), (1, 1), (2, 86), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b54) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 80), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b57) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b5a) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l128b20_1 code

theorem block_l128b20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128b20 :=
  Rest.liftedBlock (rest_l128b20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128b20 x hx)

theorem rest_l128b81 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128b81 bytes_l128b81) (entryMap (live .l128b81))
      4 0x128b81 bytes_l128b81 b_l128b81 := by
  have f0 : InstrSpec 0x128b81 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x128b81) (xorR32R32Effect 0x128b81 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x128b81 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x128b81 0x45 0xf6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128b84 [0x41, 0x0F, 0xB7, 0x5C, 0x24, 0x14] (LoadPre 0x128b84 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x14)) s (0x128b84 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x128b84 6 3 (.sib 12 none 0 (.d8 0x14)))
      [.gpr 12] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x128b84 6 3 (.sib 12 none 0 (.d8 0x14))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x128b84 0x41 (by decide) 3 (.sib 12 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128b8a [0x49, 0x39, 0xD9] (fun s => s.RIP = 0x128b8a) (cmpR64R64Effect 0x128b8a 9 3)
      [.gpr 9, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x128b8a 9 3).toInstrSpec (cmp_r64_r64_effect_step 0x128b8a 0x49 0xd9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b84) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 55), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b8a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 55), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b8d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x128b8d 2 0x104) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128b81 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128b81 :=
  Rest.liftedBlock (rest_l128b81 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128b81 x hx)

theorem rest_l128b93 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128b93 bytes_l128b93) (entryMap (live .l128b93))
      8 0x128b93 bytes_l128b93 b_l128b93 := by
  have f0 : InstrSpec 0x128b93 [0x4D, 0x8B, 0x3C, 0x24] (LoadPre 0x128b93 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x128b93 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128b93 15 (.sib 12 none 0 .none))
      [.gpr 12] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x128b93 15 (.sib 12 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128b93 0x4d (by decide) 7 (.sib 12 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128b97 [0x4D, 0x8B, 0x64, 0x24, 0x08] (LoadPre 0x128b97 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x128b97 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x128b97 12 (.sib 12 none 0 (.d8 0x8)))
      [.gpr 12] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x128b97 12 (.sib 12 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128b97 0x4d (by decide) 4 (.sib 12 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128b9c [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x128b9c) (movR64R64Effect 0x128b9c 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128b9c 7 15).toInstrSpec (mov_r64_r64_effect_step 0x128b9c 0x4c 0xff (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128b9f [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x128b9f) (movR64R64Effect 0x128b9f 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x128b9f 6 12).toInstrSpec (mov_r64_r64_effect_step 0x128b9f 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x128ba2 [0x8B, 0x55, 0xD4] (LoadPre 0x128ba2 (fun s => AddrMode.addr (.base 5 (.d8 0xd4)) s (0x128ba2 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x128ba2 2 (.base 5 (.d8 0xd4)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x128ba2 2 (.base 5 (.d8 0xd4))).toInstrSpec (mov_r32_m32_low_effect_step 0x128ba2 2 (.base 5 (.d8 0xd4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x128ba5 [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x128ba5) (movR64R64Effect 0x128ba5 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x128ba5 1 14).toInstrSpec (mov_r64_r64_effect_step 0x128ba5 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x128ba8 [0x4C, 0x8B, 0x45, 0xB8] (LoadPre 0x128ba8 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x128ba8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128ba8 8 (.base 5 (.d8 0xb8)))
      [.gpr 5] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x128ba8 8 (.base 5 (.d8 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x128ba8 0x4c (by decide) 0 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x128bac [0xE8, 0x7F, 0x10, 0x00, 0x00] (PushPre 0x128bac 5) (callEffect (fun _ => 0x129c30) 0x128bb1)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x128bac 0x129c30 0x128bb1).toInstrSpec (call_rel32_effect_step 0x128bac 0x107f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b97) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b9c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 57), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b9f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ba2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ba5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ba8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (8, 65), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128bac) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 63), (2, 61), (3, 3), (4, 67), (5, 5), (6, 59), (7, 57), (8, 65), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c30) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l128b93 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128b93 :=
  Rest.liftedBlock (rest_l128b93 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128b93 x hx)

theorem rest_l128bb1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128bb1 bytes_l128bb1) (entryMap (live .l128bb1))
      4 0x128bb1 bytes_l128bb1 b_l128bb1 := by
  have f0 : InstrSpec 0x128bb1 [0x89, 0xC1] (fun s => s.RIP = 0x128bb1) (movR32R32Effect 0x128bb1 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x128bb1 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x128bb1 0xc1 (by decide)) pre_rip
  have f1 : InstrSpec 0x128bb3 [0xB0, 0x01] (fun s => s.RIP = 0x128bb3) (movR8Imm8Effect 0x128bb3 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x128bb3 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x128bb3 0xb0 (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x128bb5 [0x84, 0xC9] (fun s => s.RIP = 0x128bb5) (testR8R8Effect 0x128bb5 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128bb5 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x128bb5 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128bb3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128bb5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128bb7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x128bb7 5 0x26b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128bb1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128bb1 :=
  Rest.liftedBlock (rest_l128bb1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128bb1 x hx)

theorem rest_l128bbd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128bbd bytes_l128bbd) (entryMap (live .l128bbd))
      11 0x128bbd bytes_l128bbd b_l128bbd := by
  have f0 : InstrSpec 0x128bbd [0x49, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x128bbd (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x128bbd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x128bbd 0 (.sib 12 none 0 (.d8 0x18)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128bbd 0 (.sib 12 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x128bbd 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128bc2 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x128bc2) (movR64R64Effect 0x128bc2 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128bc2 7 15).toInstrSpec (mov_r64_r64_effect_step 0x128bc2 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128bc5 [0x48, 0x8B, 0x75, 0xC0] (LoadPre 0x128bc5 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x128bc5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128bc5 6 (.base 5 (.d8 0xc0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x128bc5 6 (.base 5 (.d8 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x128bc5 0x48 (by decide) 6 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x128bc9 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x128bc9) (movR64R64Effect 0x128bc9 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x128bc9 2 13).toInstrSpec (mov_r64_r64_effect_step 0x128bc9 0x4c 0xea (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x128bcc [0x48, 0x83, 0xC4, 0x48] (fun s => s.RIP = 0x128bcc) (addR64Imm8Effect 0x128bcc 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x128bcc 4 0x48).toInstrSpec (add_r64_imm8_effect_step 0x128bcc 0x48 0xc4 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x128bd0 [0x5B] (PopPre 0x128bd0) (popR64Effect 0x128bd0 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128bd0 1 3).toInstrSpec (pop_r64_effect_step 0x128bd0 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x128bd1 [0x41, 0x5C] (PopPre 0x128bd1) (popR64Effect 0x128bd1 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128bd1 2 12).toInstrSpec (pop_r64_rex_effect_step 0x128bd1 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x128bd3 [0x41, 0x5D] (PopPre 0x128bd3) (popR64Effect 0x128bd3 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128bd3 2 13).toInstrSpec (pop_r64_rex_effect_step 0x128bd3 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x128bd5 [0x41, 0x5E] (PopPre 0x128bd5) (popR64Effect 0x128bd5 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128bd5 2 14).toInstrSpec (pop_r64_rex_effect_step 0x128bd5 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x128bd7 [0x41, 0x5F] (PopPre 0x128bd7) (popR64Effect 0x128bd7 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128bd7 2 15).toInstrSpec (pop_r64_rex_effect_step 0x128bd7 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x128bd9 [0x5D] (PopPre 0x128bd9) (popR64Effect 0x128bd9 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128bd9 1 5).toInstrSpec (pop_r64_effect_step 0x128bd9 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x128bc2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x128bc5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x128bc9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x128bcc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(4, 57), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x128bd0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(4, 59), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x128bd1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(4, 61), (5, 5), (13, 13), (15, 15)]) (p' := 0x128bd3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(4, 63), (5, 5), (15, 15)]) (p' := 0x128bd5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(4, 65), (5, 5), (15, 15)]) (p' := 0x128bd7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(4, 67), (5, 5)]) (p' := 0x128bd9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := []) (p' := 0x128bda) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128bbd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128bbd :=
  Rest.liftedBlock (rest_l128bbd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128bbd x hx)

theorem rest_l128bdc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128bdc bytes_l128bdc) (entryMap (live .l128bdc))
      2 0x128bdc bytes_l128bdc b_l128bdc := by
  have f0 : InstrSpec 0x128bdc [0x48, 0x83, 0xF9, 0x20] (fun s => s.RIP = 0x128bdc) (cmpR64Imm8Effect 0x128bdc 1 0x20)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x128bdc 1 0x20).toInstrSpec (cmp_r64_imm8_effect_step 0x128bdc 0x48 0xf9 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128be0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128be0 3 0x18) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128bdc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128bdc :=
  Rest.liftedBlock (rest_l128bdc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128bdc x hx)

theorem rest_l128be2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128be2 bytes_l128be2) (entryMap (live .l128be2))
      2 0x128be2 bytes_l128be2 b_l128be2 := by
  have f0 : InstrSpec 0x128be2 [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x128be2) (testR64R64Effect 0x128be2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x128be2 1 1).toInstrSpec (test_r64_r64_effect_step 0x128be2 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128be5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128be5 4 0x27) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128be2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128be2 :=
  Rest.liftedBlock (rest_l128be2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128be2 x hx)

theorem rest_l128be7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128be7 bytes_l128be7) (entryMap (live .l128be7))
      4 0x128be7 bytes_l128be7 b_l128be7 := by
  have f0 : InstrSpec 0x128be7 [0x41, 0x89, 0xCA] (fun s => s.RIP = 0x128be7) (movR32R32Effect 0x128be7 3 10 1)
      [.gpr 1] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x128be7 3 10 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x128be7 0x41 0xca (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128bea [0x41, 0x83, 0xE2, 0x03] (fun s => s.RIP = 0x128bea) (andR32Imm8Effect 0x128bea 4 10 0x3)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x128bea 4 10 0x3).toInstrSpec (and_r32_imm8_rex_effect_step 0x128bea 0x41 0xe2 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128bee [0x48, 0x83, 0xF9, 0x04] (fun s => s.RIP = 0x128bee) (cmpR64Imm8Effect 0x128bee 1 0x4)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x128bee 1 0x4).toInstrSpec (cmp_r64_imm8_effect_step 0x128bee 0x48 0xf9 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128bea) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128bee) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128bf2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x128bf2 3 0x1e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128be7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128be7 :=
  Rest.liftedBlock (rest_l128be7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128be7 x hx)

theorem rest_l128bf4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128bf4 bytes_l128bf4) (entryMap (live .l128bf4))
      3 0x128bf4 bytes_l128bf4 b_l128bf4 := by
  have f0 : InstrSpec 0x128bf4 [0x31, 0xD2] (fun s => s.RIP = 0x128bf4) (xorR32R32Effect 0x128bf4 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x128bf4 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x128bf4 0xd2 (by decide)) pre_rip
  have f1 : InstrSpec 0x128bf6 [0x31, 0xC0] (fun s => s.RIP = 0x128bf6) (xorR32R32Effect 0x128bf6 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x128bf6 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x128bf6 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128bf6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128bf8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x128bf8 0x6e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l128bf4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128bf4 :=
  Rest.liftedBlock (rest_l128bf4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128bf4 x hx)

theorem rest_l128bfa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128bfa bytes_l128bfa) (entryMap (live .l128bfa))
      4 0x128bfa bytes_l128bfa b_l128bfa := by
  have f0 : InstrSpec 0x128bfa [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x128bfa) (movR64R64Effect 0x128bfa 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128bfa 7 14).toInstrSpec (mov_r64_r64_effect_step 0x128bfa 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128bfd [0x48, 0x89, 0xCE] (fun s => s.RIP = 0x128bfd) (movR64R64Effect 0x128bfd 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x128bfd 6 1).toInstrSpec (mov_r64_r64_effect_step 0x128bfd 0x48 0xce (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128c00 [0x4C, 0x89, 0xCB] (fun s => s.RIP = 0x128c00) (movR64R64Effect 0x128c00 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x128c00 3 9).toInstrSpec (mov_r64_r64_effect_step 0x128c00 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128c03 [0xFF, 0x15, 0xE7, 0xB1, 0x0D, 0x00] (GoesTo (CallMemPre 0x128c03 (.rip 0xdb1e7)) (callEffect (callMemPtr 0x128c03 (.rip 0xdb1e7)) (0x128c03 + BitVec.ofNat 64 (callMemLen (.rip 0xdb1e7)))) 0x1297a0) (callEffect (callMemPtr 0x128c03 (.rip 0xdb1e7)) (0x128c03 + BitVec.ofNat 64 (callMemLen (.rip 0xdb1e7))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x128c03 (.rip 0xdb1e7)).toInstrSpec (call_m64_effect_step 0x128c03 (.rip 0xdb1e7) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x1297a0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128bfd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c00) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 57), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c03) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 57), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297a0) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l128bfa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128bfa :=
  Rest.liftedBlock (rest_l128bfa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128bfa x hx)

theorem rest_l128c09 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128c09 bytes_l128c09) (entryMap (live .l128c09))
      2 0x128c09 bytes_l128c09 b_l128c09 := by
  have f0 : InstrSpec 0x128c09 [0x49, 0x89, 0xD9] (fun s => s.RIP = 0x128c09) (movR64R64Effect 0x128c09 9 3)
      [.gpr 3] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x128c09 9 3).toInstrSpec (mov_r64_r64_effect_step 0x128c09 0x49 0xd9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c0c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x128c0c 0x77 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l128c09 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128c09 :=
  Rest.liftedBlock (rest_l128c09 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128c09 x hx)

theorem rest_l128c0e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128c0e bytes_l128c0e) (entryMap (live .l128c0e))
      2 0x128c0e bytes_l128c0e b_l128c0e := by
  have f0 : InstrSpec 0x128c0e [0x31, 0xC0] (fun s => s.RIP = 0x128c0e) (xorR32R32Effect 0x128c0e 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x128c0e 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x128c0e 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c10) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x128c10 0x73 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l128c0e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128c0e :=
  Rest.liftedBlock (rest_l128c0e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128c0e x hx)

theorem rest_l128c12 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128c12 bytes_l128c12) (entryMap (live .l128c12))
      5 0x128c12 bytes_l128c12 b_l128c12 := by
  have f0 : InstrSpec 0x128c12 [0x89, 0xCE] (fun s => s.RIP = 0x128c12) (movR32R32Effect 0x128c12 2 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x128c12 2 6 1).toInstrSpec (mov_r32_r32_effect_step 0x128c12 0xce (by decide)) pre_rip
  have f1 : InstrSpec 0x128c14 [0x83, 0xE6, 0x1C] (fun s => s.RIP = 0x128c14) (andR32Imm8Effect 0x128c14 3 6 0x1c)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x128c14 3 6 0x1c).toInstrSpec (and_r32_imm8_effect_step 0x128c14 0xe6 0x1c (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128c17 [0x31, 0xD2] (fun s => s.RIP = 0x128c17) (xorR32R32Effect 0x128c17 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x128c17 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x128c17 0xd2 (by decide)) pre_rip
  have f3 : InstrSpec 0x128c19 [0x31, 0xC0] (fun s => s.RIP = 0x128c19) (xorR32R32Effect 0x128c19 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x128c19 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x128c19 0xc0 (by decide)) pre_rip
  have f4 : InstrSpec 0x128c1b [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x128c1b) (fun _ => nopEffect 0x128c1b 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x128c1b 5).toInstrSpec (nop_m_effect_step 0x128c1b [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c14) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c17) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c19) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 57), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c1b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 1), (2, 57), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c20) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l128c12 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128c12 :=
  Rest.liftedBlock (rest_l128c12 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128c12 x hx)

theorem rest_l128c20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128c20 bytes_l128c20) (entryMap (live .l128c20))
      19 0x128c20 bytes_l128c20 b_l128c20 := by
  have f0 : InstrSpec 0x128c20 [0x31, 0xFF] (fun s => s.RIP = 0x128c20) (xorR32R32Effect 0x128c20 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x128c20 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x128c20 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x128c22 [0x41, 0x80, 0x3C, 0x16, 0xC0] (LoadPre 0x128c22 (fun s => AddrMode.addr (.sib 14 (some 2) 0 .none) s (0x128c22 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x128c22 5 (.sib 14 (some 2) 0 .none) 0xc0)
      [.gpr 14, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x128c22 5 (.sib 14 (some 2) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x128c22 0x41 (by decide) (.sib 14 (some 2) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128c27 [0x40, 0x0F, 0x9D, 0xC7] (fun s => s.RIP = 0x128c27) (atFlags (condHolds 13) (setccR8Effect 0x128c27 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x128c27 4 7 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x128c27 13 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x128c2b [0x48, 0x01, 0xC7] (fun s => s.RIP = 0x128c2b) (addR64R64Effect 0x128c2b 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x128c2b 7 0).toInstrSpec (add_r64_r64_effect_step 0x128c2b 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x128c2e [0x31, 0xC0] (fun s => s.RIP = 0x128c2e) (xorR32R32Effect 0x128c2e 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x128c2e 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x128c2e 0xc0 (by decide)) pre_rip
  have f5 : InstrSpec 0x128c30 [0x41, 0x80, 0x7C, 0x16, 0x01, 0xC0] (LoadPre 0x128c30 (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x1)) s (0x128c30 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x128c30 6 (.sib 14 (some 2) 0 (.d8 0x1)) 0xc0)
      [.gpr 14, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x128c30 6 (.sib 14 (some 2) 0 (.d8 0x1)) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x128c30 0x41 (by decide) (.sib 14 (some 2) 0 (.d8 0x1)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x128c36 [0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x128c36) (atFlags (condHolds 13) (setccR8Effect 0x128c36 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x128c36 3 0 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x128c36 13 0xc0 (by decide) (by decide) c)) pre_rip
  have f7 : InstrSpec 0x128c39 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x128c39) (xorR32R32Effect 0x128c39 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x128c39 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x128c39 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x128c3c [0x41, 0x80, 0x7C, 0x16, 0x02, 0xC0] (LoadPre 0x128c3c (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x2)) s (0x128c3c + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x128c3c 6 (.sib 14 (some 2) 0 (.d8 0x2)) 0xc0)
      [.gpr 14, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x128c3c 6 (.sib 14 (some 2) 0 (.d8 0x2)) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x128c3c 0x41 (by decide) (.sib 14 (some 2) 0 (.d8 0x2)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x128c42 [0x41, 0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x128c42) (atFlags (condHolds 13) (setccR8Effect 0x128c42 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x128c42 4 8 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x128c42 13 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  have f10 : InstrSpec 0x128c46 [0x49, 0x01, 0xC0] (fun s => s.RIP = 0x128c46) (addR64R64Effect 0x128c46 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x128c46 8 0).toInstrSpec (add_r64_r64_effect_step 0x128c46 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x128c49 [0x49, 0x01, 0xF8] (fun s => s.RIP = 0x128c49) (addR64R64Effect 0x128c49 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x128c49 8 7).toInstrSpec (add_r64_r64_effect_step 0x128c49 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x128c4c [0x31, 0xC0] (fun s => s.RIP = 0x128c4c) (xorR32R32Effect 0x128c4c 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x128c4c 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x128c4c 0xc0 (by decide)) pre_rip
  have f13 : InstrSpec 0x128c4e [0x41, 0x80, 0x7C, 0x16, 0x03, 0xC0] (LoadPre 0x128c4e (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x3)) s (0x128c4e + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x128c4e 6 (.sib 14 (some 2) 0 (.d8 0x3)) 0xc0)
      [.gpr 14, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x128c4e 6 (.sib 14 (some 2) 0 (.d8 0x3)) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x128c4e 0x41 (by decide) (.sib 14 (some 2) 0 (.d8 0x3)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x128c54 [0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x128c54) (atFlags (condHolds 13) (setccR8Effect 0x128c54 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x128c54 3 0 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x128c54 13 0xc0 (by decide) (by decide) c)) pre_rip
  have f15 : InstrSpec 0x128c57 [0x4C, 0x01, 0xC0] (fun s => s.RIP = 0x128c57) (addR64R64Effect 0x128c57 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x128c57 0 8).toInstrSpec (add_r64_r64_effect_step 0x128c57 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x128c5a [0x48, 0x83, 0xC2, 0x04] (fun s => s.RIP = 0x128c5a) (addR64Imm8Effect 0x128c5a 2 0x4)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x128c5a 2 0x4).toInstrSpec (add_r64_imm8_effect_step 0x128c5a 0x48 0xc2 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x128c5e [0x48, 0x39, 0xD6] (fun s => s.RIP = 0x128c5e) (cmpR64R64Effect 0x128c5e 6 2)
      [.gpr 6, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x128c5e 6 2).toInstrSpec (cmp_r64_r64_effect_step 0x128c5e 0x48 0xd6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c22) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c27) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c2b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c2e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c30) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 64), (21, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c36) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 64), (21, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c39) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 69), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c3c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f8 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f8 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 69), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 71), (21, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c42) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 71), (21, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c46) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 76), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c49) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c4c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c4e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f13 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f13 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 80), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 82), (21, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c54) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 82), (21, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c57) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c5a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 87), (2, 89), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c5e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 87), (2, 89), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c61) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 93) (jcc_rel8_effect_step 0x128c61 5 0xbd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128c20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128c20 :=
  Rest.liftedBlock (rest_l128c20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128c20 x hx)

theorem rest_l128c63 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128c63 bytes_l128c63) (entryMap (live .l128c63))
      2 0x128c63 bytes_l128c63 b_l128c63 := by
  have f0 : InstrSpec 0x128c63 [0x4D, 0x85, 0xD2] (fun s => s.RIP = 0x128c63) (testR64R64Effect 0x128c63 10 10)
      [.gpr 10, .gpr 10] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x128c63 10 10).toInstrSpec (test_r64_r64_effect_step 0x128c63 0x4d 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c66) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128c66 4 0x1d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128c63 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128c63 :=
  Rest.liftedBlock (rest_l128c63 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128c63 x hx)

theorem rest_l128c68 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128c68 bytes_l128c68) (entryMap (live .l128c68))
      3 0x128c68 bytes_l128c68 b_l128c68 := by
  have f0 : InstrSpec 0x128c68 [0x4C, 0x01, 0xF2] (fun s => s.RIP = 0x128c68) (addR64R64Effect 0x128c68 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x128c68 2 14).toInstrSpec (add_r64_r64_effect_step 0x128c68 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128c6b [0x31, 0xF6] (fun s => s.RIP = 0x128c6b) (xorR32R32Effect 0x128c6b 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x128c6b 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x128c6b 0xf6 (by decide)) pre_rip
  have f2 : InstrSpec 0x128c6d [0x0F, 0x1F, 0x00] (fun s => s.RIP = 0x128c6d) (fun _ => nopEffect 0x128c6d 3)
      [] [] [.rip] :=
    (nopEffect_footprint 0x128c6d 3).toInstrSpec (nop_m_effect_step 0x128c6d [] (by decide) (by decide) (.base 0 .none) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c6b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 53), (4, 4), (5, 5), (6, 55), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c6d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 53), (4, 4), (5, 5), (6, 55), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c70) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l128c68 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128c68 :=
  Rest.liftedBlock (rest_l128c68 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128c68 x hx)

theorem rest_l128c70 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128c70 bytes_l128c70) (entryMap (live .l128c70))
      7 0x128c70 bytes_l128c70 b_l128c70 := by
  have f0 : InstrSpec 0x128c70 [0x31, 0xFF] (fun s => s.RIP = 0x128c70) (xorR32R32Effect 0x128c70 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x128c70 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x128c70 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x128c72 [0x80, 0x3C, 0x32, 0xC0] (LoadPre 0x128c72 (fun s => AddrMode.addr (.sib 2 (some 6) 0 .none) s (0x128c72 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x128c72 4 (.sib 2 (some 6) 0 .none) 0xc0)
      [.gpr 2, .gpr 6] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x128c72 4 (.sib 2 (some 6) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x128c72 (.sib 2 (some 6) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128c76 [0x40, 0x0F, 0x9D, 0xC7] (fun s => s.RIP = 0x128c76) (atFlags (condHolds 13) (setccR8Effect 0x128c76 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x128c76 4 7 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x128c76 13 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x128c7a [0x48, 0x01, 0xF8] (fun s => s.RIP = 0x128c7a) (addR64R64Effect 0x128c7a 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x128c7a 0 7).toInstrSpec (add_r64_r64_effect_step 0x128c7a 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x128c7d [0x48, 0xFF, 0xC6] (fun s => s.RIP = 0x128c7d) (incR64Effect 0x128c7d 6)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (incR64Effect_footprint 0x128c7d 6).toInstrSpec (inc_r64_effect_step 0x128c7d 0x48 0xc6 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x128c80 [0x49, 0x39, 0xF2] (fun s => s.RIP = 0x128c80) (cmpR64R64Effect 0x128c80 10 6)
      [.gpr 10, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x128c80 10 6).toInstrSpec (cmp_r64_r64_effect_step 0x128c80 0x49 0xf2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c72) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c76) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c7a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (2, 2), (4, 4), (5, 5), (6, 6), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c7d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (2, 2), (4, 4), (5, 5), (6, 62), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c80) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 60), (2, 2), (4, 4), (5, 5), (6, 62), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c83) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x128c83 5 0xeb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128c70 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128c70 :=
  Rest.liftedBlock (rest_l128c70 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128c70 x hx)

theorem rest_l128c85 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128c85 bytes_l128c85) (entryMap (live .l128c85))
      4 0x128c85 bytes_l128c85 b_l128c85 := by
  have f0 : InstrSpec 0x128c85 [0x49, 0x01, 0xC1] (fun s => s.RIP = 0x128c85) (addR64R64Effect 0x128c85 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x128c85 9 0).toInstrSpec (add_r64_r64_effect_step 0x128c85 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128c88 [0x41, 0x0F, 0xB7, 0x5C, 0x24, 0x14] (LoadPre 0x128c88 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x14)) s (0x128c88 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x128c88 6 3 (.sib 12 none 0 (.d8 0x14)))
      [.gpr 12] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x128c88 6 3 (.sib 12 none 0 (.d8 0x14))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x128c88 0x41 (by decide) 3 (.sib 12 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128c8e [0x49, 0x39, 0xD9] (fun s => s.RIP = 0x128c8e) (cmpR64R64Effect 0x128c8e 9 3)
      [.gpr 9, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x128c8e 9 3).toInstrSpec (cmp_r64_r64_effect_step 0x128c8e 0x49 0xd9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (5, 5), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c88) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 55), (4, 4), (5, 5), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c8e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 55), (4, 4), (5, 5), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c91) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x128c91 3 0xfffffefc) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128c85 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128c85 :=
  Rest.liftedBlock (rest_l128c85 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128c85 x hx)

theorem rest_l128c97 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128c97 bytes_l128c97) (entryMap (live .l128c97))
      4 0x128c97 bytes_l128c97 b_l128c97 := by
  have f0 : InstrSpec 0x128c97 [0x41, 0xF7, 0xC7, 0x00, 0x00, 0x00, 0x01] (fun s => s.RIP = 0x128c97) (testR32Imm32Effect 0x128c97 7 15 0x1000000)
      [.gpr 15] [] [.flags, .rip] :=
    (testR32Imm32Effect_footprint 0x128c97 7 15 0x1000000).toInstrSpec (test_r32_imm32_rex_effect_step 0x128c97 0x41 0xc7 0x1000000 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128c9e [0x4C, 0x89, 0x6D, 0xA8] (StorePre 0x128c9e 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x128c9e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128c9e 13 (.base 5 (.d8 0xa8)))
      [.gpr 13, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128c9e 13 (.base 5 (.d8 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x128c9e 0x4c (by decide) 5 (.base 5 (.d8 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x128ca2 [0x4C, 0x89, 0x4D, 0xA0] (StorePre 0x128ca2 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa0)) s (0x128ca2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128ca2 9 (.base 5 (.d8 0xa0)))
      [.gpr 9, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128ca2 9 (.base 5 (.d8 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x128ca2 0x4c (by decide) 1 (.base 5 (.d8 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128c9e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ca2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ca6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x128ca6 5 0x28) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128c97 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128c97 :=
  Rest.liftedBlock (rest_l128c97 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128c97 x hx)

theorem rest_l128ca8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128ca8 bytes_l128ca8) (entryMap (live .l128ca8))
      9 0x128ca8 bytes_l128ca8 b_l128ca8 := by
  have f0 : InstrSpec 0x128ca8 [0x89, 0xDA] (fun s => s.RIP = 0x128ca8) (movR32R32Effect 0x128ca8 2 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x128ca8 2 2 3).toInstrSpec (mov_r32_r32_effect_step 0x128ca8 0xda (by decide)) pre_rip
  have f1 : InstrSpec 0x128caa [0x44, 0x29, 0xCA] (fun s => s.RIP = 0x128caa) (subR32R32Effect 0x128caa 3 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (subR32R32Effect_footprint 0x128caa 3 2 9).toInstrSpec (sub_r32_r32_rex_effect_step 0x128caa 0x44 0xca (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128cad [0x44, 0x89, 0xF8] (fun s => s.RIP = 0x128cad) (movR32R32Effect 0x128cad 3 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x128cad 3 0 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x128cad 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128cb0 [0xC1, 0xE8, 0x1D] (fun s => s.RIP = 0x128cb0) (shrR32Effect 0x128cb0 3 0 29)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x128cb0 3 0 29).toInstrSpec (shr_r32_imm8_effect_step 0x128cb0 0xe8 0x1d (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x128cb3 [0x83, 0xE0, 0x03] (fun s => s.RIP = 0x128cb3) (andR32Imm8Effect 0x128cb3 3 0 0x3)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x128cb3 3 0 0x3).toInstrSpec (and_r32_imm8_effect_step 0x128cb3 0xe0 0x3 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x128cb6 [0x48, 0x8D, 0x0D, 0x97, 0xAE, 0x0D, 0x00] (fun s => s.RIP = 0x128cb6) (leaR64Effect 0x128cb6 1 (.rip 0xdae97))
      [] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x128cb6 1 (.rip 0xdae97)).toInstrSpec (lea_r64_effect_step 0x128cb6 0x48 (by decide) 1 (.rip 0xdae97) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x128cbd [0x48, 0x63, 0x04, 0x81] (LoadPre 0x128cbd (fun s => AddrMode.addr (.sib 1 (some 0) 2 .none) s (0x128cbd + BitVec.ofNat 64 4)) 4) (movsxdR64M32Effect 0x128cbd 4 0 (.sib 1 (some 0) 2 .none))
      [.gpr 1, .gpr 0] [] [.reg 0, .rip] :=
    (movsxdR64M32Effect_footprint 0x128cbd 4 0 (.sib 1 (some 0) 2 .none)).toInstrSpec (movsxd_r64_m32_effect_step 0x128cbd 0x48 (by decide) 0 (.sib 1 (some 0) 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x128cc1 [0x48, 0x01, 0xC8] (fun s => s.RIP = 0x128cc1) (addR64R64Effect 0x128cc1 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x128cc1 0 1).toInstrSpec (add_r64_r64_effect_step 0x128cc1 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x128cc4 [0x89, 0x55, 0xB4] (StorePre 0x128cc4 3 (fun s => AddrMode.addr (.base 5 (.d8 0xb4)) s (0x128cc4 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x128cc4 2 (.base 5 (.d8 0xb4)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x128cc4 2 (.base 5 (.d8 0xb4))).toInstrSpec (mov_m32_r32_low_effect_step 0x128cc4 2 (.base 5 (.d8 0xb4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x128caa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x128cad) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x128cb0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x128cb3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x128cb6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x128cbd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 63), (2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x128cc1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(1, 63), (2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x128cc4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(1, 63), (2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x128cc7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128ca8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128ca8 :=
  Rest.liftedBlock (rest_l128ca8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128ca8 x hx)

theorem rest_l128cd0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128cd0 bytes_l128cd0) (entryMap (live .l128cd0))
      13 0x128cd0 bytes_l128cd0 b_l128cd0 := by
  have f0 : InstrSpec 0x128cd0 [0x49, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x128cd0 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x128cd0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x128cd0 0 (.sib 12 none 0 (.d8 0x10)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128cd0 0 (.sib 12 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x128cd0 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128cd5 [0x48, 0x89, 0x45, 0xC8] (StorePre 0x128cd5 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x128cd5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128cd5 0 (.base 5 (.d8 0xc8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128cd5 0 (.base 5 (.d8 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x128cd5 0x48 (by decide) 0 (.base 5 (.d8 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x128cd9 [0x25, 0x00, 0x00, 0xE0, 0x9F] (fun s => s.RIP = 0x128cd9) (andEaxImm32Effect 0x128cd9 0x9fe00000)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x128cd9 0x9fe00000).toInstrSpec (and_eax_imm32_effect_step 0x128cd9 0x9fe00000) pre_rip
  have f3 : InstrSpec 0x128cde [0x0D, 0x30, 0x00, 0x00, 0x20] (fun s => s.RIP = 0x128cde) (orEaxImm32Effect 0x128cde 0x20000030)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orEaxImm32Effect_footprint 0x128cde 0x20000030).toInstrSpec (or_eax_imm32_effect_step 0x128cde 0x20000030) pre_rip
  have f4 : InstrSpec 0x128ce3 [0x41, 0x89, 0x44, 0x24, 0x10] (StorePre 0x128ce3 5 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x128ce3 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x128ce3 0 (.sib 12 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 12] [] [.rip] :=
    (movM32R32Effect_footprint 0x128ce3 0 (.sib 12 none 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_effect_step 0x128ce3 0x41 (by decide) 0 (.sib 12 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x128ce8 [0x4D, 0x8B, 0x2C, 0x24] (LoadPre 0x128ce8 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x128ce8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128ce8 13 (.sib 12 none 0 .none))
      [.gpr 12] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x128ce8 13 (.sib 12 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128ce8 0x4d (by decide) 5 (.sib 12 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x128cec [0x4D, 0x8B, 0x7C, 0x24, 0x08] (LoadPre 0x128cec (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x128cec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x128cec 15 (.sib 12 none 0 (.d8 0x8)))
      [.gpr 12] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x128cec 15 (.sib 12 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128cec 0x4d (by decide) 7 (.sib 12 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x128cf1 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x128cf1) (movR64R64Effect 0x128cf1 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128cf1 7 13).toInstrSpec (mov_r64_r64_effect_step 0x128cf1 0x4c 0xef (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x128cf4 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x128cf4) (movR64R64Effect 0x128cf4 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x128cf4 6 15).toInstrSpec (mov_r64_r64_effect_step 0x128cf4 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x128cf7 [0x8B, 0x55, 0xD4] (LoadPre 0x128cf7 (fun s => AddrMode.addr (.base 5 (.d8 0xd4)) s (0x128cf7 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x128cf7 2 (.base 5 (.d8 0xd4)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x128cf7 2 (.base 5 (.d8 0xd4))).toInstrSpec (mov_r32_m32_low_effect_step 0x128cf7 2 (.base 5 (.d8 0xd4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x128cfa [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x128cfa) (movR64R64Effect 0x128cfa 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x128cfa 1 14).toInstrSpec (mov_r64_r64_effect_step 0x128cfa 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x128cfd [0x4C, 0x8B, 0x45, 0xB8] (LoadPre 0x128cfd (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x128cfd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128cfd 8 (.base 5 (.d8 0xb8)))
      [.gpr 5] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x128cfd 8 (.base 5 (.d8 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x128cfd 0x4c (by decide) 0 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x128d01 [0xE8, 0x2A, 0x0F, 0x00, 0x00] (PushPre 0x128d01 5) (callEffect (fun _ => 0x129c30) 0x128d06)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x128d01 0x129c30 0x128d06).toInstrSpec (call_rel32_effect_step 0x128d01 0xf2a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128cd5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128cd9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128cde) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ce3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ce8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128cec) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128cf1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (7, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128cf4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128cf7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 58), (2, 69), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128cfa) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 58), (1, 71), (2, 69), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128cfd) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 58), (1, 71), (2, 69), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 73), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128d01) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 58), (1, 71), (2, 69), (3, 3), (4, 75), (5, 5), (6, 67), (7, 65), (8, 73), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c30) f12 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l128cd0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128cd0 :=
  Rest.liftedBlock (rest_l128cd0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128cd0 x hx)

theorem rest_l128d06 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128d06 bytes_l128d06) (entryMap (live .l128d06))
      4 0x128d06 bytes_l128d06 b_l128d06 := by
  have f0 : InstrSpec 0x128d06 [0x89, 0xC1] (fun s => s.RIP = 0x128d06) (movR32R32Effect 0x128d06 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x128d06 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x128d06 0xc1 (by decide)) pre_rip
  have f1 : InstrSpec 0x128d08 [0xB0, 0x01] (fun s => s.RIP = 0x128d08) (movR8Imm8Effect 0x128d08 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x128d08 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x128d08 0xb0 (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x128d0a [0x84, 0xC9] (fun s => s.RIP = 0x128d0a) (testR8R8Effect 0x128d0a 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128d0a 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x128d0a 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128d08) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128d0a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128d0c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x128d0c 5 0x116) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128d06 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128d06 :=
  Rest.liftedBlock (rest_l128d06 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128d06 x hx)

theorem rest_l128d12 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128d12 bytes_l128d12) (entryMap (live .l128d12))
      3 0x128d12 bytes_l128d12 b_l128d12 := by
  have f0 : InstrSpec 0x128d12 [0x2B, 0x5D, 0xA0] (LoadPre 0x128d12 (fun s => AddrMode.addr (.base 5 (.d8 0xa0)) s (0x128d12 + BitVec.ofNat 64 3)) 4) (subR32M32Effect 0x128d12 3 3 (.base 5 (.d8 0xa0)))
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (subR32M32Effect_footprint 0x128d12 3 3 (.base 5 (.d8 0xa0))).toInstrSpec (sub_r32_m32_effect_step 0x128d12 3 (.base 5 (.d8 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128d15 [0xFF, 0xC3] (fun s => s.RIP = 0x128d15) (incR32Effect 0x128d15 2 3)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (incR32Effect_footprint 0x128d15 2 3).toInstrSpec (inc_r32_effect_step 0x128d15 0xc3 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128d17 [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128d17) (fun _ => nopEffect 0x128d17 9)
      [] [] [.rip] :=
    (nopEffect_footprint 0x128d17 9).toInstrSpec (nop_m_effect_step 0x128d17 [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (5, 5), (13, 13)]) (p' := 0x128d15) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 55), (5, 5), (13, 13)]) (p' := 0x128d17) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 55), (5, 5), (13, 13)]) (p' := 0x128d20) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l128d12 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128d12 :=
  Rest.liftedBlock (rest_l128d12 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128d12 x hx)

theorem rest_l128d20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128d20 bytes_l128d20) (entryMap (live .l128d20))
      2 0x128d20 bytes_l128d20 b_l128d20 := by
  have f0 : InstrSpec 0x128d20 [0x66, 0xFF, 0xCB] (fun s => s.RIP = 0x128d20) (decR16Effect 0x128d20 3 3)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (decR16Effect_footprint 0x128d20 3 3).toInstrSpec (dec_r16_effect_step 0x128d20 0xcb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.fresh (n := 53) f0 .ZF (fun _ => rfl) (decR16Effect_fresh 0x128d20 3 3 _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(5, 5), (13, 13), (19, 53)]) (p' := 0x128d23) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128d23 4 0x12) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128d20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128d20 :=
  Rest.liftedBlock (rest_l128d20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128d20 x hx)

theorem rest_l128d25 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128d25 bytes_l128d25) (entryMap (live .l128d25))
      2 0x128d25 bytes_l128d25 b_l128d25 := by
  have f0 : InstrSpec 0x128d25 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x128d25) (movR64R64Effect 0x128d25 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128d25 7 13).toInstrSpec (mov_r64_r64_effect_step 0x128d25 0x4c 0xef (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128d28 [0xBE, 0x30, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128d28) (movR32Imm32Effect 0x128d28 5 6 0x30)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x128d28 5 6 0x30).toInstrSpec (mov_r32_imm32_effect_step 0x128d28 0xbe (by decide) 0x30) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(13, 13)]) (p' := 0x128d28) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(13, 13)]) (p' := 0x128d2d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128d25 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128d25 :=
  Rest.liftedBlock (rest_l128d25 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128d25 x hx)

theorem rest_l128d31 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128d31 bytes_l128d31) (entryMap (live .l128d31))
      2 0x128d31 bytes_l128d31 b_l128d31 := by
  have f0 : InstrSpec 0x128d31 [0x84, 0xC0] (fun s => s.RIP = 0x128d31) (testR8R8Effect 0x128d31 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128d31 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x128d31 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128d33) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128d33 4 0xeb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128d31 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128d31 :=
  Rest.liftedBlock (rest_l128d31 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128d31 x hx)

theorem rest_l128d35 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128d35 bytes_l128d35) (entryMap (live .l128d35))
      1 0x128d35 bytes_l128d35 b_l128d35 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x128d35 0x6f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l128d35 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128d35 :=
  Rest.liftedBlock (rest_l128d35 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128d35 x hx)

theorem rest_l128d37 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128d37 bytes_l128d37) (entryMap (live .l128d37))
      3 0x128d37 bytes_l128d37 b_l128d37 := by
  have f0 : InstrSpec 0x128d37 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x128d37) (movR64R64Effect 0x128d37 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128d37 7 13).toInstrSpec (mov_r64_r64_effect_step 0x128d37 0x4c 0xef (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128d3a [0x48, 0x8B, 0x75, 0xC0] (LoadPre 0x128d3a (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x128d3a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128d3a 6 (.base 5 (.d8 0xc0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x128d3a 6 (.base 5 (.d8 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x128d3a 0x48 (by decide) 6 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128d3e [0x48, 0x8B, 0x55, 0xA8] (LoadPre 0x128d3e (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x128d3e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128d3e 2 (.base 5 (.d8 0xa8)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x128d3e 2 (.base 5 (.d8 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x128d3e 0x48 (by decide) 2 (.base 5 (.d8 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(5, 5), (13, 13)]) (p' := 0x128d3a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(5, 5), (13, 13)]) (p' := 0x128d3e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(5, 5), (13, 13)]) (p' := 0x128d42) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128d37 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128d37 :=
  Rest.liftedBlock (rest_l128d37 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128d37 x hx)

theorem rest_l128d46 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128d46 bytes_l128d46) (entryMap (live .l128d46))
      3 0x128d46 bytes_l128d46 b_l128d46 := by
  have f0 : InstrSpec 0x128d46 [0x84, 0xC0] (fun s => s.RIP = 0x128d46) (testR8R8Effect 0x128d46 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128d46 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x128d46 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128d48 [0xB0, 0x01] (fun s => s.RIP = 0x128d48) (movR8Imm8Effect 0x128d48 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x128d48 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x128d48 0xb0 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128d48) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128d4a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x128d4a 5 0xd8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128d46 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128d46 :=
  Rest.liftedBlock (rest_l128d46 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128d46 x hx)

theorem rest_l128d50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128d50 bytes_l128d50) (entryMap (live .l128d50))
      4 0x128d50 bytes_l128d50 b_l128d50 := by
  have f0 : InstrSpec 0x128d50 [0x48, 0x8B, 0x45, 0xC8] (LoadPre 0x128d50 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x128d50 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128d50 0 (.base 5 (.d8 0xc8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128d50 0 (.base 5 (.d8 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x128d50 0x48 (by decide) 0 (.base 5 (.d8 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128d54 [0x49, 0x89, 0x44, 0x24, 0x10] (StorePre 0x128d54 5 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x128d54 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x128d54 0 (.sib 12 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 12] [] [.rip] :=
    (movM64R64Effect_footprint 0x128d54 0 (.sib 12 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x128d54 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x128d59 [0x31, 0xC0] (fun s => s.RIP = 0x128d59) (xorR32R32Effect 0x128d59 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x128d59 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x128d59 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128d54) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128d59) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128d5b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 58) (jmp_rel32_effect_step 0x128d5b 0xc8 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l128d50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128d50 :=
  Rest.liftedBlock (rest_l128d50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128d50 x hx)

theorem rest_l128da6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128da6 bytes_l128da6) (entryMap (live .l128da6))
      2 0x128da6 bytes_l128da6 b_l128da6 := by
  have f0 : InstrSpec 0x128da6 [0xB0, 0x01] (fun s => s.RIP = 0x128da6) (movR8Imm8Effect 0x128da6 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x128da6 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x128da6 0xb0 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128da8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x128da8 0x7e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l128da6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128da6 :=
  Rest.liftedBlock (rest_l128da6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128da6 x hx)

theorem rest_l128e28 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128e28 bytes_l128e28) (entryMap (live .l128e28))
      8 0x128e28 bytes_l128e28 b_l128e28 := by
  have f0 : InstrSpec 0x128e28 [0x48, 0x83, 0xC4, 0x48] (fun s => s.RIP = 0x128e28) (addR64Imm8Effect 0x128e28 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x128e28 4 0x48).toInstrSpec (add_r64_imm8_effect_step 0x128e28 0x48 0xc4 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128e2c [0x5B] (PopPre 0x128e2c) (popR64Effect 0x128e2c 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128e2c 1 3).toInstrSpec (pop_r64_effect_step 0x128e2c 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x128e2d [0x41, 0x5C] (PopPre 0x128e2d) (popR64Effect 0x128e2d 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128e2d 2 12).toInstrSpec (pop_r64_rex_effect_step 0x128e2d 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x128e2f [0x41, 0x5D] (PopPre 0x128e2f) (popR64Effect 0x128e2f 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128e2f 2 13).toInstrSpec (pop_r64_rex_effect_step 0x128e2f 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x128e31 [0x41, 0x5E] (PopPre 0x128e31) (popR64Effect 0x128e31 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128e31 2 14).toInstrSpec (pop_r64_rex_effect_step 0x128e31 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x128e33 [0x41, 0x5F] (PopPre 0x128e33) (popR64Effect 0x128e33 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128e33 2 15).toInstrSpec (pop_r64_rex_effect_step 0x128e33 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x128e35 [0x5D] (PopPre 0x128e35) (popR64Effect 0x128e35 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128e35 1 5).toInstrSpec (pop_r64_effect_step 0x128e35 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x128e36 [0xC3] (RetPre 0x128e36) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x128e36).toInstrSpec (ret_effect_step 0x128e36) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128e2c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128e2d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128e2f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128e31) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128e33) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128e35) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128e36) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l128e28 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128e28 :=
  Rest.liftedBlock (rest_l128e28 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128e28 x hx)

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

theorem_by block_l128b20_eval :
    program.runBlock (dialect code) ⟨.l128b20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128b81_eval :
    program.runBlock (dialect code) ⟨.l128b81, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128b93_eval :
    program.runBlock (dialect code) ⟨.l128b93, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128bb1_eval :
    program.runBlock (dialect code) ⟨.l128bb1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128bbd_eval :
    program.runBlock (dialect code) ⟨.l128bbd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128bdc_eval :
    program.runBlock (dialect code) ⟨.l128bdc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128be2_eval :
    program.runBlock (dialect code) ⟨.l128be2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128be7_eval :
    program.runBlock (dialect code) ⟨.l128be7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128bf4_eval :
    program.runBlock (dialect code) ⟨.l128bf4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128bfa_eval :
    program.runBlock (dialect code) ⟨.l128bfa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128c09_eval :
    program.runBlock (dialect code) ⟨.l128c09, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128c0e_eval :
    program.runBlock (dialect code) ⟨.l128c0e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128c12_eval :
    program.runBlock (dialect code) ⟨.l128c12, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128c20_eval :
    program.runBlock (dialect code) ⟨.l128c20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128c63_eval :
    program.runBlock (dialect code) ⟨.l128c63, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128c68_eval :
    program.runBlock (dialect code) ⟨.l128c68, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128c70_eval :
    program.runBlock (dialect code) ⟨.l128c70, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128c85_eval :
    program.runBlock (dialect code) ⟨.l128c85, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128c97_eval :
    program.runBlock (dialect code) ⟨.l128c97, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128ca8_eval :
    program.runBlock (dialect code) ⟨.l128ca8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128cd0_eval :
    program.runBlock (dialect code) ⟨.l128cd0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128d06_eval :
    program.runBlock (dialect code) ⟨.l128d06, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128d12_eval :
    program.runBlock (dialect code) ⟨.l128d12, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128d20_eval :
    program.runBlock (dialect code) ⟨.l128d20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128d25_eval :
    program.runBlock (dialect code) ⟨.l128d25, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128d31_eval :
    program.runBlock (dialect code) ⟨.l128d31, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128d35_eval :
    program.runBlock (dialect code) ⟨.l128d35, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128d37_eval :
    program.runBlock (dialect code) ⟨.l128d37, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128d46_eval :
    program.runBlock (dialect code) ⟨.l128d46, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128d50_eval :
    program.runBlock (dialect code) ⟨.l128d50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128da6_eval :
    program.runBlock (dialect code) ⟨.l128da6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128e28_eval :
    program.runBlock (dialect code) ⟨.l128e28, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Sec1.LIR
