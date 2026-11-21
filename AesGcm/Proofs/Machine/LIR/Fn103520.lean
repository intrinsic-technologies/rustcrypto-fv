import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l103520_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x103520 bytes_l103520) [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]
      10 0x10355a bytes_l103520_1 b_l103520_1 := by
  have f20 : InstrSpec 0x10355a [0x85, 0xF6] (fun s => s.RIP = 0x10355a) (testR32R32Effect 0x10355a 2 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR32R32Effect_footprint 0x10355a 2 6 6).toInstrSpec (test_r32_r32_effect_step 0x10355a 0xf6 (by decide)) pre_rip
  have f21 : InstrSpec 0x10355c [0xBE, 0x2D, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10355c) (movR32Imm32Effect 0x10355c 5 6 0x2d)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10355c 5 6 0x2d).toInstrSpec (mov_r32_imm32_effect_step 0x10355c 0xbe (by decide) 0x2d) pre_rip
  have f22 : InstrSpec 0x103561 [0x0F, 0x45, 0xF2] (fun s => s.RIP = 0x103561) (atFlags (condHolds 5) (cmovR32R32Effect 0x103561 3 6 2))
      [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 6, .rip] :=
    (cmovR32R32Effect_footprint 0x103561 3 6 2 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x103561 5 0xf2 (by decide) c)) pre_rip
  have f23 : InstrSpec 0x103564 [0x89, 0x75, 0xD4] (StorePre 0x103564 3 (fun s => AddrMode.addr (.base 5 (.d8 0xd4)) s (0x103564 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x103564 6 (.base 5 (.d8 0xd4)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x103564 6 (.base 5 (.d8 0xd4))).toInstrSpec (mov_m32_r32_low_effect_step 0x103564 6 (.base 5 (.d8 0xd4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x103567 [0x41, 0xB9, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103567) (movR32Imm32Effect 0x103567 6 9 0x1)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x103567 6 9 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x103567 0x41 0xb9 (by decide) (by decide) 0x1) pre_rip
  have f25 : InstrSpec 0x10356d [0x4C, 0x0F, 0x45, 0xC8] (fun s => s.RIP = 0x10356d) (atFlags (condHolds 5) (cmovR64R64Effect 0x10356d 4 9 0))
      [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 9, .rip] :=
    (cmovR64R64Effect_footprint 0x10356d 4 9 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10356d 5 0x4c (by decide) 0xc8 (by decide) c)) pre_rip
  have f26 : InstrSpec 0x103571 [0x4D, 0x01, 0xE9] (fun s => s.RIP = 0x103571) (addR64R64Effect 0x103571 9 13)
      [.gpr 9, .gpr 13] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103571 9 13).toInstrSpec (add_r64_r64_effect_step 0x103571 0x4d 0xe9 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x103574 [0x41, 0xF7, 0xC7, 0x00, 0x00, 0x80, 0x00] (fun s => s.RIP = 0x103574) (testR32Imm32Effect 0x103574 7 15 0x800000)
      [.gpr 15] [] [.flags, .rip] :=
    (testR32Imm32Effect_footprint 0x103574 7 15 0x800000).toInstrSpec (test_r32_imm32_rex_effect_step 0x103574 0x41 0xc7 0x800000 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10357b [0x48, 0x89, 0x4D, 0xB8] (StorePre 0x10357b 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x10357b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10357b 1 (.base 5 (.d8 0xb8)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x10357b 1 (.base 5 (.d8 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x10357b 0x48 (by decide) 1 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10355c) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 94), (7, 7), (8, 8), (9, 9), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103561) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f22 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 9), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103564) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 9), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103567) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 99), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10356d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 101), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103571) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 103), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103574) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 103), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 105), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10357b) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 103), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 105), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10357f) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 108) (jcc_rel8_effect_step 0x10357f 5 0x5b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l103520 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103520 bytes_l103520) (entryMap (live .l103520))
      30 0x103520 bytes_l103520 b_l103520 := by
  have f0 : InstrSpec 0x103520 [0x55] (PushPre 0x103520 1) (pushR64Effect 0x103520 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103520 1 5).toInstrSpec (push_r64_effect_step 0x103520 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x103521 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x103521) (movR64R64Effect 0x103521 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x103521 5 4).toInstrSpec (mov_r64_r64_effect_step 0x103521 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103524 [0x41, 0x57] (PushPre 0x103524 2) (pushR64Effect 0x103524 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103524 2 15).toInstrSpec (push_r64_rex_effect_step 0x103524 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x103526 [0x41, 0x56] (PushPre 0x103526 2) (pushR64Effect 0x103526 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103526 2 14).toInstrSpec (push_r64_rex_effect_step 0x103526 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x103528 [0x41, 0x55] (PushPre 0x103528 2) (pushR64Effect 0x103528 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103528 2 13).toInstrSpec (push_r64_rex_effect_step 0x103528 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10352a [0x41, 0x54] (PushPre 0x10352a 2) (pushR64Effect 0x10352a 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10352a 2 12).toInstrSpec (push_r64_rex_effect_step 0x10352a 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10352c [0x53] (PushPre 0x10352c 1) (pushR64Effect 0x10352c 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10352c 1 3).toInstrSpec (push_r64_effect_step 0x10352c 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x10352d [0x48, 0x83, 0xEC, 0x48] (fun s => s.RIP = 0x10352d) (subR64Imm8Effect 0x10352d 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10352d 4 0x48).toInstrSpec (sub_r64_imm8_effect_step 0x10352d 0x48 0xec 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x103531 [0x4D, 0x89, 0xCD] (fun s => s.RIP = 0x103531) (movR64R64Effect 0x103531 13 9)
      [.gpr 9] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x103531 13 9).toInstrSpec (mov_r64_r64_effect_step 0x103531 0x4d 0xcd (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x103534 [0x4C, 0x89, 0x45, 0xC0] (StorePre 0x103534 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x103534 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103534 8 (.base 5 (.d8 0xc0)))
      [.gpr 8, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x103534 8 (.base 5 (.d8 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x103534 0x4c (by decide) 0 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x103538 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x103538) (movR64R64Effect 0x103538 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103538 14 2).toInstrSpec (mov_r64_r64_effect_step 0x103538 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10353b [0x49, 0x89, 0xFC] (fun s => s.RIP = 0x10353b) (movR64R64Effect 0x10353b 12 7)
      [.gpr 7] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10353b 12 7).toInstrSpec (mov_r64_r64_effect_step 0x10353b 0x49 0xfc (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10353e [0x44, 0x8B, 0x7F, 0x10] (LoadPre 0x10353e (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x10353e + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x10353e 15 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x10353e 15 (.base 7 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x10353e 0x44 (by decide) 7 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x103542 [0x44, 0x89, 0xF8] (fun s => s.RIP = 0x103542) (movR32R32Effect 0x103542 3 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x103542 3 0 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x103542 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x103545 [0x25, 0x00, 0x00, 0x20, 0x00] (fun s => s.RIP = 0x103545) (andEaxImm32Effect 0x103545 0x200000)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x103545 0x200000).toInstrSpec (and_eax_imm32_effect_step 0x103545 0x200000) pre_rip
  have f15 : InstrSpec 0x10354a [0x83, 0xF8, 0x01] (fun s => s.RIP = 0x10354a) (cmpR32Imm8Effect 0x10354a 3 0 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x10354a 3 0 0x1).toInstrSpec (cmp_r32_imm8_effect_step 0x10354a 0xf8 0x1 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10354d [0xBA, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10354d) (movR32Imm32Effect 0x10354d 5 2 0x0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10354d 5 2 0x0).toInstrSpec (mov_r32_imm32_effect_step 0x10354d 0xba (by decide) 0x0) pre_rip
  have f17 : InstrSpec 0x103552 [0x19, 0xD2] (fun s => s.RIP = 0x103552) (atFlags StatusFlags.CF (sbbR32R32Effect 0x103552 2 2 2))
      [.gpr 2, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (sbbR32R32Effect_footprint 0x103552 2 2 2).toInstrSpec (StepEffect.atFlags fun c => (sbb_r32_r32_effect_step 0x103552 0xd2 c (by decide))) pre_rip
  have f18 : InstrSpec 0x103554 [0x83, 0xCA, 0x2B] (fun s => s.RIP = 0x103554) (orR32Imm8Effect 0x103554 3 2 0x2b)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (orR32Imm8Effect_footprint 0x103554 3 2 0x2b).toInstrSpec (or_r32_imm8_effect_step 0x103554 0xca 0x2b (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x103557 [0xC1, 0xE8, 0x15] (fun s => s.RIP = 0x103557) (shrR32Effect 0x103557 3 0 21)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x103557 3 0 21).toInstrSpec (shr_r32_imm8_effect_step 0x103557 0xe8 0x15 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103521) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103524) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103526) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103528) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10352a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10352c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10352d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103531) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 69), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103534) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 69), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103538) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 69), (14, 72), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10353b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 74), (13, 69), (14, 72), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10353e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103542) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103545) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10354a) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 80), (1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (16, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10354d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 80), (1, 1), (2, 84), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (16, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103552) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 80), (1, 1), (2, 86), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103554) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 80), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103557) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10355a) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l103520_1 code

theorem block_l103520 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103520 :=
  Rest.liftedBlock (rest_l103520 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103520 x hx)

theorem rest_l103581 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103581 bytes_l103581) (entryMap (live .l103581))
      4 0x103581 bytes_l103581 b_l103581 := by
  have f0 : InstrSpec 0x103581 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x103581) (xorR32R32Effect 0x103581 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103581 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x103581 0x45 0xf6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103584 [0x41, 0x0F, 0xB7, 0x5C, 0x24, 0x14] (LoadPre 0x103584 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x14)) s (0x103584 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x103584 6 3 (.sib 12 none 0 (.d8 0x14)))
      [.gpr 12] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x103584 6 3 (.sib 12 none 0 (.d8 0x14))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x103584 0x41 (by decide) 3 (.sib 12 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10358a [0x49, 0x39, 0xD9] (fun s => s.RIP = 0x10358a) (cmpR64R64Effect 0x10358a 9 3)
      [.gpr 9, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x10358a 9 3).toInstrSpec (cmp_r64_r64_effect_step 0x10358a 0x49 0xd9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103584) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 55), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10358a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 55), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10358d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x10358d 2 0x104) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103581 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103581 :=
  Rest.liftedBlock (rest_l103581 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103581 x hx)

theorem rest_l103593 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103593 bytes_l103593) (entryMap (live .l103593))
      8 0x103593 bytes_l103593 b_l103593 := by
  have f0 : InstrSpec 0x103593 [0x4D, 0x8B, 0x3C, 0x24] (LoadPre 0x103593 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x103593 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103593 15 (.sib 12 none 0 .none))
      [.gpr 12] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x103593 15 (.sib 12 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x103593 0x4d (by decide) 7 (.sib 12 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103597 [0x4D, 0x8B, 0x64, 0x24, 0x08] (LoadPre 0x103597 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x103597 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103597 12 (.sib 12 none 0 (.d8 0x8)))
      [.gpr 12] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x103597 12 (.sib 12 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x103597 0x4d (by decide) 4 (.sib 12 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10359c [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x10359c) (movR64R64Effect 0x10359c 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10359c 7 15).toInstrSpec (mov_r64_r64_effect_step 0x10359c 0x4c 0xff (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10359f [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x10359f) (movR64R64Effect 0x10359f 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10359f 6 12).toInstrSpec (mov_r64_r64_effect_step 0x10359f 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1035a2 [0x8B, 0x55, 0xD4] (LoadPre 0x1035a2 (fun s => AddrMode.addr (.base 5 (.d8 0xd4)) s (0x1035a2 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1035a2 2 (.base 5 (.d8 0xd4)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1035a2 2 (.base 5 (.d8 0xd4))).toInstrSpec (mov_r32_m32_low_effect_step 0x1035a2 2 (.base 5 (.d8 0xd4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1035a5 [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x1035a5) (movR64R64Effect 0x1035a5 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1035a5 1 14).toInstrSpec (mov_r64_r64_effect_step 0x1035a5 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1035a8 [0x4C, 0x8B, 0x45, 0xB8] (LoadPre 0x1035a8 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x1035a8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1035a8 8 (.base 5 (.d8 0xb8)))
      [.gpr 5] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1035a8 8 (.base 5 (.d8 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x1035a8 0x4c (by decide) 0 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1035ac [0xE8, 0x8F, 0x07, 0x00, 0x00] (PushPre 0x1035ac 5) (callEffect (fun _ => 0x103d40) 0x1035b1)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1035ac 0x103d40 0x1035b1).toInstrSpec (call_rel32_effect_step 0x1035ac 0x78f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103597) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10359c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 57), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10359f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035a2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035a5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035a8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (8, 65), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035ac) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 63), (2, 61), (3, 3), (4, 67), (5, 5), (6, 59), (7, 57), (8, 65), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d40) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l103593 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103593 :=
  Rest.liftedBlock (rest_l103593 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103593 x hx)

theorem rest_l1035b1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1035b1 bytes_l1035b1) (entryMap (live .l1035b1))
      4 0x1035b1 bytes_l1035b1 b_l1035b1 := by
  have f0 : InstrSpec 0x1035b1 [0x89, 0xC1] (fun s => s.RIP = 0x1035b1) (movR32R32Effect 0x1035b1 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1035b1 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1035b1 0xc1 (by decide)) pre_rip
  have f1 : InstrSpec 0x1035b3 [0xB0, 0x01] (fun s => s.RIP = 0x1035b3) (movR8Imm8Effect 0x1035b3 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x1035b3 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x1035b3 0xb0 (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x1035b5 [0x84, 0xC9] (fun s => s.RIP = 0x1035b5) (testR8R8Effect 0x1035b5 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1035b5 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x1035b5 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035b3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035b5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035b7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x1035b7 5 0x26b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1035b1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1035b1 :=
  Rest.liftedBlock (rest_l1035b1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1035b1 x hx)

theorem rest_l1035bd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1035bd bytes_l1035bd) (entryMap (live .l1035bd))
      11 0x1035bd bytes_l1035bd b_l1035bd := by
  have f0 : InstrSpec 0x1035bd [0x49, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x1035bd (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x1035bd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1035bd 0 (.sib 12 none 0 (.d8 0x18)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1035bd 0 (.sib 12 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1035bd 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1035c2 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x1035c2) (movR64R64Effect 0x1035c2 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1035c2 7 15).toInstrSpec (mov_r64_r64_effect_step 0x1035c2 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1035c5 [0x48, 0x8B, 0x75, 0xC0] (LoadPre 0x1035c5 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x1035c5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1035c5 6 (.base 5 (.d8 0xc0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1035c5 6 (.base 5 (.d8 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x1035c5 0x48 (by decide) 6 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1035c9 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x1035c9) (movR64R64Effect 0x1035c9 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1035c9 2 13).toInstrSpec (mov_r64_r64_effect_step 0x1035c9 0x4c 0xea (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1035cc [0x48, 0x83, 0xC4, 0x48] (fun s => s.RIP = 0x1035cc) (addR64Imm8Effect 0x1035cc 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1035cc 4 0x48).toInstrSpec (add_r64_imm8_effect_step 0x1035cc 0x48 0xc4 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1035d0 [0x5B] (PopPre 0x1035d0) (popR64Effect 0x1035d0 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1035d0 1 3).toInstrSpec (pop_r64_effect_step 0x1035d0 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1035d1 [0x41, 0x5C] (PopPre 0x1035d1) (popR64Effect 0x1035d1 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1035d1 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1035d1 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1035d3 [0x41, 0x5D] (PopPre 0x1035d3) (popR64Effect 0x1035d3 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1035d3 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1035d3 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x1035d5 [0x41, 0x5E] (PopPre 0x1035d5) (popR64Effect 0x1035d5 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1035d5 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1035d5 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x1035d7 [0x41, 0x5F] (PopPre 0x1035d7) (popR64Effect 0x1035d7 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1035d7 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1035d7 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x1035d9 [0x5D] (PopPre 0x1035d9) (popR64Effect 0x1035d9 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1035d9 1 5).toInstrSpec (pop_r64_effect_step 0x1035d9 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x1035c2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x1035c5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x1035c9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x1035cc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(4, 57), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x1035d0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(4, 59), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x1035d1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(4, 61), (5, 5), (13, 13), (15, 15)]) (p' := 0x1035d3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(4, 63), (5, 5), (15, 15)]) (p' := 0x1035d5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(4, 65), (5, 5), (15, 15)]) (p' := 0x1035d7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(4, 67), (5, 5)]) (p' := 0x1035d9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := []) (p' := 0x1035da) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l1035bd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1035bd :=
  Rest.liftedBlock (rest_l1035bd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1035bd x hx)

theorem rest_l1035dc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1035dc bytes_l1035dc) (entryMap (live .l1035dc))
      2 0x1035dc bytes_l1035dc b_l1035dc := by
  have f0 : InstrSpec 0x1035dc [0x48, 0x83, 0xF9, 0x20] (fun s => s.RIP = 0x1035dc) (cmpR64Imm8Effect 0x1035dc 1 0x20)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1035dc 1 0x20).toInstrSpec (cmp_r64_imm8_effect_step 0x1035dc 0x48 0xf9 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035e0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1035e0 3 0x18) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1035dc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1035dc :=
  Rest.liftedBlock (rest_l1035dc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1035dc x hx)

theorem rest_l1035e2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1035e2 bytes_l1035e2) (entryMap (live .l1035e2))
      2 0x1035e2 bytes_l1035e2 b_l1035e2 := by
  have f0 : InstrSpec 0x1035e2 [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x1035e2) (testR64R64Effect 0x1035e2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1035e2 1 1).toInstrSpec (test_r64_r64_effect_step 0x1035e2 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035e5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1035e5 4 0x27) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1035e2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1035e2 :=
  Rest.liftedBlock (rest_l1035e2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1035e2 x hx)

theorem rest_l1035e7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1035e7 bytes_l1035e7) (entryMap (live .l1035e7))
      4 0x1035e7 bytes_l1035e7 b_l1035e7 := by
  have f0 : InstrSpec 0x1035e7 [0x41, 0x89, 0xCA] (fun s => s.RIP = 0x1035e7) (movR32R32Effect 0x1035e7 3 10 1)
      [.gpr 1] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x1035e7 3 10 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x1035e7 0x41 0xca (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1035ea [0x41, 0x83, 0xE2, 0x03] (fun s => s.RIP = 0x1035ea) (andR32Imm8Effect 0x1035ea 4 10 0x3)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1035ea 4 10 0x3).toInstrSpec (and_r32_imm8_rex_effect_step 0x1035ea 0x41 0xe2 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1035ee [0x48, 0x83, 0xF9, 0x04] (fun s => s.RIP = 0x1035ee) (cmpR64Imm8Effect 0x1035ee 1 0x4)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1035ee 1 0x4).toInstrSpec (cmp_r64_imm8_effect_step 0x1035ee 0x48 0xf9 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035ea) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035ee) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035f2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x1035f2 3 0x1e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1035e7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1035e7 :=
  Rest.liftedBlock (rest_l1035e7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1035e7 x hx)

theorem rest_l1035f4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1035f4 bytes_l1035f4) (entryMap (live .l1035f4))
      3 0x1035f4 bytes_l1035f4 b_l1035f4 := by
  have f0 : InstrSpec 0x1035f4 [0x31, 0xD2] (fun s => s.RIP = 0x1035f4) (xorR32R32Effect 0x1035f4 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1035f4 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x1035f4 0xd2 (by decide)) pre_rip
  have f1 : InstrSpec 0x1035f6 [0x31, 0xC0] (fun s => s.RIP = 0x1035f6) (xorR32R32Effect 0x1035f6 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1035f6 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x1035f6 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035f6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035f8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x1035f8 0x6e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1035f4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1035f4 :=
  Rest.liftedBlock (rest_l1035f4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1035f4 x hx)

theorem rest_l1035fa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1035fa bytes_l1035fa) (entryMap (live .l1035fa))
      4 0x1035fa bytes_l1035fa b_l1035fa := by
  have f0 : InstrSpec 0x1035fa [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1035fa) (movR64R64Effect 0x1035fa 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1035fa 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1035fa 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1035fd [0x48, 0x89, 0xCE] (fun s => s.RIP = 0x1035fd) (movR64R64Effect 0x1035fd 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1035fd 6 1).toInstrSpec (mov_r64_r64_effect_step 0x1035fd 0x48 0xce (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103600 [0x4C, 0x89, 0xCB] (fun s => s.RIP = 0x103600) (movR64R64Effect 0x103600 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x103600 3 9).toInstrSpec (mov_r64_r64_effect_step 0x103600 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103603 [0xFF, 0x15, 0x17, 0xDC, 0x0F, 0x00] (GoesTo (CallMemPre 0x103603 (.rip 0xfdc17)) (callEffect (callMemPtr 0x103603 (.rip 0xfdc17)) (0x103603 + BitVec.ofNat 64 (callMemLen (.rip 0xfdc17)))) 0x1038b0) (callEffect (callMemPtr 0x103603 (.rip 0xfdc17)) (0x103603 + BitVec.ofNat 64 (callMemLen (.rip 0xfdc17))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x103603 (.rip 0xfdc17)).toInstrSpec (call_m64_effect_step 0x103603 (.rip 0xfdc17) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x1038b0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (4, 4), (5, 5), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035fd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103600) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 57), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103603) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 57), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038b0) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1035fa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1035fa :=
  Rest.liftedBlock (rest_l1035fa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1035fa x hx)

theorem rest_l103609 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103609 bytes_l103609) (entryMap (live .l103609))
      2 0x103609 bytes_l103609 b_l103609 := by
  have f0 : InstrSpec 0x103609 [0x49, 0x89, 0xD9] (fun s => s.RIP = 0x103609) (movR64R64Effect 0x103609 9 3)
      [.gpr 3] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x103609 9 3).toInstrSpec (mov_r64_r64_effect_step 0x103609 0x49 0xd9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10360c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x10360c 0x77 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103609 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103609 :=
  Rest.liftedBlock (rest_l103609 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103609 x hx)

theorem rest_l10360e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10360e bytes_l10360e) (entryMap (live .l10360e))
      2 0x10360e bytes_l10360e b_l10360e := by
  have f0 : InstrSpec 0x10360e [0x31, 0xC0] (fun s => s.RIP = 0x10360e) (xorR32R32Effect 0x10360e 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10360e 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x10360e 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103610) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x103610 0x73 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10360e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10360e :=
  Rest.liftedBlock (rest_l10360e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10360e x hx)

theorem rest_l103612 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103612 bytes_l103612) (entryMap (live .l103612))
      5 0x103612 bytes_l103612 b_l103612 := by
  have f0 : InstrSpec 0x103612 [0x89, 0xCE] (fun s => s.RIP = 0x103612) (movR32R32Effect 0x103612 2 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x103612 2 6 1).toInstrSpec (mov_r32_r32_effect_step 0x103612 0xce (by decide)) pre_rip
  have f1 : InstrSpec 0x103614 [0x83, 0xE6, 0x1C] (fun s => s.RIP = 0x103614) (andR32Imm8Effect 0x103614 3 6 0x1c)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x103614 3 6 0x1c).toInstrSpec (and_r32_imm8_effect_step 0x103614 0xe6 0x1c (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103617 [0x31, 0xD2] (fun s => s.RIP = 0x103617) (xorR32R32Effect 0x103617 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103617 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x103617 0xd2 (by decide)) pre_rip
  have f3 : InstrSpec 0x103619 [0x31, 0xC0] (fun s => s.RIP = 0x103619) (xorR32R32Effect 0x103619 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103619 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x103619 0xc0 (by decide)) pre_rip
  have f4 : InstrSpec 0x10361b [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x10361b) (fun _ => nopEffect 0x10361b 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10361b 5).toInstrSpec (nop_m_effect_step 0x10361b [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103614) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103617) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103619) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 57), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10361b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 1), (2, 57), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103620) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l103612 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103612 :=
  Rest.liftedBlock (rest_l103612 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103612 x hx)

theorem rest_l103620 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103620 bytes_l103620) (entryMap (live .l103620))
      19 0x103620 bytes_l103620 b_l103620 := by
  have f0 : InstrSpec 0x103620 [0x31, 0xFF] (fun s => s.RIP = 0x103620) (xorR32R32Effect 0x103620 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103620 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x103620 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x103622 [0x41, 0x80, 0x3C, 0x16, 0xC0] (LoadPre 0x103622 (fun s => AddrMode.addr (.sib 14 (some 2) 0 .none) s (0x103622 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103622 5 (.sib 14 (some 2) 0 .none) 0xc0)
      [.gpr 14, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x103622 5 (.sib 14 (some 2) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x103622 0x41 (by decide) (.sib 14 (some 2) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103627 [0x40, 0x0F, 0x9D, 0xC7] (fun s => s.RIP = 0x103627) (atFlags (condHolds 13) (setccR8Effect 0x103627 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x103627 4 7 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x103627 13 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x10362b [0x48, 0x01, 0xC7] (fun s => s.RIP = 0x10362b) (addR64R64Effect 0x10362b 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10362b 7 0).toInstrSpec (add_r64_r64_effect_step 0x10362b 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10362e [0x31, 0xC0] (fun s => s.RIP = 0x10362e) (xorR32R32Effect 0x10362e 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10362e 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x10362e 0xc0 (by decide)) pre_rip
  have f5 : InstrSpec 0x103630 [0x41, 0x80, 0x7C, 0x16, 0x01, 0xC0] (LoadPre 0x103630 (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x1)) s (0x103630 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x103630 6 (.sib 14 (some 2) 0 (.d8 0x1)) 0xc0)
      [.gpr 14, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x103630 6 (.sib 14 (some 2) 0 (.d8 0x1)) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x103630 0x41 (by decide) (.sib 14 (some 2) 0 (.d8 0x1)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x103636 [0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x103636) (atFlags (condHolds 13) (setccR8Effect 0x103636 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x103636 3 0 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x103636 13 0xc0 (by decide) (by decide) c)) pre_rip
  have f7 : InstrSpec 0x103639 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x103639) (xorR32R32Effect 0x103639 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103639 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x103639 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10363c [0x41, 0x80, 0x7C, 0x16, 0x02, 0xC0] (LoadPre 0x10363c (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x2)) s (0x10363c + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x10363c 6 (.sib 14 (some 2) 0 (.d8 0x2)) 0xc0)
      [.gpr 14, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x10363c 6 (.sib 14 (some 2) 0 (.d8 0x2)) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x10363c 0x41 (by decide) (.sib 14 (some 2) 0 (.d8 0x2)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x103642 [0x41, 0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x103642) (atFlags (condHolds 13) (setccR8Effect 0x103642 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x103642 4 8 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x103642 13 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  have f10 : InstrSpec 0x103646 [0x49, 0x01, 0xC0] (fun s => s.RIP = 0x103646) (addR64R64Effect 0x103646 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103646 8 0).toInstrSpec (add_r64_r64_effect_step 0x103646 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x103649 [0x49, 0x01, 0xF8] (fun s => s.RIP = 0x103649) (addR64R64Effect 0x103649 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103649 8 7).toInstrSpec (add_r64_r64_effect_step 0x103649 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10364c [0x31, 0xC0] (fun s => s.RIP = 0x10364c) (xorR32R32Effect 0x10364c 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10364c 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x10364c 0xc0 (by decide)) pre_rip
  have f13 : InstrSpec 0x10364e [0x41, 0x80, 0x7C, 0x16, 0x03, 0xC0] (LoadPre 0x10364e (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x3)) s (0x10364e + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x10364e 6 (.sib 14 (some 2) 0 (.d8 0x3)) 0xc0)
      [.gpr 14, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x10364e 6 (.sib 14 (some 2) 0 (.d8 0x3)) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x10364e 0x41 (by decide) (.sib 14 (some 2) 0 (.d8 0x3)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x103654 [0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x103654) (atFlags (condHolds 13) (setccR8Effect 0x103654 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x103654 3 0 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x103654 13 0xc0 (by decide) (by decide) c)) pre_rip
  have f15 : InstrSpec 0x103657 [0x4C, 0x01, 0xC0] (fun s => s.RIP = 0x103657) (addR64R64Effect 0x103657 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103657 0 8).toInstrSpec (add_r64_r64_effect_step 0x103657 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10365a [0x48, 0x83, 0xC2, 0x04] (fun s => s.RIP = 0x10365a) (addR64Imm8Effect 0x10365a 2 0x4)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10365a 2 0x4).toInstrSpec (add_r64_imm8_effect_step 0x10365a 0x48 0xc2 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10365e [0x48, 0x39, 0xD6] (fun s => s.RIP = 0x10365e) (cmpR64R64Effect 0x10365e 6 2)
      [.gpr 6, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x10365e 6 2).toInstrSpec (cmp_r64_r64_effect_step 0x10365e 0x48 0xd6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103622) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103627) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10362b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10362e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103630) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 64), (21, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103636) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 64), (21, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103639) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 69), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10363c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f8 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f8 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 69), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 71), (21, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103642) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 71), (21, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103646) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 76), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103649) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10364c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10364e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f13 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f13 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 80), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 82), (21, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103654) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 82), (21, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103657) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (2, 2), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10365a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 87), (2, 89), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10365e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 87), (2, 89), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103661) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 93) (jcc_rel8_effect_step 0x103661 5 0xbd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103620 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103620 :=
  Rest.liftedBlock (rest_l103620 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103620 x hx)

theorem rest_l103663 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103663 bytes_l103663) (entryMap (live .l103663))
      2 0x103663 bytes_l103663 b_l103663 := by
  have f0 : InstrSpec 0x103663 [0x4D, 0x85, 0xD2] (fun s => s.RIP = 0x103663) (testR64R64Effect 0x103663 10 10)
      [.gpr 10, .gpr 10] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x103663 10 10).toInstrSpec (test_r64_r64_effect_step 0x103663 0x4d 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103666) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x103666 4 0x1d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103663 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103663 :=
  Rest.liftedBlock (rest_l103663 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103663 x hx)

theorem rest_l103668 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103668 bytes_l103668) (entryMap (live .l103668))
      3 0x103668 bytes_l103668 b_l103668 := by
  have f0 : InstrSpec 0x103668 [0x4C, 0x01, 0xF2] (fun s => s.RIP = 0x103668) (addR64R64Effect 0x103668 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103668 2 14).toInstrSpec (add_r64_r64_effect_step 0x103668 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10366b [0x31, 0xF6] (fun s => s.RIP = 0x10366b) (xorR32R32Effect 0x10366b 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10366b 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x10366b 0xf6 (by decide)) pre_rip
  have f2 : InstrSpec 0x10366d [0x0F, 0x1F, 0x00] (fun s => s.RIP = 0x10366d) (fun _ => nopEffect 0x10366d 3)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10366d 3).toInstrSpec (nop_m_effect_step 0x10366d [] (by decide) (by decide) (.base 0 .none) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10366b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 53), (4, 4), (5, 5), (6, 55), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10366d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 53), (4, 4), (5, 5), (6, 55), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103670) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l103668 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103668 :=
  Rest.liftedBlock (rest_l103668 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103668 x hx)

theorem rest_l103670 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103670 bytes_l103670) (entryMap (live .l103670))
      7 0x103670 bytes_l103670 b_l103670 := by
  have f0 : InstrSpec 0x103670 [0x31, 0xFF] (fun s => s.RIP = 0x103670) (xorR32R32Effect 0x103670 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103670 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x103670 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x103672 [0x80, 0x3C, 0x32, 0xC0] (LoadPre 0x103672 (fun s => AddrMode.addr (.sib 2 (some 6) 0 .none) s (0x103672 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x103672 4 (.sib 2 (some 6) 0 .none) 0xc0)
      [.gpr 2, .gpr 6] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x103672 4 (.sib 2 (some 6) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x103672 (.sib 2 (some 6) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103676 [0x40, 0x0F, 0x9D, 0xC7] (fun s => s.RIP = 0x103676) (atFlags (condHolds 13) (setccR8Effect 0x103676 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x103676 4 7 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x103676 13 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x10367a [0x48, 0x01, 0xF8] (fun s => s.RIP = 0x10367a) (addR64R64Effect 0x10367a 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10367a 0 7).toInstrSpec (add_r64_r64_effect_step 0x10367a 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10367d [0x48, 0xFF, 0xC6] (fun s => s.RIP = 0x10367d) (incR64Effect 0x10367d 6)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (incR64Effect_footprint 0x10367d 6).toInstrSpec (inc_r64_effect_step 0x10367d 0x48 0xc6 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x103680 [0x49, 0x39, 0xF2] (fun s => s.RIP = 0x103680) (cmpR64R64Effect 0x103680 10 6)
      [.gpr 10, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103680 10 6).toInstrSpec (cmp_r64_r64_effect_step 0x103680 0x49 0xf2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103672) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103676) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10367a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (2, 2), (4, 4), (5, 5), (6, 6), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10367d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (2, 2), (4, 4), (5, 5), (6, 62), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103680) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 60), (2, 2), (4, 4), (5, 5), (6, 62), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103683) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x103683 5 0xeb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103670 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103670 :=
  Rest.liftedBlock (rest_l103670 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103670 x hx)

theorem rest_l103685 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103685 bytes_l103685) (entryMap (live .l103685))
      4 0x103685 bytes_l103685 b_l103685 := by
  have f0 : InstrSpec 0x103685 [0x49, 0x01, 0xC1] (fun s => s.RIP = 0x103685) (addR64R64Effect 0x103685 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x103685 9 0).toInstrSpec (add_r64_r64_effect_step 0x103685 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103688 [0x41, 0x0F, 0xB7, 0x5C, 0x24, 0x14] (LoadPre 0x103688 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x14)) s (0x103688 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x103688 6 3 (.sib 12 none 0 (.d8 0x14)))
      [.gpr 12] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x103688 6 3 (.sib 12 none 0 (.d8 0x14))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x103688 0x41 (by decide) 3 (.sib 12 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10368e [0x49, 0x39, 0xD9] (fun s => s.RIP = 0x10368e) (cmpR64R64Effect 0x10368e 9 3)
      [.gpr 9, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x10368e 9 3).toInstrSpec (cmp_r64_r64_effect_step 0x10368e 0x49 0xd9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (5, 5), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103688) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 55), (4, 4), (5, 5), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10368e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 55), (4, 4), (5, 5), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103691) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x103691 3 0xfffffefc) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103685 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103685 :=
  Rest.liftedBlock (rest_l103685 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103685 x hx)

theorem rest_l103697 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103697 bytes_l103697) (entryMap (live .l103697))
      4 0x103697 bytes_l103697 b_l103697 := by
  have f0 : InstrSpec 0x103697 [0x41, 0xF7, 0xC7, 0x00, 0x00, 0x00, 0x01] (fun s => s.RIP = 0x103697) (testR32Imm32Effect 0x103697 7 15 0x1000000)
      [.gpr 15] [] [.flags, .rip] :=
    (testR32Imm32Effect_footprint 0x103697 7 15 0x1000000).toInstrSpec (test_r32_imm32_rex_effect_step 0x103697 0x41 0xc7 0x1000000 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10369e [0x4C, 0x89, 0x6D, 0xA8] (StorePre 0x10369e 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x10369e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10369e 13 (.base 5 (.d8 0xa8)))
      [.gpr 13, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x10369e 13 (.base 5 (.d8 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x10369e 0x4c (by decide) 5 (.base 5 (.d8 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1036a2 [0x4C, 0x89, 0x4D, 0xA0] (StorePre 0x1036a2 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa0)) s (0x1036a2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1036a2 9 (.base 5 (.d8 0xa0)))
      [.gpr 9, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1036a2 9 (.base 5 (.d8 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x1036a2 0x4c (by decide) 1 (.base 5 (.d8 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10369e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036a2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036a6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1036a6 5 0x28) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103697 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103697 :=
  Rest.liftedBlock (rest_l103697 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103697 x hx)

theorem rest_l1036a8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1036a8 bytes_l1036a8) (entryMap (live .l1036a8))
      9 0x1036a8 bytes_l1036a8 b_l1036a8 := by
  have f0 : InstrSpec 0x1036a8 [0x89, 0xDA] (fun s => s.RIP = 0x1036a8) (movR32R32Effect 0x1036a8 2 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x1036a8 2 2 3).toInstrSpec (mov_r32_r32_effect_step 0x1036a8 0xda (by decide)) pre_rip
  have f1 : InstrSpec 0x1036aa [0x44, 0x29, 0xCA] (fun s => s.RIP = 0x1036aa) (subR32R32Effect 0x1036aa 3 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (subR32R32Effect_footprint 0x1036aa 3 2 9).toInstrSpec (sub_r32_r32_rex_effect_step 0x1036aa 0x44 0xca (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1036ad [0x44, 0x89, 0xF8] (fun s => s.RIP = 0x1036ad) (movR32R32Effect 0x1036ad 3 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1036ad 3 0 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x1036ad 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1036b0 [0xC1, 0xE8, 0x1D] (fun s => s.RIP = 0x1036b0) (shrR32Effect 0x1036b0 3 0 29)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x1036b0 3 0 29).toInstrSpec (shr_r32_imm8_effect_step 0x1036b0 0xe8 0x1d (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1036b3 [0x83, 0xE0, 0x03] (fun s => s.RIP = 0x1036b3) (andR32Imm8Effect 0x1036b3 3 0 0x3)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1036b3 3 0 0x3).toInstrSpec (and_r32_imm8_effect_step 0x1036b3 0xe0 0x3 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1036b6 [0x48, 0x8D, 0x0D, 0x63, 0xD8, 0x0F, 0x00] (fun s => s.RIP = 0x1036b6) (leaR64Effect 0x1036b6 1 (.rip 0xfd863))
      [] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1036b6 1 (.rip 0xfd863)).toInstrSpec (lea_r64_effect_step 0x1036b6 0x48 (by decide) 1 (.rip 0xfd863) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1036bd [0x48, 0x63, 0x04, 0x81] (LoadPre 0x1036bd (fun s => AddrMode.addr (.sib 1 (some 0) 2 .none) s (0x1036bd + BitVec.ofNat 64 4)) 4) (movsxdR64M32Effect 0x1036bd 4 0 (.sib 1 (some 0) 2 .none))
      [.gpr 1, .gpr 0] [] [.reg 0, .rip] :=
    (movsxdR64M32Effect_footprint 0x1036bd 4 0 (.sib 1 (some 0) 2 .none)).toInstrSpec (movsxd_r64_m32_effect_step 0x1036bd 0x48 (by decide) 0 (.sib 1 (some 0) 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1036c1 [0x48, 0x01, 0xC8] (fun s => s.RIP = 0x1036c1) (addR64R64Effect 0x1036c1 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1036c1 0 1).toInstrSpec (add_r64_r64_effect_step 0x1036c1 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1036c4 [0x89, 0x55, 0xB4] (StorePre 0x1036c4 3 (fun s => AddrMode.addr (.base 5 (.d8 0xb4)) s (0x1036c4 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1036c4 2 (.base 5 (.d8 0xb4)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1036c4 2 (.base 5 (.d8 0xb4))).toInstrSpec (mov_m32_r32_low_effect_step 0x1036c4 2 (.base 5 (.d8 0xb4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x1036aa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x1036ad) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x1036b0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x1036b3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x1036b6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x1036bd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 63), (2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x1036c1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(1, 63), (2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x1036c4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(1, 63), (2, 55), (3, 3), (5, 5), (9, 9), (15, 15)]) (p' := 0x1036c7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l1036a8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1036a8 :=
  Rest.liftedBlock (rest_l1036a8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1036a8 x hx)

theorem rest_l1036d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1036d0 bytes_l1036d0) (entryMap (live .l1036d0))
      13 0x1036d0 bytes_l1036d0 b_l1036d0 := by
  have f0 : InstrSpec 0x1036d0 [0x49, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1036d0 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x1036d0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036d0 0 (.sib 12 none 0 (.d8 0x10)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1036d0 0 (.sib 12 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1036d0 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1036d5 [0x48, 0x89, 0x45, 0xC8] (StorePre 0x1036d5 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x1036d5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1036d5 0 (.base 5 (.d8 0xc8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1036d5 0 (.base 5 (.d8 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x1036d5 0x48 (by decide) 0 (.base 5 (.d8 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1036d9 [0x25, 0x00, 0x00, 0xE0, 0x9F] (fun s => s.RIP = 0x1036d9) (andEaxImm32Effect 0x1036d9 0x9fe00000)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1036d9 0x9fe00000).toInstrSpec (and_eax_imm32_effect_step 0x1036d9 0x9fe00000) pre_rip
  have f3 : InstrSpec 0x1036de [0x0D, 0x30, 0x00, 0x00, 0x20] (fun s => s.RIP = 0x1036de) (orEaxImm32Effect 0x1036de 0x20000030)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orEaxImm32Effect_footprint 0x1036de 0x20000030).toInstrSpec (or_eax_imm32_effect_step 0x1036de 0x20000030) pre_rip
  have f4 : InstrSpec 0x1036e3 [0x41, 0x89, 0x44, 0x24, 0x10] (StorePre 0x1036e3 5 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x1036e3 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1036e3 0 (.sib 12 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 12] [] [.rip] :=
    (movM32R32Effect_footprint 0x1036e3 0 (.sib 12 none 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_effect_step 0x1036e3 0x41 (by decide) 0 (.sib 12 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1036e8 [0x4D, 0x8B, 0x2C, 0x24] (LoadPre 0x1036e8 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x1036e8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1036e8 13 (.sib 12 none 0 .none))
      [.gpr 12] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x1036e8 13 (.sib 12 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1036e8 0x4d (by decide) 5 (.sib 12 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1036ec [0x4D, 0x8B, 0x7C, 0x24, 0x08] (LoadPre 0x1036ec (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x1036ec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036ec 15 (.sib 12 none 0 (.d8 0x8)))
      [.gpr 12] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1036ec 15 (.sib 12 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1036ec 0x4d (by decide) 7 (.sib 12 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1036f1 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x1036f1) (movR64R64Effect 0x1036f1 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1036f1 7 13).toInstrSpec (mov_r64_r64_effect_step 0x1036f1 0x4c 0xef (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1036f4 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x1036f4) (movR64R64Effect 0x1036f4 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1036f4 6 15).toInstrSpec (mov_r64_r64_effect_step 0x1036f4 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1036f7 [0x8B, 0x55, 0xD4] (LoadPre 0x1036f7 (fun s => AddrMode.addr (.base 5 (.d8 0xd4)) s (0x1036f7 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1036f7 2 (.base 5 (.d8 0xd4)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1036f7 2 (.base 5 (.d8 0xd4))).toInstrSpec (mov_r32_m32_low_effect_step 0x1036f7 2 (.base 5 (.d8 0xd4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1036fa [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x1036fa) (movR64R64Effect 0x1036fa 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1036fa 1 14).toInstrSpec (mov_r64_r64_effect_step 0x1036fa 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1036fd [0x4C, 0x8B, 0x45, 0xB8] (LoadPre 0x1036fd (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x1036fd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1036fd 8 (.base 5 (.d8 0xb8)))
      [.gpr 5] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1036fd 8 (.base 5 (.d8 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x1036fd 0x4c (by decide) 0 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x103701 [0xE8, 0x3A, 0x06, 0x00, 0x00] (PushPre 0x103701 5) (callEffect (fun _ => 0x103d40) 0x103706)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103701 0x103d40 0x103706).toInstrSpec (call_rel32_effect_step 0x103701 0x63a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036d5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036d9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036de) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036e3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036e8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 61), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036ec) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036f1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (7, 65), (9, 9), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036f4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036f7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 58), (2, 69), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036fa) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 58), (1, 71), (2, 69), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1036fd) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 58), (1, 71), (2, 69), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (8, 73), (9, 9), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103701) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 58), (1, 71), (2, 69), (3, 3), (4, 75), (5, 5), (6, 67), (7, 65), (8, 73), (9, 9), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103d40) f12 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l1036d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1036d0 :=
  Rest.liftedBlock (rest_l1036d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1036d0 x hx)

theorem rest_l103706 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103706 bytes_l103706) (entryMap (live .l103706))
      4 0x103706 bytes_l103706 b_l103706 := by
  have f0 : InstrSpec 0x103706 [0x89, 0xC1] (fun s => s.RIP = 0x103706) (movR32R32Effect 0x103706 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x103706 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x103706 0xc1 (by decide)) pre_rip
  have f1 : InstrSpec 0x103708 [0xB0, 0x01] (fun s => s.RIP = 0x103708) (movR8Imm8Effect 0x103708 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x103708 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x103708 0xb0 (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x10370a [0x84, 0xC9] (fun s => s.RIP = 0x10370a) (testR8R8Effect 0x10370a 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10370a 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x10370a 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103708) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10370a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10370c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x10370c 5 0x116) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103706 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103706 :=
  Rest.liftedBlock (rest_l103706 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103706 x hx)

theorem rest_l103712 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103712 bytes_l103712) (entryMap (live .l103712))
      3 0x103712 bytes_l103712 b_l103712 := by
  have f0 : InstrSpec 0x103712 [0x2B, 0x5D, 0xA0] (LoadPre 0x103712 (fun s => AddrMode.addr (.base 5 (.d8 0xa0)) s (0x103712 + BitVec.ofNat 64 3)) 4) (subR32M32Effect 0x103712 3 3 (.base 5 (.d8 0xa0)))
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (subR32M32Effect_footprint 0x103712 3 3 (.base 5 (.d8 0xa0))).toInstrSpec (sub_r32_m32_effect_step 0x103712 3 (.base 5 (.d8 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103715 [0xFF, 0xC3] (fun s => s.RIP = 0x103715) (incR32Effect 0x103715 2 3)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (incR32Effect_footprint 0x103715 2 3).toInstrSpec (inc_r32_effect_step 0x103715 0xc3 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103717 [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103717) (fun _ => nopEffect 0x103717 9)
      [] [] [.rip] :=
    (nopEffect_footprint 0x103717 9).toInstrSpec (nop_m_effect_step 0x103717 [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (5, 5), (13, 13)]) (p' := 0x103715) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 55), (5, 5), (13, 13)]) (p' := 0x103717) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 55), (5, 5), (13, 13)]) (p' := 0x103720) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l103712 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103712 :=
  Rest.liftedBlock (rest_l103712 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103712 x hx)

theorem rest_l103720 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103720 bytes_l103720) (entryMap (live .l103720))
      2 0x103720 bytes_l103720 b_l103720 := by
  have f0 : InstrSpec 0x103720 [0x66, 0xFF, 0xCB] (fun s => s.RIP = 0x103720) (decR16Effect 0x103720 3 3)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (decR16Effect_footprint 0x103720 3 3).toInstrSpec (dec_r16_effect_step 0x103720 0xcb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.fresh (n := 53) f0 .ZF (fun _ => rfl) (decR16Effect_fresh 0x103720 3 3 _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(5, 5), (13, 13), (19, 53)]) (p' := 0x103723) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x103723 4 0x12) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103720 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103720 :=
  Rest.liftedBlock (rest_l103720 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103720 x hx)

theorem rest_l103725 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103725 bytes_l103725) (entryMap (live .l103725))
      2 0x103725 bytes_l103725 b_l103725 := by
  have f0 : InstrSpec 0x103725 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x103725) (movR64R64Effect 0x103725 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103725 7 13).toInstrSpec (mov_r64_r64_effect_step 0x103725 0x4c 0xef (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103728 [0xBE, 0x30, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103728) (movR32Imm32Effect 0x103728 5 6 0x30)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x103728 5 6 0x30).toInstrSpec (mov_r32_imm32_effect_step 0x103728 0xbe (by decide) 0x30) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(13, 13)]) (p' := 0x103728) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(13, 13)]) (p' := 0x10372d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l103725 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103725 :=
  Rest.liftedBlock (rest_l103725 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103725 x hx)

theorem rest_l103731 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103731 bytes_l103731) (entryMap (live .l103731))
      2 0x103731 bytes_l103731 b_l103731 := by
  have f0 : InstrSpec 0x103731 [0x84, 0xC0] (fun s => s.RIP = 0x103731) (testR8R8Effect 0x103731 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x103731 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x103731 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103733) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x103733 4 0xeb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103731 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103731 :=
  Rest.liftedBlock (rest_l103731 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103731 x hx)

theorem rest_l103735 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103735 bytes_l103735) (entryMap (live .l103735))
      1 0x103735 bytes_l103735 b_l103735 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x103735 0x6f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103735 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103735 :=
  Rest.liftedBlock (rest_l103735 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103735 x hx)

theorem rest_l103737 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103737 bytes_l103737) (entryMap (live .l103737))
      3 0x103737 bytes_l103737 b_l103737 := by
  have f0 : InstrSpec 0x103737 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x103737) (movR64R64Effect 0x103737 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103737 7 13).toInstrSpec (mov_r64_r64_effect_step 0x103737 0x4c 0xef (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10373a [0x48, 0x8B, 0x75, 0xC0] (LoadPre 0x10373a (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x10373a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10373a 6 (.base 5 (.d8 0xc0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10373a 6 (.base 5 (.d8 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x10373a 0x48 (by decide) 6 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10373e [0x48, 0x8B, 0x55, 0xA8] (LoadPre 0x10373e (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x10373e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10373e 2 (.base 5 (.d8 0xa8)))
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10373e 2 (.base 5 (.d8 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x10373e 0x48 (by decide) 2 (.base 5 (.d8 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(5, 5), (13, 13)]) (p' := 0x10373a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(5, 5), (13, 13)]) (p' := 0x10373e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(5, 5), (13, 13)]) (p' := 0x103742) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l103737 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103737 :=
  Rest.liftedBlock (rest_l103737 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103737 x hx)

theorem rest_l103746 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103746 bytes_l103746) (entryMap (live .l103746))
      3 0x103746 bytes_l103746 b_l103746 := by
  have f0 : InstrSpec 0x103746 [0x84, 0xC0] (fun s => s.RIP = 0x103746) (testR8R8Effect 0x103746 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x103746 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x103746 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103748 [0xB0, 0x01] (fun s => s.RIP = 0x103748) (movR8Imm8Effect 0x103748 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x103748 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x103748 0xb0 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103748) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10374a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x10374a 5 0xd8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103746 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103746 :=
  Rest.liftedBlock (rest_l103746 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103746 x hx)

theorem rest_l103750 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103750 bytes_l103750) (entryMap (live .l103750))
      4 0x103750 bytes_l103750 b_l103750 := by
  have f0 : InstrSpec 0x103750 [0x48, 0x8B, 0x45, 0xC8] (LoadPre 0x103750 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x103750 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103750 0 (.base 5 (.d8 0xc8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103750 0 (.base 5 (.d8 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x103750 0x48 (by decide) 0 (.base 5 (.d8 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103754 [0x49, 0x89, 0x44, 0x24, 0x10] (StorePre 0x103754 5 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x103754 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103754 0 (.sib 12 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 12] [] [.rip] :=
    (movM64R64Effect_footprint 0x103754 0 (.sib 12 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x103754 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103759 [0x31, 0xC0] (fun s => s.RIP = 0x103759) (xorR32R32Effect 0x103759 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x103759 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x103759 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103754) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103759) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10375b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 58) (jmp_rel32_effect_step 0x10375b 0xc8 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103750 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103750 :=
  Rest.liftedBlock (rest_l103750 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103750 x hx)

theorem rest_l1037a6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1037a6 bytes_l1037a6) (entryMap (live .l1037a6))
      2 0x1037a6 bytes_l1037a6 b_l1037a6 := by
  have f0 : InstrSpec 0x1037a6 [0xB0, 0x01] (fun s => s.RIP = 0x1037a6) (movR8Imm8Effect 0x1037a6 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x1037a6 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x1037a6 0xb0 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1037a8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x1037a8 0x7e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1037a6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1037a6 :=
  Rest.liftedBlock (rest_l1037a6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1037a6 x hx)

theorem rest_l103828 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103828 bytes_l103828) (entryMap (live .l103828))
      8 0x103828 bytes_l103828 b_l103828 := by
  have f0 : InstrSpec 0x103828 [0x48, 0x83, 0xC4, 0x48] (fun s => s.RIP = 0x103828) (addR64Imm8Effect 0x103828 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x103828 4 0x48).toInstrSpec (add_r64_imm8_effect_step 0x103828 0x48 0xc4 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10382c [0x5B] (PopPre 0x10382c) (popR64Effect 0x10382c 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10382c 1 3).toInstrSpec (pop_r64_effect_step 0x10382c 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10382d [0x41, 0x5C] (PopPre 0x10382d) (popR64Effect 0x10382d 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10382d 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10382d 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10382f [0x41, 0x5D] (PopPre 0x10382f) (popR64Effect 0x10382f 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10382f 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10382f 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x103831 [0x41, 0x5E] (PopPre 0x103831) (popR64Effect 0x103831 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103831 2 14).toInstrSpec (pop_r64_rex_effect_step 0x103831 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x103833 [0x41, 0x5F] (PopPre 0x103833) (popR64Effect 0x103833 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103833 2 15).toInstrSpec (pop_r64_rex_effect_step 0x103833 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x103835 [0x5D] (PopPre 0x103835) (popR64Effect 0x103835 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103835 1 5).toInstrSpec (pop_r64_effect_step 0x103835 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x103836 [0xC3] (RetPre 0x103836) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x103836).toInstrSpec (ret_effect_step 0x103836) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10382c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10382d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10382f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103831) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103833) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103835) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103836) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l103828 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103828 :=
  Rest.liftedBlock (rest_l103828 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103828 x hx)

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

theorem_by block_l103520_eval :
    program.runBlock (dialect code) ⟨.l103520, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103581_eval :
    program.runBlock (dialect code) ⟨.l103581, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103593_eval :
    program.runBlock (dialect code) ⟨.l103593, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1035b1_eval :
    program.runBlock (dialect code) ⟨.l1035b1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1035bd_eval :
    program.runBlock (dialect code) ⟨.l1035bd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1035dc_eval :
    program.runBlock (dialect code) ⟨.l1035dc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1035e2_eval :
    program.runBlock (dialect code) ⟨.l1035e2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1035e7_eval :
    program.runBlock (dialect code) ⟨.l1035e7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1035f4_eval :
    program.runBlock (dialect code) ⟨.l1035f4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1035fa_eval :
    program.runBlock (dialect code) ⟨.l1035fa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103609_eval :
    program.runBlock (dialect code) ⟨.l103609, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10360e_eval :
    program.runBlock (dialect code) ⟨.l10360e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103612_eval :
    program.runBlock (dialect code) ⟨.l103612, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103620_eval :
    program.runBlock (dialect code) ⟨.l103620, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103663_eval :
    program.runBlock (dialect code) ⟨.l103663, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103668_eval :
    program.runBlock (dialect code) ⟨.l103668, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103670_eval :
    program.runBlock (dialect code) ⟨.l103670, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103685_eval :
    program.runBlock (dialect code) ⟨.l103685, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103697_eval :
    program.runBlock (dialect code) ⟨.l103697, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1036a8_eval :
    program.runBlock (dialect code) ⟨.l1036a8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1036d0_eval :
    program.runBlock (dialect code) ⟨.l1036d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103706_eval :
    program.runBlock (dialect code) ⟨.l103706, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103712_eval :
    program.runBlock (dialect code) ⟨.l103712, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103720_eval :
    program.runBlock (dialect code) ⟨.l103720, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103725_eval :
    program.runBlock (dialect code) ⟨.l103725, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103731_eval :
    program.runBlock (dialect code) ⟨.l103731, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103735_eval :
    program.runBlock (dialect code) ⟨.l103735, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103737_eval :
    program.runBlock (dialect code) ⟨.l103737, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103746_eval :
    program.runBlock (dialect code) ⟨.l103746, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103750_eval :
    program.runBlock (dialect code) ⟨.l103750, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1037a6_eval :
    program.runBlock (dialect code) ⟨.l1037a6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103828_eval :
    program.runBlock (dialect code) ⟨.l103828, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
