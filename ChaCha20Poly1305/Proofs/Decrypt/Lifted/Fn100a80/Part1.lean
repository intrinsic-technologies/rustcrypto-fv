import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Program
import X86Proofs.Instructions.Branch.Triple
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Values

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

theorem rest_l100a80 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100a80 bytes_l100a80) (entryMap (live .l100a80))
      15 0x100a80 bytes_l100a80 b_l100a80 := by
  have f0 : InstrSpec 0x100a80 [0x55] (PushPre 0x100a80 1) (pushR64Effect 0x100a80 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100a80 1 5).toInstrSpec (push_r64_effect_step 0x100a80 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x100a81 [0x41, 0x57] (PushPre 0x100a81 2) (pushR64Effect 0x100a81 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100a81 2 15).toInstrSpec (push_r64_rex_effect_step 0x100a81 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x100a83 [0x41, 0x56] (PushPre 0x100a83 2) (pushR64Effect 0x100a83 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100a83 2 14).toInstrSpec (push_r64_rex_effect_step 0x100a83 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x100a85 [0x41, 0x55] (PushPre 0x100a85 2) (pushR64Effect 0x100a85 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100a85 2 13).toInstrSpec (push_r64_rex_effect_step 0x100a85 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x100a87 [0x41, 0x54] (PushPre 0x100a87 2) (pushR64Effect 0x100a87 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100a87 2 12).toInstrSpec (push_r64_rex_effect_step 0x100a87 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x100a89 [0x53] (PushPre 0x100a89 1) (pushR64Effect 0x100a89 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100a89 1 3).toInstrSpec (push_r64_effect_step 0x100a89 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x100a8a [0x48, 0x81, 0xEC, 0x70, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x100a8a) (subR64Imm32Effect 0x100a8a 4 0x170)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x100a8a 4 0x170).toInstrSpec (sub_r64_imm32_effect_step 0x100a8a 0x48 0xec 0x170 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100a91 [0x4C, 0x8B, 0x5E, 0x10] (LoadPre 0x100a91 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x100a91 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100a91 11 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x100a91 11 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x100a91 0x4c (by decide) 3 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x100a95 [0x44, 0x8B, 0x67, 0x30] (LoadPre 0x100a95 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x100a95 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x100a95 12 (.base 7 (.d8 0x30)))
      [.gpr 7] [] [.reg 12, .rip] :=
    (movR32M32Effect_footprint 0x100a95 12 (.base 7 (.d8 0x30))).toInstrSpec (mov_r32_m32_effect_step 0x100a95 0x44 (by decide) 4 (.base 7 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x100a99 [0x0F, 0xB6, 0x4F, 0x40] (LoadPre 0x100a99 (fun s => AddrMode.addr (.base 7 (.d8 0x40)) s (0x100a99 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x100a99 4 1 (.base 7 (.d8 0x40)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x100a99 4 1 (.base 7 (.d8 0x40))).toInstrSpec (movzx_r32_m8_effect_step 0x100a99 1 (.base 7 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x100a9d [0x41, 0xBA, 0x40, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100a9d) (movR32Imm32Effect 0x100a9d 6 10 0x40)
      [] [] [.reg 10, .rip] :=
    (movR32Imm32Effect_footprint 0x100a9d 6 10 0x40).toInstrSpec (mov_r32_imm32_rex_effect_step 0x100a9d 0x41 0xba (by decide) (by decide) 0x40) pre_rip
  have f11 : InstrSpec 0x100aa3 [0x49, 0x29, 0xCA] (fun s => s.RIP = 0x100aa3) (subR64R64Effect 0x100aa3 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (subR64R64Effect_footprint 0x100aa3 10 1).toInstrSpec (sub_r64_r64_effect_step 0x100aa3 0x49 0xca (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x100aa6 [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x100aa6) (movR64R64Effect 0x100aa6 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100aa6 0 11).toInstrSpec (mov_r64_r64_effect_step 0x100aa6 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x100aa9 [0x4C, 0x29, 0xD0] (fun s => s.RIP = 0x100aa9) (subR64R64Effect 0x100aa9 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x100aa9 0 10).toInstrSpec (sub_r64_r64_effect_step 0x100aa9 0x4c 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a81) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a83) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a85) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a87) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a89) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a8a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a91) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a95) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (11, 67), (12, 69), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a99) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 71), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (11, 67), (12, 69), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a9d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 71), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 73), (11, 67), (12, 69), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100aa3) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 71), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 75), (11, 67), (12, 69), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100aa6) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 71), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 75), (11, 67), (12, 69), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100aa9) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 80) f13 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 71), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 75), (11, 67), (12, 69), (13, 13), (14, 14), (15, 15), (16, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100aac) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 82) (jcc_rel8_effect_step 0x100aac 2 0x22) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100a80 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100a80 :=
  Rest.liftedBlock (rest_l100a80 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100a80 x hx)

theorem rest_l100aae [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100aae bytes_l100aae) (entryMap (live .l100aae))
      10 0x100aae bytes_l100aae b_l100aae := by
  have f0 : InstrSpec 0x100aae [0x44, 0x89, 0xE2] (fun s => s.RIP = 0x100aae) (movR32R32Effect 0x100aae 3 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x100aae 3 2 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x100aae 0x44 0xe2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100ab1 [0xF7, 0xD2] (fun s => s.RIP = 0x100ab1) (notR32Effect 0x100ab1 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR32Effect_footprint 0x100ab1 2 2).toInstrSpec (not_r32_effect_step 0x100ab1 0xd2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100ab3 [0x49, 0x89, 0xC0] (fun s => s.RIP = 0x100ab3) (movR64R64Effect 0x100ab3 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x100ab3 8 0).toInstrSpec (mov_r64_r64_effect_step 0x100ab3 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100ab6 [0x49, 0xC1, 0xE8, 0x06] (fun s => s.RIP = 0x100ab6) (shrR64Effect 0x100ab6 4 8 6)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x100ab6 4 8 6).toInstrSpec (shr_r64_imm8_effect_step 0x100ab6 0x49 0xe8 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100aba [0x83, 0xE0, 0x3F] (fun s => s.RIP = 0x100aba) (andR32Imm8Effect 0x100aba 3 0 0x3f)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x100aba 3 0 0x3f).toInstrSpec (and_r32_imm8_effect_step 0x100aba 0xe0 0x3f (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x100abd [0x48, 0x83, 0xF8, 0x01] (fun s => s.RIP = 0x100abd) (cmpR64Imm8Effect 0x100abd 0 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100abd 0 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x100abd 0x48 0xf8 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100ac1 [0x49, 0x83, 0xD8, 0xFF] (fun s => s.RIP = 0x100ac1) (atFlags StatusFlags.CF (sbbR64Imm8Effect 0x100ac1 8 0xff))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (sbbR64Imm8Effect_footprint 0x100ac1 8 0xff).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_imm8_effect_step 0x100ac1 0x49 0xd8 0xff c (by decide) (by decide) (by decide))) pre_rip
  have f7 : InstrSpec 0x100ac5 [0xB0, 0x01] (fun s => s.RIP = 0x100ac5) (movR8Imm8Effect 0x100ac5 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x100ac5 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x100ac5 0xb0 (by decide) 0x1) pre_rip
  have f8 : InstrSpec 0x100ac7 [0x49, 0x39, 0xD0] (fun s => s.RIP = 0x100ac7) (cmpR64R64Effect 0x100ac7 8 2)
      [.gpr 8, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x100ac7 8 2).toInstrSpec (cmp_r64_r64_effect_step 0x100ac7 0x49 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ab1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ab3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (6, 6), (7, 7), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ab6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (6, 6), (7, 7), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100aba) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 55), (4, 4), (6, 6), (7, 7), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100abd) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 1), (2, 55), (4, 4), (6, 6), (7, 7), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (16, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ac1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 1), (2, 55), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ac5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 55), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ac7) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 67), (1, 1), (2, 55), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (16, 69), (19, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100aca) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 72) (jcc_rel32_effect_step 0x100aca 7 0x9da) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100aae [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100aae :=
  Rest.liftedBlock (rest_l100aae code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100aae x hx)

theorem rest_l100ad0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100ad0 bytes_l100ad0) (entryMap (live .l100ad0))
      14 0x100ad0 bytes_l100ad0 b_l100ad0 := by
  have f0 : InstrSpec 0x100ad0 [0x4D, 0x39, 0xD3] (fun s => s.RIP = 0x100ad0) (cmpR64R64Effect 0x100ad0 11 10)
      [.gpr 11, .gpr 10] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x100ad0 11 10).toInstrSpec (cmp_r64_r64_effect_step 0x100ad0 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100ad3 [0x4D, 0x0F, 0x42, 0xD3] (fun s => s.RIP = 0x100ad3) (atFlags (condHolds 2) (cmovR64R64Effect 0x100ad3 4 10 11))
      [.gpr 10, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .rip] :=
    (cmovR64R64Effect_footprint 0x100ad3 4 10 11 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x100ad3 2 0x4d (by decide) 0xd3 (by decide) c)) pre_rip
  have f2 : InstrSpec 0x100ad7 [0x41, 0x8D, 0x04, 0x0A] (fun s => s.RIP = 0x100ad7) (leaR32Effect 0x100ad7 4 0 (.sib 10 (some 1) 0 .none))
      [.gpr 10, .gpr 1] [] [.reg 0, .rip] :=
    (leaR32Effect_footprint 0x100ad7 4 0 (.sib 10 (some 1) 0 .none)).toInstrSpec (lea_r32_rex_effect_step 0x100ad7 0x41 (by decide) 0 (.sib 10 (some 1) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100adb [0x88, 0x47, 0x40] (StorePre 0x100adb 3 (fun s => AddrMode.addr (.base 7 (.d8 0x40)) s (0x100adb + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x100adb 3 0 (.base 7 (.d8 0x40)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x100adb 3 0 (.base 7 (.d8 0x40))).toInstrSpec (mov_m8_r8_effect_step 0x100adb 0 (by decide) (.base 7 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x100ade [0x48, 0x8B, 0x1E] (LoadPre 0x100ade (fun s => AddrMode.addr (.base 6 .none) s (0x100ade + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100ade 3 (.base 6 .none))
      [.gpr 6] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x100ade 3 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x100ade 0x48 (by decide) 3 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x100ae1 [0x4C, 0x8B, 0x76, 0x08] (LoadPre 0x100ae1 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x100ae1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100ae1 14 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x100ae1 14 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x100ae1 0x4c (by decide) 6 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x100ae5 [0x4D, 0x29, 0xD3] (fun s => s.RIP = 0x100ae5) (subR64R64Effect 0x100ae5 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (subR64R64Effect_footprint 0x100ae5 11 10).toInstrSpec (sub_r64_r64_effect_step 0x100ae5 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100ae8 [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x100ae8) (movR64R64Effect 0x100ae8 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100ae8 0 11).toInstrSpec (mov_r64_r64_effect_step 0x100ae8 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100aeb [0x48, 0xC1, 0xE8, 0x06] (fun s => s.RIP = 0x100aeb) (shrR64Effect 0x100aeb 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x100aeb 4 0 6).toInstrSpec (shr_r64_imm8_effect_step 0x100aeb 0x48 0xe8 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100aef [0x48, 0x89, 0x44, 0x24, 0x50] (StorePre 0x100aef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x100aef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100aef 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100aef 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x100aef 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x100af4 [0x45, 0x89, 0xDF] (fun s => s.RIP = 0x100af4) (movR32R32Effect 0x100af4 3 15 11)
      [.gpr 11] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x100af4 3 15 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x100af4 0x45 0xdf (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x100af7 [0x41, 0x83, 0xE7, 0x3F] (fun s => s.RIP = 0x100af7) (andR32Imm8Effect 0x100af7 4 15 0x3f)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x100af7 4 15 0x3f).toInstrSpec (and_r32_imm8_rex_effect_step 0x100af7 0x41 0xe7 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x100afb [0x4D, 0x85, 0xD2] (fun s => s.RIP = 0x100afb) (testR64R64Effect 0x100afb 10 10)
      [.gpr 10, .gpr 10] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100afb 10 10).toInstrSpec (test_r64_r64_effect_step 0x100afb 0x4d 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ad3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (10, 55), (11, 11), (12, 12), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ad7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (10, 55), (11, 11), (12, 12), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100adb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 57), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (10, 55), (11, 11), (12, 12), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ade) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (9, 9), (10, 55), (11, 11), (12, 12), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ae1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (9, 9), (10, 55), (11, 11), (12, 12), (14, 62), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ae5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (9, 9), (10, 55), (11, 64), (12, 12), (14, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ae8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 1), (2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (9, 9), (10, 55), (11, 64), (12, 12), (14, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100aeb) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 1), (2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (9, 9), (10, 55), (11, 64), (12, 12), (14, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100aef) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 1), (2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (9, 9), (10, 55), (11, 64), (12, 12), (14, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100af4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 68), (1, 1), (2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (9, 9), (10, 55), (11, 64), (12, 12), (14, 62), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100af7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 68), (1, 1), (2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (9, 9), (10, 55), (11, 64), (12, 12), (14, 62), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100afb) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 68), (1, 1), (2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (9, 9), (10, 55), (11, 64), (12, 12), (14, 62), (15, 73), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100afe) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 77) (jcc_rel32_effect_step 0x100afe 4 0xa1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100ad0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100ad0 :=
  Rest.liftedBlock (rest_l100ad0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100ad0 x hx)

theorem rest_l100b04 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b04 bytes_l100b04) (entryMap (live .l100b04))
      4 0x100b04 bytes_l100b04 b_l100b04 := by
  have f0 : InstrSpec 0x100b04 [0x44, 0x89, 0xD0] (fun s => s.RIP = 0x100b04) (movR32R32Effect 0x100b04 3 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x100b04 3 0 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x100b04 0x44 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100b07 [0x83, 0xE0, 0x03] (fun s => s.RIP = 0x100b07) (andR32Imm8Effect 0x100b07 3 0 0x3)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x100b07 3 0 0x3).toInstrSpec (and_r32_imm8_effect_step 0x100b07 0xe0 0x3 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100b0a [0x49, 0x83, 0xFA, 0x04] (fun s => s.RIP = 0x100b0a) (cmpR64Imm8Effect 0x100b0a 10 0x4)
      [.gpr 10] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100b0a 10 0x4).toInstrSpec (cmp_r64_imm8_effect_step 0x100b0a 0x49 0xfa 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b07) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b0a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b0e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x100b0e 3 0x4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100b04 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b04 :=
  Rest.liftedBlock (rest_l100b04 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b04 x hx)

theorem rest_l100b10 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b10 bytes_l100b10) (entryMap (live .l100b10))
      2 0x100b10 bytes_l100b10 b_l100b10 := by
  have f0 : InstrSpec 0x100b10 [0x31, 0xD2] (fun s => s.RIP = 0x100b10) (xorR32R32Effect 0x100b10 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100b10 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x100b10 0xd2 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b12) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x100b12 0x67 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100b10 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b10 :=
  Rest.liftedBlock (rest_l100b10 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b10 x hx)

theorem rest_l100b14 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b14 bytes_l100b14) (entryMap (live .l100b14))
      6 0x100b14 bytes_l100b14 b_l100b14 := by
  have f0 : InstrSpec 0x100b14 [0x44, 0x89, 0xD6] (fun s => s.RIP = 0x100b14) (movR32R32Effect 0x100b14 3 6 10)
      [.gpr 10] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x100b14 3 6 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x100b14 0x44 0xd6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100b17 [0x83, 0xE6, 0x7C] (fun s => s.RIP = 0x100b17) (andR32Imm8Effect 0x100b17 3 6 0x7c)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x100b17 3 6 0x7c).toInstrSpec (and_r32_imm8_effect_step 0x100b17 0xe6 0x7c (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100b1a [0x4C, 0x8D, 0x0C, 0x39] (fun s => s.RIP = 0x100b1a) (leaR64Effect 0x100b1a 9 (.sib 1 (some 7) 0 .none))
      [.gpr 1, .gpr 7] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x100b1a 9 (.sib 1 (some 7) 0 .none)).toInstrSpec (lea_r64_effect_step 0x100b1a 0x4c (by decide) 1 (.sib 1 (some 7) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100b1e [0x49, 0x83, 0xC1, 0x43] (fun s => s.RIP = 0x100b1e) (addR64Imm8Effect 0x100b1e 9 0x43)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x100b1e 9 0x43).toInstrSpec (add_r64_imm8_effect_step 0x100b1e 0x49 0xc1 0x43 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100b22 [0x31, 0xD2] (fun s => s.RIP = 0x100b22) (xorR32R32Effect 0x100b22 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100b22 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x100b22 0xd2 (by decide)) pre_rip
  have f5 : InstrSpec 0x100b24 [0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100b24) (fun _ => nopEffect 0x100b24 12)
      [] [] [.rip] :=
    (nopEffect_footprint 0x100b24 12).toInstrSpec (nop_m_effect_step 0x100b24 [0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b17) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 7), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b1a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 7), (9, 57), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b1e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 7), (9, 59), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b22) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (6, 55), (7, 7), (9, 59), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b24) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (6, 55), (7, 7), (9, 59), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b30) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 64) (by decide) rfl

theorem block_l100b14 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b14 :=
  Rest.liftedBlock (rest_l100b14 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b14 x hx)

theorem rest_l100b30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b30 bytes_l100b30) (entryMap (live .l100b30))
      15 0x100b30 bytes_l100b30 b_l100b30 := by
  have f0 : InstrSpec 0x100b30 [0x45, 0x0F, 0xB6, 0x44, 0x11, 0xFD] (LoadPre 0x100b30 (fun s => AddrMode.addr (.sib 9 (some 2) 0 (.d8 0xfd)) s (0x100b30 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x100b30 6 8 (.sib 9 (some 2) 0 (.d8 0xfd)))
      [.gpr 9, .gpr 2] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x100b30 6 8 (.sib 9 (some 2) 0 (.d8 0xfd))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x100b30 0x45 (by decide) 0 (.sib 9 (some 2) 0 (.d8 0xfd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100b36 [0x44, 0x32, 0x04, 0x13] (LoadPre 0x100b36 (fun s => AddrMode.addr (.sib 3 (some 2) 0 .none) s (0x100b36 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x100b36 4 8 (.sib 3 (some 2) 0 .none))
      [.gpr 8, .gpr 3, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x100b36 4 8 (.sib 3 (some 2) 0 .none)).toInstrSpec (xor_r8_m8_rex_effect_step 0x100b36 0x44 (by decide) 0 (.sib 3 (some 2) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100b3a [0x45, 0x88, 0x04, 0x16] (StorePre 0x100b3a 4 (fun s => AddrMode.addr (.sib 14 (some 2) 0 .none) s (0x100b3a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x100b3a 4 8 (.sib 14 (some 2) 0 .none))
      [.gpr 8, .gpr 14, .gpr 2] [] [.rip] :=
    (movM8R8Effect_footprint 0x100b3a 4 8 (.sib 14 (some 2) 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x100b3a 0x45 (by decide) 0 (.sib 14 (some 2) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100b3e [0x45, 0x0F, 0xB6, 0x44, 0x11, 0xFE] (LoadPre 0x100b3e (fun s => AddrMode.addr (.sib 9 (some 2) 0 (.d8 0xfe)) s (0x100b3e + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x100b3e 6 8 (.sib 9 (some 2) 0 (.d8 0xfe)))
      [.gpr 9, .gpr 2] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x100b3e 6 8 (.sib 9 (some 2) 0 (.d8 0xfe))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x100b3e 0x45 (by decide) 0 (.sib 9 (some 2) 0 (.d8 0xfe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x100b44 [0x44, 0x32, 0x44, 0x13, 0x01] (LoadPre 0x100b44 (fun s => AddrMode.addr (.sib 3 (some 2) 0 (.d8 0x1)) s (0x100b44 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x100b44 5 8 (.sib 3 (some 2) 0 (.d8 0x1)))
      [.gpr 8, .gpr 3, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x100b44 5 8 (.sib 3 (some 2) 0 (.d8 0x1))).toInstrSpec (xor_r8_m8_rex_effect_step 0x100b44 0x44 (by decide) 0 (.sib 3 (some 2) 0 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x100b49 [0x45, 0x88, 0x44, 0x16, 0x01] (StorePre 0x100b49 5 (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x1)) s (0x100b49 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x100b49 5 8 (.sib 14 (some 2) 0 (.d8 0x1)))
      [.gpr 8, .gpr 14, .gpr 2] [] [.rip] :=
    (movM8R8Effect_footprint 0x100b49 5 8 (.sib 14 (some 2) 0 (.d8 0x1))).toInstrSpec (mov_m8_r8_rex_effect_step 0x100b49 0x45 (by decide) 0 (.sib 14 (some 2) 0 (.d8 0x1)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x100b4e [0x45, 0x0F, 0xB6, 0x44, 0x11, 0xFF] (LoadPre 0x100b4e (fun s => AddrMode.addr (.sib 9 (some 2) 0 (.d8 0xff)) s (0x100b4e + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x100b4e 6 8 (.sib 9 (some 2) 0 (.d8 0xff)))
      [.gpr 9, .gpr 2] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x100b4e 6 8 (.sib 9 (some 2) 0 (.d8 0xff))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x100b4e 0x45 (by decide) 0 (.sib 9 (some 2) 0 (.d8 0xff)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x100b54 [0x44, 0x32, 0x44, 0x13, 0x02] (LoadPre 0x100b54 (fun s => AddrMode.addr (.sib 3 (some 2) 0 (.d8 0x2)) s (0x100b54 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x100b54 5 8 (.sib 3 (some 2) 0 (.d8 0x2)))
      [.gpr 8, .gpr 3, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x100b54 5 8 (.sib 3 (some 2) 0 (.d8 0x2))).toInstrSpec (xor_r8_m8_rex_effect_step 0x100b54 0x44 (by decide) 0 (.sib 3 (some 2) 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x100b59 [0x45, 0x88, 0x44, 0x16, 0x02] (StorePre 0x100b59 5 (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x2)) s (0x100b59 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x100b59 5 8 (.sib 14 (some 2) 0 (.d8 0x2)))
      [.gpr 8, .gpr 14, .gpr 2] [] [.rip] :=
    (movM8R8Effect_footprint 0x100b59 5 8 (.sib 14 (some 2) 0 (.d8 0x2))).toInstrSpec (mov_m8_r8_rex_effect_step 0x100b59 0x45 (by decide) 0 (.sib 14 (some 2) 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x100b5e [0x45, 0x0F, 0xB6, 0x04, 0x11] (LoadPre 0x100b5e (fun s => AddrMode.addr (.sib 9 (some 2) 0 .none) s (0x100b5e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100b5e 5 8 (.sib 9 (some 2) 0 .none))
      [.gpr 9, .gpr 2] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x100b5e 5 8 (.sib 9 (some 2) 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x100b5e 0x45 (by decide) 0 (.sib 9 (some 2) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x100b63 [0x44, 0x32, 0x44, 0x13, 0x03] (LoadPre 0x100b63 (fun s => AddrMode.addr (.sib 3 (some 2) 0 (.d8 0x3)) s (0x100b63 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x100b63 5 8 (.sib 3 (some 2) 0 (.d8 0x3)))
      [.gpr 8, .gpr 3, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x100b63 5 8 (.sib 3 (some 2) 0 (.d8 0x3))).toInstrSpec (xor_r8_m8_rex_effect_step 0x100b63 0x44 (by decide) 0 (.sib 3 (some 2) 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x100b68 [0x45, 0x88, 0x44, 0x16, 0x03] (StorePre 0x100b68 5 (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x3)) s (0x100b68 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x100b68 5 8 (.sib 14 (some 2) 0 (.d8 0x3)))
      [.gpr 8, .gpr 14, .gpr 2] [] [.rip] :=
    (movM8R8Effect_footprint 0x100b68 5 8 (.sib 14 (some 2) 0 (.d8 0x3))).toInstrSpec (mov_m8_r8_rex_effect_step 0x100b68 0x45 (by decide) 0 (.sib 14 (some 2) 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x100b6d [0x48, 0x83, 0xC2, 0x04] (fun s => s.RIP = 0x100b6d) (addR64Imm8Effect 0x100b6d 2 0x4)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x100b6d 2 0x4).toInstrSpec (add_r64_imm8_effect_step 0x100b6d 0x48 0xc2 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x100b71 [0x48, 0x39, 0xD6] (fun s => s.RIP = 0x100b71) (cmpR64R64Effect 0x100b71 6 2)
      [.gpr 6, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x100b71 6 2).toInstrSpec (cmp_r64_r64_effect_step 0x100b71 0x48 0xd6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b36) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b3a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b3e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 58), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b44) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b49) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b4e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b54) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b59) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b5e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 68), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b63) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b68) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b6d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 73), (3, 3), (4, 4), (6, 6), (7, 7), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b71) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 73), (3, 3), (4, 4), (6, 6), (7, 7), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b74) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 77) (jcc_rel8_effect_step 0x100b74 5 0xba) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100b30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b30 :=
  Rest.liftedBlock (rest_l100b30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b30 x hx)

theorem rest_l100b76 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b76 bytes_l100b76) (entryMap (live .l100b76))
      2 0x100b76 bytes_l100b76 b_l100b76 := by
  have f0 : InstrSpec 0x100b76 [0x48, 0x85, 0xC0] (fun s => s.RIP = 0x100b76) (testR64R64Effect 0x100b76 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100b76 0 0).toInstrSpec (test_r64_r64_effect_step 0x100b76 0x48 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b79) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x100b79 4 0x2a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100b76 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b76 :=
  Rest.liftedBlock (rest_l100b76 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b76 x hx)

theorem rest_l100b7b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b7b bytes_l100b7b) (entryMap (live .l100b7b))
      7 0x100b7b bytes_l100b7b b_l100b7b := by
  have f0 : InstrSpec 0x100b7b [0x48, 0x01, 0xD1] (fun s => s.RIP = 0x100b7b) (addR64R64Effect 0x100b7b 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x100b7b 1 2).toInstrSpec (add_r64_r64_effect_step 0x100b7b 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100b7e [0x48, 0x01, 0xF9] (fun s => s.RIP = 0x100b7e) (addR64R64Effect 0x100b7e 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x100b7e 1 7).toInstrSpec (add_r64_r64_effect_step 0x100b7e 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100b81 [0x48, 0x83, 0xC1, 0x40] (fun s => s.RIP = 0x100b81) (addR64Imm8Effect 0x100b81 1 0x40)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x100b81 1 0x40).toInstrSpec (add_r64_imm8_effect_step 0x100b81 0x48 0xc1 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100b85 [0x49, 0x8D, 0x34, 0x16] (fun s => s.RIP = 0x100b85) (leaR64Effect 0x100b85 6 (.sib 14 (some 2) 0 .none))
      [.gpr 14, .gpr 2] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x100b85 6 (.sib 14 (some 2) 0 .none)).toInstrSpec (lea_r64_effect_step 0x100b85 0x49 (by decide) 6 (.sib 14 (some 2) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100b89 [0x48, 0x01, 0xDA] (fun s => s.RIP = 0x100b89) (addR64R64Effect 0x100b89 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x100b89 2 3).toInstrSpec (add_r64_r64_effect_step 0x100b89 0x48 0xda (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x100b8c [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x100b8c) (xorR32R32Effect 0x100b8c 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100b8c 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x100b8c 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100b8f [0x90] (fun s => s.RIP = 0x100b8f) (fun _ => nopEffect 0x100b8f 1)
      [] [] [.rip] :=
    (nopEffect_footprint 0x100b8f 1).toInstrSpec (nop_effect_step 0x100b8f) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b7e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b81) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b85) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (2, 2), (3, 3), (4, 4), (6, 59), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b89) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 57), (2, 61), (3, 3), (4, 4), (6, 59), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b8c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 57), (2, 61), (3, 3), (4, 4), (6, 59), (7, 7), (9, 63), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b8f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 57), (2, 61), (3, 3), (4, 4), (6, 59), (7, 7), (9, 63), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b90) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 66) (by decide) rfl

theorem block_l100b7b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b7b :=
  Rest.liftedBlock (rest_l100b7b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b7b x hx)

theorem rest_l100b90 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b90 bytes_l100b90) (entryMap (live .l100b90))
      6 0x100b90 bytes_l100b90 b_l100b90 := by
  have f0 : InstrSpec 0x100b90 [0x46, 0x0F, 0xB6, 0x04, 0x09] (LoadPre 0x100b90 (fun s => AddrMode.addr (.sib 1 (some 9) 0 .none) s (0x100b90 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100b90 5 8 (.sib 1 (some 9) 0 .none))
      [.gpr 1, .gpr 9] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x100b90 5 8 (.sib 1 (some 9) 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x100b90 0x46 (by decide) 0 (.sib 1 (some 9) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100b95 [0x46, 0x32, 0x04, 0x0A] (LoadPre 0x100b95 (fun s => AddrMode.addr (.sib 2 (some 9) 0 .none) s (0x100b95 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x100b95 4 8 (.sib 2 (some 9) 0 .none))
      [.gpr 8, .gpr 2, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x100b95 4 8 (.sib 2 (some 9) 0 .none)).toInstrSpec (xor_r8_m8_rex_effect_step 0x100b95 0x46 (by decide) 0 (.sib 2 (some 9) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100b99 [0x46, 0x88, 0x04, 0x0E] (StorePre 0x100b99 4 (fun s => AddrMode.addr (.sib 6 (some 9) 0 .none) s (0x100b99 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x100b99 4 8 (.sib 6 (some 9) 0 .none))
      [.gpr 8, .gpr 6, .gpr 9] [] [.rip] :=
    (movM8R8Effect_footprint 0x100b99 4 8 (.sib 6 (some 9) 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x100b99 0x46 (by decide) 0 (.sib 6 (some 9) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100b9d [0x49, 0xFF, 0xC1] (fun s => s.RIP = 0x100b9d) (incR64Effect 0x100b9d 9)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (incR64Effect_footprint 0x100b9d 9).toInstrSpec (inc_r64_effect_step 0x100b9d 0x49 0xc1 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100ba0 [0x4C, 0x39, 0xC8] (fun s => s.RIP = 0x100ba0) (cmpR64R64Effect 0x100ba0 0 9)
      [.gpr 0, .gpr 9] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x100ba0 0 9).toInstrSpec (cmp_r64_r64_effect_step 0x100ba0 0x4c 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b95) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b99) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b9d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 58), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ba0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 58), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ba3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel8_effect_step 0x100ba3 5 0xeb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100b90 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b90 :=
  Rest.liftedBlock (rest_l100b90 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b90 x hx)

theorem rest_l100ba5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100ba5 bytes_l100ba5) (entryMap (live .l100ba5))
      8 0x100ba5 bytes_l100ba5 b_l100ba5 := by
  have f0 : InstrSpec 0x100ba5 [0x48, 0x83, 0x7C, 0x24, 0x50, 0x00] (LoadPre 0x100ba5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x100ba5 + BitVec.ofNat 64 6)) 8) (cmpMImm8Effect 0x100ba5 6 64 (.sib 4 none 0 (.d8 0x50)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect64_footprint 0x100ba5 6 (.sib 4 none 0 (.d8 0x50)) 0x0).toInstrSpec (cmp_m64_imm8_effect_step 0x100ba5 0x48 (by decide) (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100bab [0x48, 0x89, 0x7C, 0x24, 0x48] (StorePre 0x100bab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x100bab + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100bab 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100bab 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x100bab 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x100bb0 [0x4C, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x100bb0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x100bb0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100bb0 10 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100bb0 10 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x100bb0 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100bb8 [0x4C, 0x89, 0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x100bb8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x100bb8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100bb8 11 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100bb8 11 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x100bb8 0x4c (by decide) 3 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x100bc0 [0x48, 0x89, 0x9C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x100bc0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x100bc0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100bc0 3 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100bc0 3 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x100bc0 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x100bc8 [0x4C, 0x89, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x100bc8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x100bc8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100bc8 14 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100bc8 14 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x100bc8 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x100bd0 [0x4C, 0x89, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x100bd0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x100bd0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100bd0 15 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100bd0 15 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x100bd0 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bab) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bb0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bb8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bc0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bc8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bd0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bd8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 61) (jcc_rel32_effect_step 0x100bd8 4 0x4ee) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100ba5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100ba5 :=
  Rest.liftedBlock (rest_l100ba5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100ba5 x hx)

theorem rest_l100bde_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x100bde bytes_l100bde) [(0, 79), (3, 3), (4, 4), (7, 7), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]
      16 0x100c28 bytes_l100bde_1 b_l100bde_1 := by
  have f20 : InstrSpec 0x100c28 [0x8B, 0x47, 0x24] (LoadPre 0x100c28 (fun s => AddrMode.addr (.base 7 (.d8 0x24)) s (0x100c28 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c28 0 (.base 7 (.d8 0x24)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100c28 0 (.base 7 (.d8 0x24))).toInstrSpec (mov_r32_m32_low_effect_step 0x100c28 0 (.base 7 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x100c2b [0x89, 0x44, 0x24, 0x28] (StorePre 0x100c2b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100c2b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c2b 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100c2b 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m32_r32_low_effect_step 0x100c2b 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x100c2f [0x8B, 0x47, 0x28] (LoadPre 0x100c2f (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x100c2f + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c2f 0 (.base 7 (.d8 0x28)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100c2f 0 (.base 7 (.d8 0x28))).toInstrSpec (mov_r32_m32_low_effect_step 0x100c2f 0 (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x100c32 [0x89, 0x44, 0x24, 0x24] (StorePre 0x100c32 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x100c32 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c32 0 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100c32 0 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_m32_r32_low_effect_step 0x100c32 0 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x100c36 [0x8B, 0x47, 0x2C] (LoadPre 0x100c36 (fun s => AddrMode.addr (.base 7 (.d8 0x2c)) s (0x100c36 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c36 0 (.base 7 (.d8 0x2c)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100c36 0 (.base 7 (.d8 0x2c))).toInstrSpec (mov_r32_m32_low_effect_step 0x100c36 0 (.base 7 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x100c39 [0x89, 0x44, 0x24, 0x20] (StorePre 0x100c39 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100c39 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c39 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100c39 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m32_r32_low_effect_step 0x100c39 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x100c3d [0x44, 0x8B, 0x47, 0x34] (LoadPre 0x100c3d (fun s => AddrMode.addr (.base 7 (.d8 0x34)) s (0x100c3d + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x100c3d 8 (.base 7 (.d8 0x34)))
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x100c3d 8 (.base 7 (.d8 0x34))).toInstrSpec (mov_r32_m32_effect_step 0x100c3d 0x44 (by decide) 0 (.base 7 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x100c41 [0x8B, 0x47, 0x38] (LoadPre 0x100c41 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x100c41 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c41 0 (.base 7 (.d8 0x38)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100c41 0 (.base 7 (.d8 0x38))).toInstrSpec (mov_r32_m32_low_effect_step 0x100c41 0 (.base 7 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x100c44 [0x89, 0x44, 0x24, 0x1C] (StorePre 0x100c44 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x100c44 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c44 0 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100c44 0 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m32_r32_low_effect_step 0x100c44 0 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x100c48 [0x8B, 0x47, 0x3C] (LoadPre 0x100c48 (fun s => AddrMode.addr (.base 7 (.d8 0x3c)) s (0x100c48 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c48 0 (.base 7 (.d8 0x3c)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100c48 0 (.base 7 (.d8 0x3c))).toInstrSpec (mov_r32_m32_low_effect_step 0x100c48 0 (.base 7 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x100c4b [0x89, 0x44, 0x24, 0x18] (StorePre 0x100c4b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100c4b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c4b 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100c4b 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m32_r32_low_effect_step 0x100c4b 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x100c4f [0x31, 0xFF] (fun s => s.RIP = 0x100c4f) (xorR32R32Effect 0x100c4f 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c4f 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x100c4f 0xff (by decide)) pre_rip
  have f32 : InstrSpec 0x100c51 [0x44, 0x89, 0x54, 0x24, 0x38] (StorePre 0x100c51 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x100c51 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100c51 10 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100c51 10 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m32_r32_effect_step 0x100c51 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x100c56 [0x44, 0x89, 0x9C, 0x24, 0x84, 0x00, 0x00, 0x00] (StorePre 0x100c56 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x100c56 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100c56 11 (.sib 4 none 0 (.d32 0x84)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100c56 11 (.sib 4 none 0 (.d32 0x84))).toInstrSpec (mov_m32_r32_effect_step 0x100c56 0x44 (by decide) 3 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x100c5e [0x44, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x100c5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x100c5e + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100c5e 8 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100c5e 8 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m32_r32_effect_step 0x100c5e 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x100c66 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100c66) (fun _ => nopEffect 0x100c66 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x100c66 10).toInstrSpec (nop_m_effect_step 0x100c66 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 84), (3, 3), (4, 4), (7, 7), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c2b) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 84), (3, 3), (4, 4), (7, 7), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c2f) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (3, 3), (4, 4), (7, 7), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c32) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 87), (3, 3), (4, 4), (7, 7), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c36) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (3, 3), (4, 4), (7, 7), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c39) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 90), (3, 3), (4, 4), (7, 7), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c3d) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f26 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 90), (3, 3), (4, 4), (7, 7), (8, 93), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c41) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (3, 3), (4, 4), (7, 7), (8, 93), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c44) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 95), (3, 3), (4, 4), (7, 7), (8, 93), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c48) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 98), (3, 3), (4, 4), (7, 7), (8, 93), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c4b) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 98), (3, 3), (4, 4), (7, 7), (8, 93), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c4f) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f31 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 98), (3, 3), (4, 4), (7, 101), (8, 93), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c51) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.exec (n := 103) (ρ' := [(0, 98), (3, 3), (4, 4), (7, 101), (8, 93), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c56) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 98), (3, 3), (4, 4), (7, 101), (8, 93), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c5e) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.exec (n := 105) (ρ' := [(0, 98), (3, 3), (4, 4), (7, 101), (8, 93), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c66) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 98), (3, 3), (4, 4), (7, 101), (8, 93), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c70) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 107) (by decide) rfl

theorem rest_l100bde [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100bde bytes_l100bde) (entryMap (live .l100bde))
      36 0x100bde bytes_l100bde b_l100bde := by
  have f0 : InstrSpec 0x100bde [0x4A, 0x8D, 0x04, 0x13] (fun s => s.RIP = 0x100bde) (leaR64Effect 0x100bde 0 (.sib 3 (some 10) 0 .none))
      [.gpr 3, .gpr 10] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x100bde 0 (.sib 3 (some 10) 0 .none)).toInstrSpec (lea_r64_effect_step 0x100bde 0x4a (by decide) 0 (.sib 3 (some 10) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100be2 [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x100be2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x100be2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100be2 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100be2 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x100be2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x100be7 [0x4B, 0x8D, 0x04, 0x16] (fun s => s.RIP = 0x100be7) (leaR64Effect 0x100be7 0 (.sib 14 (some 10) 0 .none))
      [.gpr 14, .gpr 10] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x100be7 0 (.sib 14 (some 10) 0 .none)).toInstrSpec (lea_r64_effect_step 0x100be7 0x4b (by decide) 0 (.sib 14 (some 10) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100beb [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x100beb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x100beb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100beb 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100beb 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x100beb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x100bf0 [0x8B, 0x07] (LoadPre 0x100bf0 (fun s => AddrMode.addr (.base 7 .none) s (0x100bf0 + BitVec.ofNat 64 2)) 4) (movR32M32LowEffect 0x100bf0 0 (.base 7 .none))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100bf0 0 (.base 7 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x100bf0 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x100bf2 [0x89, 0x44, 0x24, 0x58] (StorePre 0x100bf2 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100bf2 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100bf2 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100bf2 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m32_r32_low_effect_step 0x100bf2 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x100bf6 [0x8B, 0x47, 0x04] (LoadPre 0x100bf6 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x100bf6 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100bf6 0 (.base 7 (.d8 0x4)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100bf6 0 (.base 7 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x100bf6 0 (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x100bf9 [0x89, 0x44, 0x24, 0x10] (StorePre 0x100bf9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100bf9 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100bf9 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100bf9 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_low_effect_step 0x100bf9 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x100bfd [0x8B, 0x47, 0x08] (LoadPre 0x100bfd (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x100bfd + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100bfd 0 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100bfd 0 (.base 7 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x100bfd 0 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x100c00 [0x89, 0x44, 0x24, 0x0C] (StorePre 0x100c00 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100c00 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c00 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100c00 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x100c00 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x100c04 [0x8B, 0x47, 0x0C] (LoadPre 0x100c04 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x100c04 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c04 0 (.base 7 (.d8 0xc)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100c04 0 (.base 7 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x100c04 0 (.base 7 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x100c07 [0x89, 0x44, 0x24, 0x40] (StorePre 0x100c07 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100c07 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c07 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100c07 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m32_r32_low_effect_step 0x100c07 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x100c0b [0x44, 0x8B, 0x57, 0x10] (LoadPre 0x100c0b (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x100c0b + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x100c0b 10 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x100c0b 10 (.base 7 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x100c0b 0x44 (by decide) 2 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x100c0f [0x8B, 0x47, 0x14] (LoadPre 0x100c0f (fun s => AddrMode.addr (.base 7 (.d8 0x14)) s (0x100c0f + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c0f 0 (.base 7 (.d8 0x14)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100c0f 0 (.base 7 (.d8 0x14))).toInstrSpec (mov_r32_m32_low_effect_step 0x100c0f 0 (.base 7 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x100c12 [0x89, 0x44, 0x24, 0x34] (StorePre 0x100c12 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x100c12 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c12 0 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100c12 0 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x100c12 0 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x100c16 [0x8B, 0x47, 0x18] (LoadPre 0x100c16 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x100c16 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c16 0 (.base 7 (.d8 0x18)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100c16 0 (.base 7 (.d8 0x18))).toInstrSpec (mov_r32_m32_low_effect_step 0x100c16 0 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x100c19 [0x89, 0x44, 0x24, 0x30] (StorePre 0x100c19 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100c19 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c19 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100c19 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m32_r32_low_effect_step 0x100c19 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x100c1d [0x8B, 0x47, 0x1C] (LoadPre 0x100c1d (fun s => AddrMode.addr (.base 7 (.d8 0x1c)) s (0x100c1d + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c1d 0 (.base 7 (.d8 0x1c)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100c1d 0 (.base 7 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x100c1d 0 (.base 7 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x100c20 [0x89, 0x44, 0x24, 0x2C] (StorePre 0x100c20 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x100c20 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c20 0 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100c20 0 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_m32_r32_low_effect_step 0x100c20 0 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x100c24 [0x44, 0x8B, 0x5F, 0x20] (LoadPre 0x100c24 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x100c24 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x100c24 11 (.base 7 (.d8 0x20)))
      [.gpr 7] [] [.reg 11, .rip] :=
    (movR32M32Effect_footprint 0x100c24 11 (.base 7 (.d8 0x20))).toInstrSpec (mov_r32_m32_effect_step 0x100c24 0x44 (by decide) 3 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (7, 7), (10, 10), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100be2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (7, 7), (10, 10), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100be7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (7, 7), (10, 10), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100beb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (7, 7), (10, 10), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bf0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (7, 7), (10, 10), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bf2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (7, 7), (10, 10), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bf6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (7, 7), (10, 10), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bf9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (7, 7), (10, 10), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bfd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (7, 7), (10, 10), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c00) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (7, 7), (10, 10), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c04) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (7, 7), (10, 10), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c07) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (7, 7), (10, 10), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c0b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 68), (3, 3), (4, 4), (7, 7), (10, 71), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c0f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (3, 3), (4, 4), (7, 7), (10, 71), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c12) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 73), (3, 3), (4, 4), (7, 7), (10, 71), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c16) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (3, 3), (4, 4), (7, 7), (10, 71), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c19) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 76), (3, 3), (4, 4), (7, 7), (10, 71), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c1d) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (3, 3), (4, 4), (7, 7), (10, 71), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c20) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (3, 3), (4, 4), (7, 7), (10, 71), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c24) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f19 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 79), (3, 3), (4, 4), (7, 7), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c28) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100bde_1 code

theorem block_l100bde [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100bde :=
  Rest.liftedBlock (rest_l100bde code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100bde x hx)

theorem rest_l100c70_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x100c70 bytes_l100c70) [(0, 71), (1, 67), (2, 75), (3, 57), (4, 4), (5, 59), (6, 79), (7, 69), (8, 87), (9, 62), (10, 81), (11, 83), (12, 73), (13, 65), (14, 77), (15, 85), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x100cc9 bytes_l100c70_1 b_l100c70_1 := by
  have f20 : InstrSpec 0x100cc9 [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100cc9) (fun _ => nopEffect 0x100cc9 7)
      [] [] [.rip] :=
    (nopEffect_footprint 0x100cc9 7).toInstrSpec (nop_m_effect_step 0x100cc9 [] (by decide) (by decide) (.base 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 71), (1, 67), (2, 75), (3, 57), (4, 4), (5, 59), (6, 79), (7, 69), (8, 87), (9, 62), (10, 81), (11, 83), (12, 73), (13, 65), (14, 77), (15, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cd0) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 90) (by decide) rfl

theorem rest_l100c70 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100c70 bytes_l100c70) (entryMap (live .l100c70))
      21 0x100c70 bytes_l100c70 b_l100c70 := by
  have f0 : InstrSpec 0x100c70 [0x48, 0x89, 0x7C, 0x24, 0x70] (StorePre 0x100c70 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x100c70 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100c70 7 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100c70 7 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x100c70 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x100c75 [0xB8, 0x0A, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100c75) (movR32Imm32Effect 0x100c75 5 0 0xa)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x100c75 5 0 0xa).toInstrSpec (mov_r32_imm32_effect_step 0x100c75 0xb8 (by decide) 0xa) pre_rip
  have f2 : InstrSpec 0x100c7a [0x48, 0x89, 0x44, 0x24, 0x78] (StorePre 0x100c7a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x100c7a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100c7a 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100c7a 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x100c7a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100c7f [0x8B, 0x5C, 0x24, 0x58] (LoadPre 0x100c7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100c7f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100c7f 3 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR32M32LowEffect_footprint 0x100c7f 3 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r32_m32_low_effect_step 0x100c7f 3 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x100c83 [0x44, 0x89, 0xD5] (fun s => s.RIP = 0x100c83) (movR32R32Effect 0x100c83 3 5 10)
      [.gpr 10] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x100c83 3 5 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x100c83 0x44 0xd5 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x100c86 [0x44, 0x89, 0x64, 0x24, 0x3C] (StorePre 0x100c86 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x100c86 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100c86 12 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100c86 12 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_m32_r32_effect_step 0x100c86 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x100c8b [0x45, 0x89, 0xE1] (fun s => s.RIP = 0x100c8b) (movR32R32Effect 0x100c8b 3 9 12)
      [.gpr 12] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x100c8b 3 9 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x100c8b 0x45 0xe1 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100c8e [0x44, 0x89, 0x5C, 0x24, 0x04] (StorePre 0x100c8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100c8e + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100c8e 11 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100c8e 11 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_effect_step 0x100c8e 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x100c93 [0x44, 0x8B, 0x6C, 0x24, 0x10] (LoadPre 0x100c93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100c93 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100c93 13 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR32M32Effect_footprint 0x100c93 13 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x100c93 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x100c98 [0x8B, 0x4C, 0x24, 0x34] (LoadPre 0x100c98 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x100c98 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100c98 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x100c98 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x100c98 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x100c9c [0x44, 0x89, 0xC7] (fun s => s.RIP = 0x100c9c) (movR32R32Effect 0x100c9c 3 7 8)
      [.gpr 8] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x100c9c 3 7 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x100c9c 0x44 0xc7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x100c9f [0x8B, 0x44, 0x24, 0x28] (LoadPre 0x100c9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100c9f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100c9f 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100c9f 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r32_m32_low_effect_step 0x100c9f 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x100ca3 [0x44, 0x8B, 0x64, 0x24, 0x0C] (LoadPre 0x100ca3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100ca3 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100ca3 12 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR32M32Effect_footprint 0x100ca3 12 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_effect_step 0x100ca3 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x100ca8 [0x8B, 0x54, 0x24, 0x30] (LoadPre 0x100ca8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100ca8 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100ca8 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x100ca8 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r32_m32_low_effect_step 0x100ca8 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x100cac [0x44, 0x8B, 0x74, 0x24, 0x1C] (LoadPre 0x100cac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x100cac + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100cac 14 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR32M32Effect_footprint 0x100cac 14 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x100cac 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x100cb1 [0x8B, 0x74, 0x24, 0x24] (LoadPre 0x100cb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x100cb1 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100cb1 6 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x100cb1 6 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r32_m32_low_effect_step 0x100cb1 6 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x100cb5 [0x44, 0x8B, 0x54, 0x24, 0x40] (LoadPre 0x100cb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100cb5 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100cb5 10 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x100cb5 10 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r32_m32_effect_step 0x100cb5 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x100cba [0x44, 0x8B, 0x5C, 0x24, 0x2C] (LoadPre 0x100cba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x100cba + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100cba 11 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR32M32Effect_footprint 0x100cba 11 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r32_m32_effect_step 0x100cba 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x100cbf [0x44, 0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x100cbf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100cbf + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100cbf 15 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x100cbf 15 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x100cbf 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x100cc4 [0x44, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x100cc4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100cc4 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100cc4 8 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x100cc4 8 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r32_m32_effect_step 0x100cc4 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c75) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (4, 4), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c7a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (4, 4), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c7f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 54), (3, 57), (4, 4), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c83) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 54), (3, 57), (4, 4), (5, 59), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c86) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 54), (3, 57), (4, 4), (5, 59), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c8b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 54), (3, 57), (4, 4), (5, 59), (7, 7), (8, 8), (9, 62), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c8e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 54), (3, 57), (4, 4), (5, 59), (7, 7), (8, 8), (9, 62), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c93) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 54), (3, 57), (4, 4), (5, 59), (7, 7), (8, 8), (9, 62), (10, 10), (11, 11), (12, 12), (13, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c98) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 54), (1, 67), (3, 57), (4, 4), (5, 59), (7, 7), (8, 8), (9, 62), (10, 10), (11, 11), (12, 12), (13, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c9c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 54), (1, 67), (3, 57), (4, 4), (5, 59), (7, 69), (8, 8), (9, 62), (10, 10), (11, 11), (12, 12), (13, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c9f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 67), (3, 57), (4, 4), (5, 59), (7, 69), (8, 8), (9, 62), (10, 10), (11, 11), (12, 12), (13, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ca3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 67), (3, 57), (4, 4), (5, 59), (7, 69), (8, 8), (9, 62), (10, 10), (11, 11), (12, 73), (13, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ca8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 67), (2, 75), (3, 57), (4, 4), (5, 59), (7, 69), (8, 8), (9, 62), (10, 10), (11, 11), (12, 73), (13, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cac) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 67), (2, 75), (3, 57), (4, 4), (5, 59), (7, 69), (8, 8), (9, 62), (10, 10), (11, 11), (12, 73), (13, 65), (14, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cb1) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 71), (1, 67), (2, 75), (3, 57), (4, 4), (5, 59), (6, 79), (7, 69), (8, 8), (9, 62), (10, 10), (11, 11), (12, 73), (13, 65), (14, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cb5) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 71), (1, 67), (2, 75), (3, 57), (4, 4), (5, 59), (6, 79), (7, 69), (8, 8), (9, 62), (10, 81), (11, 11), (12, 73), (13, 65), (14, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cba) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 71), (1, 67), (2, 75), (3, 57), (4, 4), (5, 59), (6, 79), (7, 69), (8, 8), (9, 62), (10, 81), (11, 83), (12, 73), (13, 65), (14, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cbf) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 71), (1, 67), (2, 75), (3, 57), (4, 4), (5, 59), (6, 79), (7, 69), (8, 8), (9, 62), (10, 81), (11, 83), (12, 73), (13, 65), (14, 77), (15, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cc4) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 71), (1, 67), (2, 75), (3, 57), (4, 4), (5, 59), (6, 79), (7, 69), (8, 87), (9, 62), (10, 81), (11, 83), (12, 73), (13, 65), (14, 77), (15, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cc9) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100c70_1 code

theorem block_l100c70 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100c70 :=
  Rest.liftedBlock (rest_l100c70 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100c70 x hx)

theorem rest_l100cd0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100cd0 bytes_l100cd0) (entryMap (live .l100cd0))
      16 0x100cd0 bytes_l100cd0 b_l100cd0 := by
  have f0 : InstrSpec 0x100cd0 [0x89, 0x74, 0x24, 0x14] (StorePre 0x100cd0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100cd0 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100cd0 6 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100cd0 6 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m32_r32_low_effect_step 0x100cd0 6 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x100cd4 [0x01, 0xEB] (fun s => s.RIP = 0x100cd4) (addR32R32Effect 0x100cd4 2 3 5)
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100cd4 2 3 5).toInstrSpec (add_r32_r32_effect_step 0x100cd4 0xeb (by decide)) pre_rip
  have f2 : InstrSpec 0x100cd6 [0x41, 0x31, 0xD9] (fun s => s.RIP = 0x100cd6) (xorR32R32Effect 0x100cd6 3 9 3)
      [.gpr 9, .gpr 3] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100cd6 3 9 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x100cd6 0x41 0xd9 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100cd9 [0x41, 0xC1, 0xC1, 0x10] (fun s => s.RIP = 0x100cd9) (rolR32Effect 0x100cd9 4 9 16)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (rolR32Effect_footprint 0x100cd9 4 9 16).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100cd9 0x41 0xc1 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100cdd [0x8B, 0x74, 0x24, 0x04] (LoadPre 0x100cdd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100cdd + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100cdd 6 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x100cdd 6 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x100cdd 6 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x100ce1 [0x44, 0x01, 0xCE] (fun s => s.RIP = 0x100ce1) (addR32R32Effect 0x100ce1 3 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100ce1 3 6 9).toInstrSpec (add_r32_r32_rex_effect_step 0x100ce1 0x44 0xce (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100ce4 [0x31, 0xF5] (fun s => s.RIP = 0x100ce4) (xorR32R32Effect 0x100ce4 2 5 6)
      [.gpr 5, .gpr 6] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100ce4 2 5 6).toInstrSpec (xor_r32_r32_effect_step 0x100ce4 0xf5 (by decide)) pre_rip
  have f7 : InstrSpec 0x100ce6 [0xC1, 0xC5, 0x0C] (fun s => s.RIP = 0x100ce6) (rolR32Effect 0x100ce6 3 5 12)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (rolR32Effect_footprint 0x100ce6 3 5 12).toInstrSpec (rol_r32_imm8_effect_step 0x100ce6 0xc5 0xc (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100ce9 [0x01, 0xEB] (fun s => s.RIP = 0x100ce9) (addR32R32Effect 0x100ce9 2 3 5)
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100ce9 2 3 5).toInstrSpec (add_r32_r32_effect_step 0x100ce9 0xeb (by decide)) pre_rip
  have f9 : InstrSpec 0x100ceb [0x41, 0x31, 0xD9] (fun s => s.RIP = 0x100ceb) (xorR32R32Effect 0x100ceb 3 9 3)
      [.gpr 9, .gpr 3] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100ceb 3 9 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x100ceb 0x41 0xd9 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x100cee [0x41, 0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x100cee) (rolR32Effect 0x100cee 4 9 8)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (rolR32Effect_footprint 0x100cee 4 9 8).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100cee 0x41 0xc1 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x100cf2 [0x44, 0x01, 0xCE] (fun s => s.RIP = 0x100cf2) (addR32R32Effect 0x100cf2 3 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100cf2 3 6 9).toInstrSpec (add_r32_r32_rex_effect_step 0x100cf2 0x44 0xce (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x100cf5 [0x89, 0x74, 0x24, 0x04] (StorePre 0x100cf5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100cf5 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100cf5 6 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100cf5 6 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x100cf5 6 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x100cf9 [0x31, 0xF5] (fun s => s.RIP = 0x100cf9) (xorR32R32Effect 0x100cf9 2 5 6)
      [.gpr 5, .gpr 6] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100cf9 2 5 6).toInstrSpec (xor_r32_r32_effect_step 0x100cf9 0xf5 (by decide)) pre_rip
  have f14 : InstrSpec 0x100cfb [0x8B, 0x74, 0x24, 0x14] (LoadPre 0x100cfb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100cfb + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100cfb 6 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x100cfb 6 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_low_effect_step 0x100cfb 6 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x100cff [0xC1, 0xC5, 0x07] (fun s => s.RIP = 0x100cff) (rolR32Effect 0x100cff 3 5 7)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (rolR32Effect_footprint 0x100cff 3 5 7).toInstrSpec (rol_r32_imm8_effect_step 0x100cff 0xc5 0x7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cd4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 54), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cd6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 54), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 56), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cd9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 54), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cdd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 54), (4, 4), (5, 5), (6, 60), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ce1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 54), (4, 4), (5, 5), (6, 62), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ce4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 54), (4, 4), (5, 64), (6, 62), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ce6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 54), (4, 4), (5, 66), (6, 62), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ce9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 66), (6, 62), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ceb) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 66), (6, 62), (7, 7), (8, 8), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cee) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 66), (6, 62), (7, 7), (8, 8), (9, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cf2) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 66), (6, 74), (7, 7), (8, 8), (9, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cf5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 66), (6, 74), (7, 7), (8, 8), (9, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cf9) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 77), (6, 74), (7, 7), (8, 8), (9, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cfb) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 77), (6, 79), (7, 7), (8, 8), (9, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cff) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 81), (6, 79), (7, 7), (8, 8), (9, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d02) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 83) (by decide) rfl

theorem block_l100cd0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100cd0 :=
  Rest.liftedBlock (rest_l100cd0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100cd0 x hx)

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

theorem_by block_l100a80_eval :
    program.runBlock (dialect code) ⟨.l100a80, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100aae_eval :
    program.runBlock (dialect code) ⟨.l100aae, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100ad0_eval :
    program.runBlock (dialect code) ⟨.l100ad0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100b04_eval :
    program.runBlock (dialect code) ⟨.l100b04, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100b10_eval :
    program.runBlock (dialect code) ⟨.l100b10, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100b14_eval :
    program.runBlock (dialect code) ⟨.l100b14, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100b30_eval :
    program.runBlock (dialect code) ⟨.l100b30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100b76_eval :
    program.runBlock (dialect code) ⟨.l100b76, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100b7b_eval :
    program.runBlock (dialect code) ⟨.l100b7b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100b90_eval :
    program.runBlock (dialect code) ⟨.l100b90, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100ba5_eval :
    program.runBlock (dialect code) ⟨.l100ba5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100bde_eval :
    program.runBlock (dialect code) ⟨.l100bde, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100c70_eval :
    program.runBlock (dialect code) ⟨.l100c70, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100cd0_eval :
    program.runBlock (dialect code) ⟨.l100cd0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
