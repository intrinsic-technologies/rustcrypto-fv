import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Program
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Values

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

theorem rest_l101ce0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101ce0 bytes_l101ce0) (entryMap (live .l101ce0))
      20 0x101ce0 bytes_l101ce0 b_l101ce0 := by
  have f0 : InstrSpec 0x101ce0 [0x55] (PushPre 0x101ce0 1) (pushR64Effect 0x101ce0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101ce0 1 5).toInstrSpec (push_r64_effect_step 0x101ce0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x101ce1 [0x41, 0x57] (PushPre 0x101ce1 2) (pushR64Effect 0x101ce1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101ce1 2 15).toInstrSpec (push_r64_rex_effect_step 0x101ce1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101ce3 [0x41, 0x56] (PushPre 0x101ce3 2) (pushR64Effect 0x101ce3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101ce3 2 14).toInstrSpec (push_r64_rex_effect_step 0x101ce3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101ce5 [0x41, 0x55] (PushPre 0x101ce5 2) (pushR64Effect 0x101ce5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101ce5 2 13).toInstrSpec (push_r64_rex_effect_step 0x101ce5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101ce7 [0x41, 0x54] (PushPre 0x101ce7 2) (pushR64Effect 0x101ce7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101ce7 2 12).toInstrSpec (push_r64_rex_effect_step 0x101ce7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x101ce9 [0x53] (PushPre 0x101ce9 1) (pushR64Effect 0x101ce9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101ce9 1 3).toInstrSpec (push_r64_effect_step 0x101ce9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x101cea [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x101cea) (movR64R64Effect 0x101cea 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101cea 0 7).toInstrSpec (mov_r64_r64_effect_step 0x101cea 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101ced [0x44, 0x8B, 0x5E, 0x28] (LoadPre 0x101ced (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x101ced + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101ced 11 (.base 6 (.d8 0x28)))
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR32M32Effect_footprint 0x101ced 11 (.base 6 (.d8 0x28))).toInstrSpec (mov_r32_m32_effect_step 0x101ced 0x44 (by decide) 3 (.base 6 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x101cf1 [0x44, 0x89, 0xD9] (fun s => s.RIP = 0x101cf1) (movR32R32Effect 0x101cf1 3 1 11)
      [.gpr 11] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x101cf1 3 1 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x101cf1 0x44 0xd9 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101cf4 [0xC1, 0xE9, 0x1A] (fun s => s.RIP = 0x101cf4) (shrR32Effect 0x101cf4 3 1 26)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x101cf4 3 1 26).toInstrSpec (shr_r32_imm8_effect_step 0x101cf4 0xe9 0x1a (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101cf7 [0x03, 0x4E, 0x2C] (LoadPre 0x101cf7 (fun s => AddrMode.addr (.base 6 (.d8 0x2c)) s (0x101cf7 + BitVec.ofNat 64 3)) 4) (addR32M32Effect 0x101cf7 3 1 (.base 6 (.d8 0x2c)))
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101cf7 3 1 (.base 6 (.d8 0x2c))).toInstrSpec (add_r32_m32_effect_step 0x101cf7 1 (.base 6 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x101cfa [0x41, 0x81, 0xE3, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101cfa) (andR32Imm32Effect 0x101cfa 7 11 0x3ffffff)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101cfa 7 11 0x3ffffff).toInstrSpec (and_r32_imm32_rex_effect_step 0x101cfa 0x41 0xe3 0x3ffffff (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101d01 [0x89, 0xCA] (fun s => s.RIP = 0x101d01) (movR32R32Effect 0x101d01 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x101d01 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x101d01 0xca (by decide)) pre_rip
  have f13 : InstrSpec 0x101d03 [0xC1, 0xEA, 0x1A] (fun s => s.RIP = 0x101d03) (shrR32Effect 0x101d03 3 2 26)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x101d03 3 2 26).toInstrSpec (shr_r32_imm8_effect_step 0x101d03 0xea 0x1a (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101d06 [0x81, 0xE1, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101d06) (andR32Imm32Effect 0x101d06 6 1 0x3ffffff)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101d06 6 1 0x3ffffff).toInstrSpec (and_r32_imm32_effect_step 0x101d06 0xe1 0x3ffffff (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x101d0c [0x03, 0x56, 0x30] (LoadPre 0x101d0c (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x101d0c + BitVec.ofNat 64 3)) 4) (addR32M32Effect 0x101d0c 3 2 (.base 6 (.d8 0x30)))
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101d0c 3 2 (.base 6 (.d8 0x30))).toInstrSpec (add_r32_m32_effect_step 0x101d0c 2 (.base 6 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x101d0f [0x41, 0x89, 0xD0] (fun s => s.RIP = 0x101d0f) (movR32R32Effect 0x101d0f 3 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x101d0f 3 8 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x101d0f 0x41 0xd0 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x101d12 [0x41, 0xC1, 0xE8, 0x1A] (fun s => s.RIP = 0x101d12) (shrR32Effect 0x101d12 4 8 26)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x101d12 4 8 26).toInstrSpec (shr_r32_imm8_rex_effect_step 0x101d12 0x41 0xe8 0x1a (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x101d16 [0x81, 0xE2, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101d16) (andR32Imm32Effect 0x101d16 6 2 0x3ffffff)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101d16 6 2 0x3ffffff).toInstrSpec (and_r32_imm32_effect_step 0x101d16 0xe2 0x3ffffff (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x101d1c [0x44, 0x03, 0x46, 0x34] (LoadPre 0x101d1c (fun s => AddrMode.addr (.base 6 (.d8 0x34)) s (0x101d1c + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101d1c 4 8 (.base 6 (.d8 0x34)))
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101d1c 4 8 (.base 6 (.d8 0x34))).toInstrSpec (add_r32_m32_rex_effect_step 0x101d1c 0x44 (by decide) 0 (.base 6 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ce1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ce3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ce5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ce7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ce9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cea) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ced) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cf1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 69), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cf4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (1, 71), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cf7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 65), (1, 73), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101cfa) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 65), (1, 73), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (11, 75), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d01) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 65), (1, 73), (2, 77), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (11, 75), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d03) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 65), (1, 73), (2, 79), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (11, 75), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d06) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 65), (1, 81), (2, 79), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (11, 75), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d0c) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 65), (1, 81), (2, 83), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (11, 75), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d0f) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 65), (1, 81), (2, 83), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 85), (11, 75), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d12) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 65), (1, 81), (2, 83), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 87), (11, 75), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d16) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 65), (1, 81), (2, 89), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 87), (11, 75), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d1c) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 65), (1, 81), (2, 89), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 91), (11, 75), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d20) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 93) (by decide) rfl

theorem block_l101ce0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101ce0 :=
  Rest.liftedBlock (rest_l101ce0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101ce0 x hx)

theorem rest_l101d20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101d20 bytes_l101d20) (entryMap (live .l101d20))
      20 0x101d20 bytes_l101d20 b_l101d20 := by
  have f0 : InstrSpec 0x101d20 [0x45, 0x89, 0xC1] (fun s => s.RIP = 0x101d20) (movR32R32Effect 0x101d20 3 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x101d20 3 9 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x101d20 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101d23 [0x41, 0xC1, 0xE9, 0x1A] (fun s => s.RIP = 0x101d23) (shrR32Effect 0x101d23 4 9 26)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x101d23 4 9 26).toInstrSpec (shr_r32_imm8_rex_effect_step 0x101d23 0x41 0xe9 0x1a (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101d27 [0x44, 0x89, 0xC7] (fun s => s.RIP = 0x101d27) (movR32R32Effect 0x101d27 3 7 8)
      [.gpr 8] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x101d27 3 7 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x101d27 0x44 0xc7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101d2a [0x81, 0xE7, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101d2a) (andR32Imm32Effect 0x101d2a 6 7 0x3ffffff)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101d2a 6 7 0x3ffffff).toInstrSpec (and_r32_imm32_effect_step 0x101d2a 0xe7 0x3ffffff (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101d30 [0x47, 0x8D, 0x14, 0x89] (fun s => s.RIP = 0x101d30) (leaR32Effect 0x101d30 4 10 (.sib 9 (some 9) 2 .none))
      [.gpr 9, .gpr 9] [] [.reg 10, .rip] :=
    (leaR32Effect_footprint 0x101d30 4 10 (.sib 9 (some 9) 2 .none)).toInstrSpec (lea_r32_rex_effect_step 0x101d30 0x47 (by decide) 2 (.sib 9 (some 9) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101d34 [0x44, 0x03, 0x56, 0x24] (LoadPre 0x101d34 (fun s => AddrMode.addr (.base 6 (.d8 0x24)) s (0x101d34 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101d34 4 10 (.base 6 (.d8 0x24)))
      [.gpr 10, .gpr 6] [] [.reg 10, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101d34 4 10 (.base 6 (.d8 0x24))).toInstrSpec (add_r32_m32_rex_effect_step 0x101d34 0x44 (by decide) 2 (.base 6 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x101d38 [0x45, 0x89, 0xD1] (fun s => s.RIP = 0x101d38) (movR32R32Effect 0x101d38 3 9 10)
      [.gpr 10] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x101d38 3 9 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x101d38 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101d3b [0x41, 0xC1, 0xE9, 0x1A] (fun s => s.RIP = 0x101d3b) (shrR32Effect 0x101d3b 4 9 26)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x101d3b 4 9 26).toInstrSpec (shr_r32_imm8_rex_effect_step 0x101d3b 0x41 0xe9 0x1a (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101d3f [0x45, 0x01, 0xD9] (fun s => s.RIP = 0x101d3f) (addR32R32Effect 0x101d3f 3 9 11)
      [.gpr 9, .gpr 11] [] [.reg 9, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101d3f 3 9 11).toInstrSpec (add_r32_r32_rex_effect_step 0x101d3f 0x45 0xd9 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101d42 [0x41, 0x81, 0xE2, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101d42) (andR32Imm32Effect 0x101d42 7 10 0x3ffffff)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101d42 7 10 0x3ffffff).toInstrSpec (and_r32_imm32_rex_effect_step 0x101d42 0x41 0xe2 0x3ffffff (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101d49 [0x41, 0x8D, 0x6A, 0x05] (fun s => s.RIP = 0x101d49) (leaR32Effect 0x101d49 4 5 (.base 10 (.d8 0x5)))
      [.gpr 10] [] [.reg 5, .rip] :=
    (leaR32Effect_footprint 0x101d49 4 5 (.base 10 (.d8 0x5))).toInstrSpec (lea_r32_rex_effect_step 0x101d49 0x41 (by decide) 5 (.base 10 (.d8 0x5)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101d4d [0x41, 0x89, 0xEB] (fun s => s.RIP = 0x101d4d) (movR32R32Effect 0x101d4d 3 11 5)
      [.gpr 5] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x101d4d 3 11 5).toInstrSpec (mov_r32_r32_rex_effect_step 0x101d4d 0x41 0xeb (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101d50 [0x41, 0xC1, 0xEB, 0x1A] (fun s => s.RIP = 0x101d50) (shrR32Effect 0x101d50 4 11 26)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x101d50 4 11 26).toInstrSpec (shr_r32_imm8_rex_effect_step 0x101d50 0x41 0xeb 0x1a (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101d54 [0x45, 0x01, 0xCB] (fun s => s.RIP = 0x101d54) (addR32R32Effect 0x101d54 3 11 9)
      [.gpr 11, .gpr 9] [] [.reg 11, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101d54 3 11 9).toInstrSpec (add_r32_r32_rex_effect_step 0x101d54 0x45 0xcb (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101d57 [0x44, 0x89, 0xDB] (fun s => s.RIP = 0x101d57) (movR32R32Effect 0x101d57 3 3 11)
      [.gpr 11] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x101d57 3 3 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x101d57 0x44 0xdb (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x101d5a [0xC1, 0xEB, 0x1A] (fun s => s.RIP = 0x101d5a) (shrR32Effect 0x101d5a 3 3 26)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR32Effect_footprint 0x101d5a 3 3 26).toInstrSpec (shr_r32_imm8_effect_step 0x101d5a 0xeb 0x1a (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x101d5d [0x01, 0xCB] (fun s => s.RIP = 0x101d5d) (addR32R32Effect 0x101d5d 2 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101d5d 2 3 1).toInstrSpec (add_r32_r32_effect_step 0x101d5d 0xcb (by decide)) pre_rip
  have f17 : InstrSpec 0x101d5f [0x41, 0x89, 0xDF] (fun s => s.RIP = 0x101d5f) (movR32R32Effect 0x101d5f 3 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x101d5f 3 15 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x101d5f 0x41 0xdf (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x101d62 [0x41, 0xC1, 0xEF, 0x1A] (fun s => s.RIP = 0x101d62) (shrR32Effect 0x101d62 4 15 26)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR32Effect_footprint 0x101d62 4 15 26).toInstrSpec (shr_r32_imm8_rex_effect_step 0x101d62 0x41 0xef 0x1a (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x101d66 [0x41, 0x01, 0xD7] (fun s => s.RIP = 0x101d66) (addR32R32Effect 0x101d66 3 15 2)
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101d66 3 15 2).toInstrSpec (add_r32_r32_rex_effect_step 0x101d66 0x41 0xd7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (8, 8), (9, 53), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d23) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (8, 8), (9, 55), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d27) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 57), (8, 8), (9, 55), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d2a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 59), (8, 8), (9, 55), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d30) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 59), (8, 8), (9, 55), (10, 61), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d34) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 59), (8, 8), (9, 55), (10, 63), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d38) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 59), (8, 8), (9, 65), (10, 63), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d3b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 59), (8, 8), (9, 67), (10, 63), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d3f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 59), (8, 8), (9, 69), (10, 63), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d42) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 59), (8, 8), (9, 69), (10, 71), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d49) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 73), (6, 6), (7, 59), (8, 8), (9, 69), (10, 71), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d4d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 73), (6, 6), (7, 59), (8, 8), (9, 69), (10, 71), (11, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d50) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 73), (6, 6), (7, 59), (8, 8), (9, 69), (10, 71), (11, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d54) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 73), (6, 6), (7, 59), (8, 8), (9, 69), (10, 71), (11, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d57) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 81), (4, 4), (5, 73), (6, 6), (7, 59), (8, 8), (9, 69), (10, 71), (11, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d5a) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 83), (4, 4), (5, 73), (6, 6), (7, 59), (8, 8), (9, 69), (10, 71), (11, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d5d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 85), (4, 4), (5, 73), (6, 6), (7, 59), (8, 8), (9, 69), (10, 71), (11, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d5f) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 85), (4, 4), (5, 73), (6, 6), (7, 59), (8, 8), (9, 69), (10, 71), (11, 79), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d62) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 85), (4, 4), (5, 73), (6, 6), (7, 59), (8, 8), (9, 69), (10, 71), (11, 79), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d66) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 85), (4, 4), (5, 73), (6, 6), (7, 59), (8, 8), (9, 69), (10, 71), (11, 79), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d69) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 93) (by decide) rfl

theorem block_l101d20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101d20 :=
  Rest.liftedBlock (rest_l101d20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101d20 x hx)

theorem rest_l101d69 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101d69 bytes_l101d69) (entryMap (live .l101d69))
      20 0x101d69 bytes_l101d69 b_l101d69 := by
  have f0 : InstrSpec 0x101d69 [0x45, 0x89, 0xFC] (fun s => s.RIP = 0x101d69) (movR32R32Effect 0x101d69 3 12 15)
      [.gpr 15] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x101d69 3 12 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x101d69 0x45 0xfc (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101d6c [0x41, 0xC1, 0xEC, 0x1A] (fun s => s.RIP = 0x101d6c) (shrR32Effect 0x101d6c 4 12 26)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR32Effect_footprint 0x101d6c 4 12 26).toInstrSpec (shr_r32_imm8_rex_effect_step 0x101d6c 0x41 0xec 0x1a (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101d70 [0x45, 0x8D, 0x34, 0x3C] (fun s => s.RIP = 0x101d70) (leaR32Effect 0x101d70 4 14 (.sib 12 (some 7) 0 .none))
      [.gpr 12, .gpr 7] [] [.reg 14, .rip] :=
    (leaR32Effect_footprint 0x101d70 4 14 (.sib 12 (some 7) 0 .none)).toInstrSpec (lea_r32_rex_effect_step 0x101d70 0x45 (by decide) 6 (.sib 12 (some 7) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101d74 [0x41, 0x81, 0xC6, 0x00, 0x00, 0x00, 0xFC] (fun s => s.RIP = 0x101d74) (addR32Imm32Effect 0x101d74 7 14 0xfc000000)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (addR32Imm32Effect_footprint 0x101d74 7 14 0xfc000000).toInstrSpec (add_r32_imm32_rex_effect_step 0x101d74 0x41 0xc6 0xfc000000 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101d7b [0x41, 0x01, 0xFC] (fun s => s.RIP = 0x101d7b) (addR32R32Effect 0x101d7b 3 12 7)
      [.gpr 12, .gpr 7] [] [.reg 12, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101d7b 3 12 7).toInstrSpec (add_r32_r32_rex_effect_step 0x101d7b 0x41 0xfc (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101d7e [0x44, 0x89, 0xF7] (fun s => s.RIP = 0x101d7e) (movR32R32Effect 0x101d7e 3 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x101d7e 3 7 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x101d7e 0x44 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101d81 [0xC1, 0xFF, 0x1F] (fun s => s.RIP = 0x101d81) (sarR32Effect 0x101d81 3 7 31)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (sarR32Effect_footprint 0x101d81 3 7 31).toInstrSpec (sar_r32_imm8_effect_step 0x101d81 0xff 0x1f (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101d84 [0x41, 0xC1, 0xEE, 0x1F] (fun s => s.RIP = 0x101d84) (shrR32Effect 0x101d84 4 14 31)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR32Effect_footprint 0x101d84 4 14 31).toInstrSpec (shr_r32_imm8_rex_effect_step 0x101d84 0x41 0xee 0x1f (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101d88 [0x41, 0xFF, 0xCE] (fun s => s.RIP = 0x101d88) (decR32Effect 0x101d88 3 14)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (decR32Effect_footprint 0x101d88 3 14).toInstrSpec (dec_r32_rex_effect_step 0x101d88 0x41 0xce (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101d8b [0x45, 0x89, 0xF5] (fun s => s.RIP = 0x101d8b) (movR32R32Effect 0x101d8b 3 13 14)
      [.gpr 14] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x101d8b 3 13 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x101d8b 0x45 0xf5 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101d8e [0x41, 0x81, 0xE5, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101d8e) (andR32Imm32Effect 0x101d8e 7 13 0x3ffffff)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101d8e 7 13 0x3ffffff).toInstrSpec (and_r32_imm32_rex_effect_step 0x101d8e 0x41 0xe5 0x3ffffff (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101d95 [0x44, 0x21, 0xED] (fun s => s.RIP = 0x101d95) (andR32R32Effect 0x101d95 3 5 13)
      [.gpr 5, .gpr 13] [] [.reg 5, .flags, .rip] :=
    (andR32R32Effect_footprint 0x101d95 3 5 13).toInstrSpec (and_r32_r32_rex_effect_step 0x101d95 0x44 0xed (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101d98 [0x45, 0x21, 0xEB] (fun s => s.RIP = 0x101d98) (andR32R32Effect 0x101d98 3 11 13)
      [.gpr 11, .gpr 13] [] [.reg 11, .flags, .rip] :=
    (andR32R32Effect_footprint 0x101d98 3 11 13).toInstrSpec (and_r32_r32_rex_effect_step 0x101d98 0x45 0xeb (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101d9b [0x44, 0x21, 0xEB] (fun s => s.RIP = 0x101d9b) (andR32R32Effect 0x101d9b 3 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (andR32R32Effect_footprint 0x101d9b 3 3 13).toInstrSpec (and_r32_r32_rex_effect_step 0x101d9b 0x44 0xeb (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101d9e [0x45, 0x21, 0xFD] (fun s => s.RIP = 0x101d9e) (andR32R32Effect 0x101d9e 3 13 15)
      [.gpr 13, .gpr 15] [] [.reg 13, .flags, .rip] :=
    (andR32R32Effect_footprint 0x101d9e 3 13 15).toInstrSpec (and_r32_r32_rex_effect_step 0x101d9e 0x45 0xfd (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x101da1 [0x45, 0x21, 0xE6] (fun s => s.RIP = 0x101da1) (andR32R32Effect 0x101da1 3 14 12)
      [.gpr 14, .gpr 12] [] [.reg 14, .flags, .rip] :=
    (andR32R32Effect_footprint 0x101da1 3 14 12).toInstrSpec (and_r32_r32_rex_effect_step 0x101da1 0x45 0xe6 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x101da4 [0x41, 0x21, 0xFA] (fun s => s.RIP = 0x101da4) (andR32R32Effect 0x101da4 3 10 7)
      [.gpr 10, .gpr 7] [] [.reg 10, .flags, .rip] :=
    (andR32R32Effect_footprint 0x101da4 3 10 7).toInstrSpec (and_r32_r32_rex_effect_step 0x101da4 0x41 0xfa (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x101da7 [0x41, 0x09, 0xEA] (fun s => s.RIP = 0x101da7) (orR32R32Effect 0x101da7 3 10 5)
      [.gpr 10, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (orR32R32Effect_footprint 0x101da7 3 10 5).toInstrSpec (or_r32_r32_rex_effect_step 0x101da7 0x41 0xea (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x101daa [0x41, 0x21, 0xF9] (fun s => s.RIP = 0x101daa) (andR32R32Effect 0x101daa 3 9 7)
      [.gpr 9, .gpr 7] [] [.reg 9, .flags, .rip] :=
    (andR32R32Effect_footprint 0x101daa 3 9 7).toInstrSpec (and_r32_r32_rex_effect_step 0x101daa 0x41 0xf9 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x101dad [0x45, 0x09, 0xD9] (fun s => s.RIP = 0x101dad) (orR32R32Effect 0x101dad 3 9 11)
      [.gpr 9, .gpr 11] [] [.reg 9, .flags, .rip] :=
    (orR32R32Effect_footprint 0x101dad 3 9 11).toInstrSpec (or_r32_r32_rex_effect_step 0x101dad 0x45 0xd9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d6c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d70) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d74) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d7b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d7e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d81) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d84) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d88) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d8b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 71), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d8e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 73), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d95) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 75), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 73), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d98) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 75), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 77), (12, 61), (13, 73), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d9b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 79), (4, 4), (5, 75), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 77), (12, 61), (13, 73), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101d9e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 79), (4, 4), (5, 75), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 77), (12, 61), (13, 81), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101da1) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 79), (4, 4), (5, 75), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 77), (12, 61), (13, 81), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101da4) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 79), (4, 4), (5, 75), (6, 6), (7, 65), (8, 8), (9, 9), (10, 85), (11, 77), (12, 61), (13, 81), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101da7) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 79), (4, 4), (5, 75), (6, 6), (7, 65), (8, 8), (9, 9), (10, 87), (11, 77), (12, 61), (13, 81), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101daa) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 79), (4, 4), (5, 75), (6, 6), (7, 65), (8, 8), (9, 89), (10, 87), (11, 77), (12, 61), (13, 81), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dad) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 79), (4, 4), (5, 75), (6, 6), (7, 65), (8, 8), (9, 91), (10, 87), (11, 77), (12, 61), (13, 81), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101db0) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 93) (by decide) rfl

theorem block_l101d69 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101d69 :=
  Rest.liftedBlock (rest_l101d69 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101d69 x hx)

theorem rest_l101db0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101db0 bytes_l101db0) (entryMap (live .l101db0))
      20 0x101db0 bytes_l101db0 b_l101db0 := by
  have f0 : InstrSpec 0x101db0 [0x21, 0xF9] (fun s => s.RIP = 0x101db0) (andR32R32Effect 0x101db0 2 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (andR32R32Effect_footprint 0x101db0 2 1 7).toInstrSpec (and_r32_r32_effect_step 0x101db0 0xf9 (by decide)) pre_rip
  have f1 : InstrSpec 0x101db2 [0x09, 0xD9] (fun s => s.RIP = 0x101db2) (orR32R32Effect 0x101db2 2 1 3)
      [.gpr 1, .gpr 3] [] [.reg 1, .flags, .rip] :=
    (orR32R32Effect_footprint 0x101db2 2 1 3).toInstrSpec (or_r32_r32_effect_step 0x101db2 0xd9 (by decide)) pre_rip
  have f2 : InstrSpec 0x101db4 [0x21, 0xFA] (fun s => s.RIP = 0x101db4) (andR32R32Effect 0x101db4 2 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (andR32R32Effect_footprint 0x101db4 2 2 7).toInstrSpec (and_r32_r32_effect_step 0x101db4 0xfa (by decide)) pre_rip
  have f3 : InstrSpec 0x101db6 [0x44, 0x09, 0xEA] (fun s => s.RIP = 0x101db6) (orR32R32Effect 0x101db6 3 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (orR32R32Effect_footprint 0x101db6 3 2 13).toInstrSpec (or_r32_r32_rex_effect_step 0x101db6 0x44 0xea (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101db9 [0x44, 0x21, 0xC7] (fun s => s.RIP = 0x101db9) (andR32R32Effect 0x101db9 3 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (andR32R32Effect_footprint 0x101db9 3 7 8).toInstrSpec (and_r32_r32_rex_effect_step 0x101db9 0x44 0xc7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101dbc [0x44, 0x09, 0xF7] (fun s => s.RIP = 0x101dbc) (orR32R32Effect 0x101dbc 3 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (orR32R32Effect_footprint 0x101dbc 3 7 14).toInstrSpec (or_r32_r32_rex_effect_step 0x101dbc 0x44 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101dbf [0x45, 0x89, 0xC8] (fun s => s.RIP = 0x101dbf) (movR32R32Effect 0x101dbf 3 8 9)
      [.gpr 9] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x101dbf 3 8 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x101dbf 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101dc2 [0x41, 0xC1, 0xE0, 0x1A] (fun s => s.RIP = 0x101dc2) (shlR32Effect 0x101dc2 4 8 26)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR32Effect_footprint 0x101dc2 4 8 26).toInstrSpec (shl_r32_imm8_rex_effect_step 0x101dc2 0x41 0xe0 0x1a (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101dc6 [0x45, 0x09, 0xD0] (fun s => s.RIP = 0x101dc6) (orR32R32Effect 0x101dc6 3 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (orR32R32Effect_footprint 0x101dc6 3 8 10).toInstrSpec (or_r32_r32_rex_effect_step 0x101dc6 0x45 0xd0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101dc9 [0x41, 0xC1, 0xE9, 0x06] (fun s => s.RIP = 0x101dc9) (shrR32Effect 0x101dc9 4 9 6)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x101dc9 4 9 6).toInstrSpec (shr_r32_imm8_rex_effect_step 0x101dc9 0x41 0xe9 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101dcd [0x41, 0x89, 0xCA] (fun s => s.RIP = 0x101dcd) (movR32R32Effect 0x101dcd 3 10 1)
      [.gpr 1] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x101dcd 3 10 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x101dcd 0x41 0xca (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101dd0 [0x41, 0xC1, 0xE2, 0x14] (fun s => s.RIP = 0x101dd0) (shlR32Effect 0x101dd0 4 10 20)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR32Effect_footprint 0x101dd0 4 10 20).toInstrSpec (shl_r32_imm8_rex_effect_step 0x101dd0 0x41 0xe2 0x14 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101dd4 [0x45, 0x09, 0xCA] (fun s => s.RIP = 0x101dd4) (orR32R32Effect 0x101dd4 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (orR32R32Effect_footprint 0x101dd4 3 10 9).toInstrSpec (or_r32_r32_rex_effect_step 0x101dd4 0x45 0xca (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101dd7 [0xC1, 0xE9, 0x0C] (fun s => s.RIP = 0x101dd7) (shrR32Effect 0x101dd7 3 1 12)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x101dd7 3 1 12).toInstrSpec (shr_r32_imm8_effect_step 0x101dd7 0xe9 0xc (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101dda [0x41, 0x89, 0xD1] (fun s => s.RIP = 0x101dda) (movR32R32Effect 0x101dda 3 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x101dda 3 9 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x101dda 0x41 0xd1 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x101ddd [0x41, 0xC1, 0xE1, 0x0E] (fun s => s.RIP = 0x101ddd) (shlR32Effect 0x101ddd 4 9 14)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR32Effect_footprint 0x101ddd 4 9 14).toInstrSpec (shl_r32_imm8_rex_effect_step 0x101ddd 0x41 0xe1 0xe (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x101de1 [0x41, 0x09, 0xC9] (fun s => s.RIP = 0x101de1) (orR32R32Effect 0x101de1 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (orR32R32Effect_footprint 0x101de1 3 9 1).toInstrSpec (or_r32_r32_rex_effect_step 0x101de1 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x101de4 [0xC1, 0xEA, 0x12] (fun s => s.RIP = 0x101de4) (shrR32Effect 0x101de4 3 2 18)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x101de4 3 2 18).toInstrSpec (shr_r32_imm8_effect_step 0x101de4 0xea 0x12 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x101de7 [0xC1, 0xE7, 0x08] (fun s => s.RIP = 0x101de7) (shlR32Effect 0x101de7 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x101de7 3 7 8).toInstrSpec (shl_r32_imm8_effect_step 0x101de7 0xe7 0x8 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x101dea [0x09, 0xD7] (fun s => s.RIP = 0x101dea) (orR32R32Effect 0x101dea 2 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (orR32R32Effect_footprint 0x101dea 2 7 2).toInstrSpec (or_r32_r32_effect_step 0x101dea 0xd7 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101db2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101db4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101db6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101db9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dbc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dbf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (6, 6), (7, 63), (8, 65), (9, 9), (10, 10), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dc2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (6, 6), (7, 63), (8, 67), (9, 9), (10, 10), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dc6) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (6, 6), (7, 63), (8, 69), (9, 9), (10, 10), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dc9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (6, 6), (7, 63), (8, 69), (9, 71), (10, 10), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dcd) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (6, 6), (7, 63), (8, 69), (9, 71), (10, 73), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dd0) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (6, 6), (7, 63), (8, 69), (9, 71), (10, 75), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dd4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (6, 6), (7, 63), (8, 69), (9, 71), (10, 77), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dd7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 79), (2, 59), (3, 3), (4, 4), (6, 6), (7, 63), (8, 69), (9, 71), (10, 77), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dda) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 79), (2, 59), (3, 3), (4, 4), (6, 6), (7, 63), (8, 69), (9, 81), (10, 77), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ddd) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 79), (2, 59), (3, 3), (4, 4), (6, 6), (7, 63), (8, 69), (9, 83), (10, 77), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101de1) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 79), (2, 59), (3, 3), (4, 4), (6, 6), (7, 63), (8, 69), (9, 85), (10, 77), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101de4) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 79), (2, 87), (3, 3), (4, 4), (6, 6), (7, 63), (8, 69), (9, 85), (10, 77), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101de7) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 79), (2, 87), (3, 3), (4, 4), (6, 6), (7, 89), (8, 69), (9, 85), (10, 77), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dea) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 79), (2, 87), (3, 3), (4, 4), (6, 6), (7, 91), (8, 69), (9, 85), (10, 77), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dec) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 93) (by decide) rfl

theorem block_l101db0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101db0 :=
  Rest.liftedBlock (rest_l101db0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101db0 x hx)

theorem rest_l101dec [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101dec bytes_l101dec) (entryMap (live .l101dec))
      20 0x101dec bytes_l101dec b_l101dec := by
  have f0 : InstrSpec 0x101dec [0x44, 0x03, 0x06] (LoadPre 0x101dec (fun s => AddrMode.addr (.base 6 .none) s (0x101dec + BitVec.ofNat 64 3)) 4) (addR32M32Effect 0x101dec 3 8 (.base 6 .none))
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101dec 3 8 (.base 6 .none)).toInstrSpec (add_r32_m32_rex_effect_step 0x101dec 0x44 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101def [0x8B, 0x4E, 0x04] (LoadPre 0x101def (fun s => AddrMode.addr (.base 6 (.d8 0x4)) s (0x101def + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101def 1 (.base 6 (.d8 0x4)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x101def 1 (.base 6 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x101def 1 (.base 6 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101df2 [0x8B, 0x56, 0x08] (LoadPre 0x101df2 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x101df2 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101df2 2 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x101df2 2 (.base 6 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x101df2 2 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x101df5 [0x4C, 0x11, 0xD1] (fun s => s.RIP = 0x101df5) (atFlags StatusFlags.CF (adcR64R64Effect 0x101df5 1 10))
      [.gpr 1, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x101df5 1 10).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x101df5 0x4c 0xd1 c (by decide) (by decide))) pre_rip
  have f4 : InstrSpec 0x101df8 [0x41, 0x89, 0xCA] (fun s => s.RIP = 0x101df8) (movR32R32Effect 0x101df8 3 10 1)
      [.gpr 1] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x101df8 3 10 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x101df8 0x41 0xca (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101dfb [0x4C, 0x01, 0xCA] (fun s => s.RIP = 0x101dfb) (addR64R64Effect 0x101dfb 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101dfb 2 9).toInstrSpec (add_r64_r64_effect_step 0x101dfb 0x4c 0xca (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101dfe [0x48, 0xC1, 0xE9, 0x20] (fun s => s.RIP = 0x101dfe) (shrR64Effect 0x101dfe 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x101dfe 4 1 32).toInstrSpec (shr_r64_imm8_effect_step 0x101dfe 0x48 0xe9 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101e02 [0x48, 0x01, 0xD1] (fun s => s.RIP = 0x101e02) (addR64R64Effect 0x101e02 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101e02 1 2).toInstrSpec (add_r64_r64_effect_step 0x101e02 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101e05 [0x03, 0x7E, 0x0C] (LoadPre 0x101e05 (fun s => AddrMode.addr (.base 6 (.d8 0xc)) s (0x101e05 + BitVec.ofNat 64 3)) 4) (addR32M32Effect 0x101e05 3 7 (.base 6 (.d8 0xc)))
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101e05 3 7 (.base 6 (.d8 0xc))).toInstrSpec (add_r32_m32_effect_step 0x101e05 7 (.base 6 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x101e08 [0x89, 0xCA] (fun s => s.RIP = 0x101e08) (movR32R32Effect 0x101e08 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x101e08 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x101e08 0xca (by decide)) pre_rip
  have f10 : InstrSpec 0x101e0a [0x48, 0xC1, 0xE9, 0x20] (fun s => s.RIP = 0x101e0a) (shrR64Effect 0x101e0a 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x101e0a 4 1 32).toInstrSpec (shr_r64_imm8_effect_step 0x101e0a 0x48 0xe9 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101e0e [0x01, 0xF9] (fun s => s.RIP = 0x101e0e) (addR32R32Effect 0x101e0e 2 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101e0e 2 1 7).toInstrSpec (add_r32_r32_effect_step 0x101e0e 0xf9 (by decide)) pre_rip
  have f12 : InstrSpec 0x101e10 [0x44, 0x89, 0x00] (StorePre 0x101e10 3 (fun s => AddrMode.addr (.base 0 .none) s (0x101e10 + BitVec.ofNat 64 3)) 4) (movM32R32Effect 0x101e10 8 (.base 0 .none))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM32R32Effect_footprint 0x101e10 8 (.base 0 .none)).toInstrSpec (mov_m32_r32_effect_step 0x101e10 0x44 (by decide) 0 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x101e13 [0x44, 0x89, 0x50, 0x04] (StorePre 0x101e13 4 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x101e13 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101e13 10 (.base 0 (.d8 0x4)))
      [.gpr 10, .gpr 0] [] [.rip] :=
    (movM32R32Effect_footprint 0x101e13 10 (.base 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_effect_step 0x101e13 0x44 (by decide) 2 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x101e17 [0x89, 0x50, 0x08] (StorePre 0x101e17 3 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x101e17 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101e17 2 (.base 0 (.d8 0x8)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101e17 2 (.base 0 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x101e17 2 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x101e1a [0x89, 0x48, 0x0C] (StorePre 0x101e1a 3 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x101e1a + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101e1a 1 (.base 0 (.d8 0xc)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101e1a 1 (.base 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x101e1a 1 (.base 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x101e1d [0x5B] (PopPre 0x101e1d) (popR64Effect 0x101e1d 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101e1d 1 3).toInstrSpec (pop_r64_effect_step 0x101e1d 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f17 : InstrSpec 0x101e1e [0x41, 0x5C] (PopPre 0x101e1e) (popR64Effect 0x101e1e 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101e1e 2 12).toInstrSpec (pop_r64_rex_effect_step 0x101e1e 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f18 : InstrSpec 0x101e20 [0x41, 0x5D] (PopPre 0x101e20) (popR64Effect 0x101e20 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101e20 2 13).toInstrSpec (pop_r64_rex_effect_step 0x101e20 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f19 : InstrSpec 0x101e22 [0x41, 0x5E] (PopPre 0x101e22) (popR64Effect 0x101e22 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101e22 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101e22 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (16, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101def) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (16, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101df2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 56), (2, 58), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (16, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101df5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 60), (2, 58), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101df8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 60), (2, 58), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dfb) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 60), (2, 64), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dfe) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 66), (2, 64), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e02) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 68), (2, 64), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e05) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 68), (2, 64), (4, 4), (6, 6), (7, 70), (8, 53), (9, 9), (10, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e08) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 68), (2, 72), (4, 4), (6, 6), (7, 70), (8, 53), (9, 9), (10, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e0a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 74), (2, 72), (4, 4), (6, 6), (7, 70), (8, 53), (9, 9), (10, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e0e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 76), (2, 72), (4, 4), (6, 6), (7, 70), (8, 53), (9, 9), (10, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e10) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 76), (2, 72), (4, 4), (6, 6), (7, 70), (8, 53), (9, 9), (10, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e13) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 76), (2, 72), (4, 4), (6, 6), (7, 70), (8, 53), (9, 9), (10, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e17) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 76), (2, 72), (4, 4), (6, 6), (7, 70), (8, 53), (9, 9), (10, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e1a) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 76), (2, 72), (4, 4), (6, 6), (7, 70), (8, 53), (9, 9), (10, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e1d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 76), (2, 72), (3, 82), (4, 83), (6, 6), (7, 70), (8, 53), (9, 9), (10, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e1e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f17 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 76), (2, 72), (3, 82), (4, 86), (6, 6), (7, 70), (8, 53), (9, 9), (10, 62), (12, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e20) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 89) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 76), (2, 72), (3, 82), (4, 89), (6, 6), (7, 70), (8, 53), (9, 9), (10, 62), (12, 85), (13, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e22) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 92) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 93) (ρ' := [(0, 0), (1, 76), (2, 72), (3, 82), (4, 92), (6, 6), (7, 70), (8, 53), (9, 9), (10, 62), (12, 85), (13, 88), (14, 91), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e24) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 94) (by decide) rfl

theorem block_l101dec [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101dec :=
  Rest.liftedBlock (rest_l101dec code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101dec x hx)

theorem rest_l101e24 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e24 bytes_l101e24) (entryMap (live .l101e24))
      3 0x101e24 bytes_l101e24 b_l101e24 := by
  have f0 : InstrSpec 0x101e24 [0x41, 0x5F] (PopPre 0x101e24) (popR64Effect 0x101e24 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101e24 2 15).toInstrSpec (pop_r64_rex_effect_step 0x101e24 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x101e26 [0x5D] (PopPre 0x101e26) (popR64Effect 0x101e26 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101e26 1 5).toInstrSpec (pop_r64_effect_step 0x101e26 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101e27 [0xC3] (RetPre 0x101e27) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101e27).toInstrSpec (ret_effect_step 0x101e27) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e26) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 56), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e27) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f2 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 60), (5, 56), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) f2 (by decide) rfl rfl rfl (by decide)

theorem block_l101e24 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e24 :=
  Rest.liftedBlock (rest_l101e24 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e24 x hx)

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

theorem_by block_l101ce0_eval :
    program.runBlock (dialect code) ⟨.l101ce0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101d20_eval :
    program.runBlock (dialect code) ⟨.l101d20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101d69_eval :
    program.runBlock (dialect code) ⟨.l101d69, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101db0_eval :
    program.runBlock (dialect code) ⟨.l101db0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101dec_eval :
    program.runBlock (dialect code) ⟨.l101dec, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e24_eval :
    program.runBlock (dialect code) ⟨.l101e24, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
