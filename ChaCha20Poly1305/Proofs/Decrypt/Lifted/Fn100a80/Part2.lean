import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Program
import X86Proofs.Instructions.Branch.Triple
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Values

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

theorem rest_l100d02 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100d02 bytes_l100d02) (entryMap (live .l100d02))
      13 0x100d02 bytes_l100d02 b_l100d02 := by
  have f0 : InstrSpec 0x100d02 [0x41, 0x01, 0xCD] (fun s => s.RIP = 0x100d02) (addR32R32Effect 0x100d02 3 13 1)
      [.gpr 13, .gpr 1] [] [.reg 13, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d02 3 13 1).toInstrSpec (add_r32_r32_rex_effect_step 0x100d02 0x41 0xcd (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100d05 [0x44, 0x31, 0xEF] (fun s => s.RIP = 0x100d05) (xorR32R32Effect 0x100d05 3 7 13)
      [.gpr 7, .gpr 13] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d05 3 7 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d05 0x44 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100d08 [0xC1, 0xC7, 0x10] (fun s => s.RIP = 0x100d08) (rolR32Effect 0x100d08 3 7 16)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d08 3 7 16).toInstrSpec (rol_r32_imm8_effect_step 0x100d08 0xc7 0x10 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100d0b [0x01, 0xF8] (fun s => s.RIP = 0x100d0b) (addR32R32Effect 0x100d0b 2 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d0b 2 0 7).toInstrSpec (add_r32_r32_effect_step 0x100d0b 0xf8 (by decide)) pre_rip
  have f4 : InstrSpec 0x100d0d [0x31, 0xC1] (fun s => s.RIP = 0x100d0d) (xorR32R32Effect 0x100d0d 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d0d 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x100d0d 0xc1 (by decide)) pre_rip
  have f5 : InstrSpec 0x100d0f [0xC1, 0xC1, 0x0C] (fun s => s.RIP = 0x100d0f) (rolR32Effect 0x100d0f 3 1 12)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d0f 3 1 12).toInstrSpec (rol_r32_imm8_effect_step 0x100d0f 0xc1 0xc (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100d12 [0x41, 0x01, 0xCD] (fun s => s.RIP = 0x100d12) (addR32R32Effect 0x100d12 3 13 1)
      [.gpr 13, .gpr 1] [] [.reg 13, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d12 3 13 1).toInstrSpec (add_r32_r32_rex_effect_step 0x100d12 0x41 0xcd (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100d15 [0x44, 0x31, 0xEF] (fun s => s.RIP = 0x100d15) (xorR32R32Effect 0x100d15 3 7 13)
      [.gpr 7, .gpr 13] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d15 3 7 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d15 0x44 0xef (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100d18 [0xC1, 0xC7, 0x08] (fun s => s.RIP = 0x100d18) (rolR32Effect 0x100d18 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d18 3 7 8).toInstrSpec (rol_r32_imm8_effect_step 0x100d18 0xc7 0x8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100d1b [0x01, 0xF8] (fun s => s.RIP = 0x100d1b) (addR32R32Effect 0x100d1b 2 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d1b 2 0 7).toInstrSpec (add_r32_r32_effect_step 0x100d1b 0xf8 (by decide)) pre_rip
  have f10 : InstrSpec 0x100d1d [0x89, 0x44, 0x24, 0x08] (StorePre 0x100d1d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100d1d + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100d1d 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100d1d 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x100d1d 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x100d21 [0x31, 0xC1] (fun s => s.RIP = 0x100d21) (xorR32R32Effect 0x100d21 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d21 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x100d21 0xc1 (by decide)) pre_rip
  have f12 : InstrSpec 0x100d23 [0xC1, 0xC1, 0x07] (fun s => s.RIP = 0x100d23) (rolR32Effect 0x100d23 3 1 7)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d23 3 1 7).toInstrSpec (rol_r32_imm8_effect_step 0x100d23 0xc1 0x7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d05) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d08) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d0b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d0d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d0f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 63), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d12) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 63), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d15) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 63), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d18) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 63), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d1b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 63), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d1d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (1, 63), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d21) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 74), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d23) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 71), (1, 76), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d26) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 78) (by decide) rfl

theorem block_l100d02 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100d02 :=
  Rest.liftedBlock (rest_l100d02 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100d02 x hx)

theorem rest_l100d26 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100d26 bytes_l100d26) (entryMap (live .l100d26))
      12 0x100d26 bytes_l100d26 b_l100d26 := by
  have f0 : InstrSpec 0x100d26 [0x41, 0x01, 0xD4] (fun s => s.RIP = 0x100d26) (addR32R32Effect 0x100d26 3 12 2)
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d26 3 12 2).toInstrSpec (add_r32_r32_rex_effect_step 0x100d26 0x41 0xd4 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100d29 [0x45, 0x31, 0xE6] (fun s => s.RIP = 0x100d29) (xorR32R32Effect 0x100d29 3 14 12)
      [.gpr 14, .gpr 12] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d29 3 14 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d29 0x45 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100d2c [0x41, 0xC1, 0xC6, 0x10] (fun s => s.RIP = 0x100d2c) (rolR32Effect 0x100d2c 4 14 16)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d2c 4 14 16).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100d2c 0x41 0xc6 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100d30 [0x44, 0x01, 0xF6] (fun s => s.RIP = 0x100d30) (addR32R32Effect 0x100d30 3 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d30 3 6 14).toInstrSpec (add_r32_r32_rex_effect_step 0x100d30 0x44 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100d33 [0x31, 0xF2] (fun s => s.RIP = 0x100d33) (xorR32R32Effect 0x100d33 2 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d33 2 2 6).toInstrSpec (xor_r32_r32_effect_step 0x100d33 0xf2 (by decide)) pre_rip
  have f5 : InstrSpec 0x100d35 [0xC1, 0xC2, 0x0C] (fun s => s.RIP = 0x100d35) (rolR32Effect 0x100d35 3 2 12)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d35 3 2 12).toInstrSpec (rol_r32_imm8_effect_step 0x100d35 0xc2 0xc (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100d38 [0x41, 0x01, 0xD4] (fun s => s.RIP = 0x100d38) (addR32R32Effect 0x100d38 3 12 2)
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d38 3 12 2).toInstrSpec (add_r32_r32_rex_effect_step 0x100d38 0x41 0xd4 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100d3b [0x45, 0x31, 0xE6] (fun s => s.RIP = 0x100d3b) (xorR32R32Effect 0x100d3b 3 14 12)
      [.gpr 14, .gpr 12] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d3b 3 14 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d3b 0x45 0xe6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100d3e [0x41, 0xC1, 0xC6, 0x08] (fun s => s.RIP = 0x100d3e) (rolR32Effect 0x100d3e 4 14 8)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d3e 4 14 8).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100d3e 0x41 0xc6 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100d42 [0x44, 0x01, 0xF6] (fun s => s.RIP = 0x100d42) (addR32R32Effect 0x100d42 3 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d42 3 6 14).toInstrSpec (add_r32_r32_rex_effect_step 0x100d42 0x44 0xf6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x100d45 [0x31, 0xF2] (fun s => s.RIP = 0x100d45) (xorR32R32Effect 0x100d45 2 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d45 2 2 6).toInstrSpec (xor_r32_r32_effect_step 0x100d45 0xf2 (by decide)) pre_rip
  have f11 : InstrSpec 0x100d47 [0xC1, 0xC2, 0x07] (fun s => s.RIP = 0x100d47) (rolR32Effect 0x100d47 3 2 7)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d47 3 2 7).toInstrSpec (rol_r32_imm8_effect_step 0x100d47 0xc2 0x7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d29) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d2c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d30) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d33) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d35) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d38) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d3b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d3e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d42) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d45) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 73), (3, 3), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d47) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 75), (3, 3), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d4a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l100d26 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100d26 :=
  Rest.liftedBlock (rest_l100d26 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100d26 x hx)

theorem rest_l100d4a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100d4a bytes_l100d4a) (entryMap (live .l100d4a))
      12 0x100d4a bytes_l100d4a b_l100d4a := by
  have f0 : InstrSpec 0x100d4a [0x45, 0x01, 0xDA] (fun s => s.RIP = 0x100d4a) (addR32R32Effect 0x100d4a 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d4a 3 10 11).toInstrSpec (add_r32_r32_rex_effect_step 0x100d4a 0x45 0xda (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100d4d [0x45, 0x31, 0xD7] (fun s => s.RIP = 0x100d4d) (xorR32R32Effect 0x100d4d 3 15 10)
      [.gpr 15, .gpr 10] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d4d 3 15 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d4d 0x45 0xd7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100d50 [0x41, 0xC1, 0xC7, 0x10] (fun s => s.RIP = 0x100d50) (rolR32Effect 0x100d50 4 15 16)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d50 4 15 16).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100d50 0x41 0xc7 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100d54 [0x45, 0x01, 0xF8] (fun s => s.RIP = 0x100d54) (addR32R32Effect 0x100d54 3 8 15)
      [.gpr 8, .gpr 15] [] [.reg 8, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d54 3 8 15).toInstrSpec (add_r32_r32_rex_effect_step 0x100d54 0x45 0xf8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100d57 [0x45, 0x31, 0xC3] (fun s => s.RIP = 0x100d57) (xorR32R32Effect 0x100d57 3 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d57 3 11 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d57 0x45 0xc3 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x100d5a [0x41, 0xC1, 0xC3, 0x0C] (fun s => s.RIP = 0x100d5a) (rolR32Effect 0x100d5a 4 11 12)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d5a 4 11 12).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100d5a 0x41 0xc3 0xc (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100d5e [0x45, 0x01, 0xDA] (fun s => s.RIP = 0x100d5e) (addR32R32Effect 0x100d5e 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d5e 3 10 11).toInstrSpec (add_r32_r32_rex_effect_step 0x100d5e 0x45 0xda (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100d61 [0x45, 0x31, 0xD7] (fun s => s.RIP = 0x100d61) (xorR32R32Effect 0x100d61 3 15 10)
      [.gpr 15, .gpr 10] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d61 3 15 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d61 0x45 0xd7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100d64 [0x41, 0xC1, 0xC7, 0x08] (fun s => s.RIP = 0x100d64) (rolR32Effect 0x100d64 4 15 8)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d64 4 15 8).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100d64 0x41 0xc7 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100d68 [0x45, 0x01, 0xF8] (fun s => s.RIP = 0x100d68) (addR32R32Effect 0x100d68 3 8 15)
      [.gpr 8, .gpr 15] [] [.reg 8, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d68 3 8 15).toInstrSpec (add_r32_r32_rex_effect_step 0x100d68 0x45 0xf8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x100d6b [0x45, 0x31, 0xC3] (fun s => s.RIP = 0x100d6b) (xorR32R32Effect 0x100d6b 3 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d6b 3 11 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d6b 0x45 0xc3 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x100d6e [0x41, 0xC1, 0xC3, 0x07] (fun s => s.RIP = 0x100d6e) (rolR32Effect 0x100d6e 4 11 7)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d6e 4 11 7).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100d6e 0x41 0xc3 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d4d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d50) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d54) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d57) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 53), (11, 61), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d5a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 53), (11, 63), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d5e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 65), (11, 63), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d61) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 65), (11, 63), (12, 12), (13, 13), (14, 14), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d64) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 65), (11, 63), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d68) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 9), (10, 65), (11, 63), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d6b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 9), (10, 65), (11, 73), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d6e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 9), (10, 65), (11, 75), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d72) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l100d4a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100d4a :=
  Rest.liftedBlock (rest_l100d4a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100d4a x hx)

theorem rest_l100d72 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100d72 bytes_l100d72) (entryMap (live .l100d72))
      12 0x100d72 bytes_l100d72 b_l100d72 := by
  have f0 : InstrSpec 0x100d72 [0x01, 0xCB] (fun s => s.RIP = 0x100d72) (addR32R32Effect 0x100d72 2 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d72 2 3 1).toInstrSpec (add_r32_r32_effect_step 0x100d72 0xcb (by decide)) pre_rip
  have f1 : InstrSpec 0x100d74 [0x41, 0x31, 0xDF] (fun s => s.RIP = 0x100d74) (xorR32R32Effect 0x100d74 3 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d74 3 15 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d74 0x41 0xdf (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100d77 [0x41, 0xC1, 0xC7, 0x10] (fun s => s.RIP = 0x100d77) (rolR32Effect 0x100d77 4 15 16)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d77 4 15 16).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100d77 0x41 0xc7 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100d7b [0x44, 0x01, 0xFE] (fun s => s.RIP = 0x100d7b) (addR32R32Effect 0x100d7b 3 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d7b 3 6 15).toInstrSpec (add_r32_r32_rex_effect_step 0x100d7b 0x44 0xfe (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100d7e [0x31, 0xF1] (fun s => s.RIP = 0x100d7e) (xorR32R32Effect 0x100d7e 2 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d7e 2 1 6).toInstrSpec (xor_r32_r32_effect_step 0x100d7e 0xf1 (by decide)) pre_rip
  have f5 : InstrSpec 0x100d80 [0xC1, 0xC1, 0x0C] (fun s => s.RIP = 0x100d80) (rolR32Effect 0x100d80 3 1 12)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d80 3 1 12).toInstrSpec (rol_r32_imm8_effect_step 0x100d80 0xc1 0xc (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100d83 [0x01, 0xCB] (fun s => s.RIP = 0x100d83) (addR32R32Effect 0x100d83 2 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d83 2 3 1).toInstrSpec (add_r32_r32_effect_step 0x100d83 0xcb (by decide)) pre_rip
  have f7 : InstrSpec 0x100d85 [0x41, 0x31, 0xDF] (fun s => s.RIP = 0x100d85) (xorR32R32Effect 0x100d85 3 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d85 3 15 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d85 0x41 0xdf (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100d88 [0x41, 0xC1, 0xC7, 0x08] (fun s => s.RIP = 0x100d88) (rolR32Effect 0x100d88 4 15 8)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d88 4 15 8).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100d88 0x41 0xc7 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100d8c [0x44, 0x01, 0xFE] (fun s => s.RIP = 0x100d8c) (addR32R32Effect 0x100d8c 3 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d8c 3 6 15).toInstrSpec (add_r32_r32_rex_effect_step 0x100d8c 0x44 0xfe (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x100d8f [0x31, 0xF1] (fun s => s.RIP = 0x100d8f) (xorR32R32Effect 0x100d8f 2 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d8f 2 1 6).toInstrSpec (xor_r32_r32_effect_step 0x100d8f 0xf1 (by decide)) pre_rip
  have f11 : InstrSpec 0x100d91 [0xC1, 0xC1, 0x07] (fun s => s.RIP = 0x100d91) (rolR32Effect 0x100d91 3 1 7)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d91 3 1 7).toInstrSpec (rol_r32_imm8_effect_step 0x100d91 0xc1 0x7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d74) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d77) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d7b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d7e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 61), (2, 2), (3, 53), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d80) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 63), (2, 2), (3, 53), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d83) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 63), (2, 2), (3, 65), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d85) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 63), (2, 2), (3, 65), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d88) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 63), (2, 2), (3, 65), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d8c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 63), (2, 2), (3, 65), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d8f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 73), (2, 2), (3, 65), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d91) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 75), (2, 2), (3, 65), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d94) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l100d72 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100d72 :=
  Rest.liftedBlock (rest_l100d72 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100d72 x hx)

theorem rest_l100d94 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100d94 bytes_l100d94) (entryMap (live .l100d94))
      12 0x100d94 bytes_l100d94 b_l100d94 := by
  have f0 : InstrSpec 0x100d94 [0x41, 0x01, 0xD5] (fun s => s.RIP = 0x100d94) (addR32R32Effect 0x100d94 3 13 2)
      [.gpr 13, .gpr 2] [] [.reg 13, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d94 3 13 2).toInstrSpec (add_r32_r32_rex_effect_step 0x100d94 0x41 0xd5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100d97 [0x45, 0x31, 0xE9] (fun s => s.RIP = 0x100d97) (xorR32R32Effect 0x100d97 3 9 13)
      [.gpr 9, .gpr 13] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d97 3 9 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d97 0x45 0xe9 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100d9a [0x41, 0xC1, 0xC1, 0x10] (fun s => s.RIP = 0x100d9a) (rolR32Effect 0x100d9a 4 9 16)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (rolR32Effect_footprint 0x100d9a 4 9 16).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100d9a 0x41 0xc1 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100d9e [0x45, 0x01, 0xC8] (fun s => s.RIP = 0x100d9e) (addR32R32Effect 0x100d9e 3 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100d9e 3 8 9).toInstrSpec (add_r32_r32_rex_effect_step 0x100d9e 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100da1 [0x44, 0x31, 0xC2] (fun s => s.RIP = 0x100da1) (xorR32R32Effect 0x100da1 3 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100da1 3 2 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x100da1 0x44 0xc2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x100da4 [0xC1, 0xC2, 0x0C] (fun s => s.RIP = 0x100da4) (rolR32Effect 0x100da4 3 2 12)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR32Effect_footprint 0x100da4 3 2 12).toInstrSpec (rol_r32_imm8_effect_step 0x100da4 0xc2 0xc (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100da7 [0x41, 0x01, 0xD5] (fun s => s.RIP = 0x100da7) (addR32R32Effect 0x100da7 3 13 2)
      [.gpr 13, .gpr 2] [] [.reg 13, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100da7 3 13 2).toInstrSpec (add_r32_r32_rex_effect_step 0x100da7 0x41 0xd5 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100daa [0x45, 0x31, 0xE9] (fun s => s.RIP = 0x100daa) (xorR32R32Effect 0x100daa 3 9 13)
      [.gpr 9, .gpr 13] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100daa 3 9 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x100daa 0x45 0xe9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100dad [0x41, 0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x100dad) (rolR32Effect 0x100dad 4 9 8)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (rolR32Effect_footprint 0x100dad 4 9 8).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100dad 0x41 0xc1 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100db1 [0x45, 0x01, 0xC8] (fun s => s.RIP = 0x100db1) (addR32R32Effect 0x100db1 3 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100db1 3 8 9).toInstrSpec (add_r32_r32_rex_effect_step 0x100db1 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x100db4 [0x44, 0x31, 0xC2] (fun s => s.RIP = 0x100db4) (xorR32R32Effect 0x100db4 3 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100db4 3 2 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x100db4 0x44 0xc2 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x100db7 [0xC1, 0xC2, 0x07] (fun s => s.RIP = 0x100db7) (rolR32Effect 0x100db7 3 2 7)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR32Effect_footprint 0x100db7 3 2 7).toInstrSpec (rol_r32_imm8_effect_step 0x100db7 0xc2 0x7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d97) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d9a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 57), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d9e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 57), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100da1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 57), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100da4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 57), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100da7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 57), (10, 10), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100daa) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 67), (10, 10), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dad) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 69), (10, 10), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100db1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 69), (10, 10), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100db4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 73), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 69), (10, 10), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100db7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 75), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 69), (10, 10), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dba) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l100d94 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100d94 :=
  Rest.liftedBlock (rest_l100d94 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100d94 x hx)

theorem rest_l100dba [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100dba bytes_l100dba) (entryMap (live .l100dba))
      15 0x100dba bytes_l100dba b_l100dba := by
  have f0 : InstrSpec 0x100dba [0x45, 0x01, 0xDC] (fun s => s.RIP = 0x100dba) (addR32R32Effect 0x100dba 3 12 11)
      [.gpr 12, .gpr 11] [] [.reg 12, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100dba 3 12 11).toInstrSpec (add_r32_r32_rex_effect_step 0x100dba 0x45 0xdc (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100dbd [0x44, 0x31, 0xE7] (fun s => s.RIP = 0x100dbd) (xorR32R32Effect 0x100dbd 3 7 12)
      [.gpr 7, .gpr 12] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100dbd 3 7 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x100dbd 0x44 0xe7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100dc0 [0xC1, 0xC7, 0x10] (fun s => s.RIP = 0x100dc0) (rolR32Effect 0x100dc0 3 7 16)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (rolR32Effect_footprint 0x100dc0 3 7 16).toInstrSpec (rol_r32_imm8_effect_step 0x100dc0 0xc7 0x10 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100dc3 [0x8B, 0x44, 0x24, 0x04] (LoadPre 0x100dc3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100dc3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100dc3 0 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100dc3 0 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x100dc3 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x100dc7 [0x01, 0xF8] (fun s => s.RIP = 0x100dc7) (addR32R32Effect 0x100dc7 2 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100dc7 2 0 7).toInstrSpec (add_r32_r32_effect_step 0x100dc7 0xf8 (by decide)) pre_rip
  have f5 : InstrSpec 0x100dc9 [0x41, 0x31, 0xC3] (fun s => s.RIP = 0x100dc9) (xorR32R32Effect 0x100dc9 3 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100dc9 3 11 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x100dc9 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100dcc [0x41, 0xC1, 0xC3, 0x0C] (fun s => s.RIP = 0x100dcc) (rolR32Effect 0x100dcc 4 11 12)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR32Effect_footprint 0x100dcc 4 11 12).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100dcc 0x41 0xc3 0xc (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100dd0 [0x45, 0x01, 0xDC] (fun s => s.RIP = 0x100dd0) (addR32R32Effect 0x100dd0 3 12 11)
      [.gpr 12, .gpr 11] [] [.reg 12, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100dd0 3 12 11).toInstrSpec (add_r32_r32_rex_effect_step 0x100dd0 0x45 0xdc (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100dd3 [0x44, 0x31, 0xE7] (fun s => s.RIP = 0x100dd3) (xorR32R32Effect 0x100dd3 3 7 12)
      [.gpr 7, .gpr 12] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100dd3 3 7 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x100dd3 0x44 0xe7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100dd6 [0xC1, 0xC7, 0x08] (fun s => s.RIP = 0x100dd6) (rolR32Effect 0x100dd6 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (rolR32Effect_footprint 0x100dd6 3 7 8).toInstrSpec (rol_r32_imm8_effect_step 0x100dd6 0xc7 0x8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x100dd9 [0x01, 0xF8] (fun s => s.RIP = 0x100dd9) (addR32R32Effect 0x100dd9 2 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100dd9 2 0 7).toInstrSpec (add_r32_r32_effect_step 0x100dd9 0xf8 (by decide)) pre_rip
  have f11 : InstrSpec 0x100ddb [0x89, 0x44, 0x24, 0x04] (StorePre 0x100ddb 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100ddb + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100ddb 0 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100ddb 0 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x100ddb 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x100ddf [0x41, 0x31, 0xC3] (fun s => s.RIP = 0x100ddf) (xorR32R32Effect 0x100ddf 3 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100ddf 3 11 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x100ddf 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x100de2 [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x100de2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100de2 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100de2 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100de2 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x100de2 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x100de6 [0x41, 0xC1, 0xC3, 0x07] (fun s => s.RIP = 0x100de6) (rolR32Effect 0x100de6 4 11 7)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR32Effect_footprint 0x100de6 4 11 7).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100de6 0x41 0xc3 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dbd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dc0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dc3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dc7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dc9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 63), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dcc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 65), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dd0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 65), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dd3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (8, 8), (9, 9), (10, 10), (11, 65), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dd6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 65), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dd9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 65), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ddb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 73), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 65), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ddf) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 73), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 76), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100de2) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 76), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100de6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 80), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dea) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 82) (by decide) rfl

theorem block_l100dba [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100dba :=
  Rest.liftedBlock (rest_l100dba code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100dba x hx)

theorem rest_l100dea [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100dea bytes_l100dea) (entryMap (live .l100dea))
      12 0x100dea bytes_l100dea b_l100dea := by
  have f0 : InstrSpec 0x100dea [0x41, 0x01, 0xEA] (fun s => s.RIP = 0x100dea) (addR32R32Effect 0x100dea 3 10 5)
      [.gpr 10, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100dea 3 10 5).toInstrSpec (add_r32_r32_rex_effect_step 0x100dea 0x41 0xea (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100ded [0x45, 0x31, 0xD6] (fun s => s.RIP = 0x100ded) (xorR32R32Effect 0x100ded 3 14 10)
      [.gpr 14, .gpr 10] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100ded 3 14 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x100ded 0x45 0xd6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100df0 [0x41, 0xC1, 0xC6, 0x10] (fun s => s.RIP = 0x100df0) (rolR32Effect 0x100df0 4 14 16)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR32Effect_footprint 0x100df0 4 14 16).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100df0 0x41 0xc6 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100df4 [0x44, 0x01, 0xF0] (fun s => s.RIP = 0x100df4) (addR32R32Effect 0x100df4 3 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100df4 3 0 14).toInstrSpec (add_r32_r32_rex_effect_step 0x100df4 0x44 0xf0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100df7 [0x31, 0xC5] (fun s => s.RIP = 0x100df7) (xorR32R32Effect 0x100df7 2 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100df7 2 5 0).toInstrSpec (xor_r32_r32_effect_step 0x100df7 0xc5 (by decide)) pre_rip
  have f5 : InstrSpec 0x100df9 [0xC1, 0xC5, 0x0C] (fun s => s.RIP = 0x100df9) (rolR32Effect 0x100df9 3 5 12)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (rolR32Effect_footprint 0x100df9 3 5 12).toInstrSpec (rol_r32_imm8_effect_step 0x100df9 0xc5 0xc (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100dfc [0x41, 0x01, 0xEA] (fun s => s.RIP = 0x100dfc) (addR32R32Effect 0x100dfc 3 10 5)
      [.gpr 10, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100dfc 3 10 5).toInstrSpec (add_r32_r32_rex_effect_step 0x100dfc 0x41 0xea (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100dff [0x45, 0x31, 0xD6] (fun s => s.RIP = 0x100dff) (xorR32R32Effect 0x100dff 3 14 10)
      [.gpr 14, .gpr 10] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100dff 3 14 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x100dff 0x45 0xd6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100e02 [0x41, 0xC1, 0xC6, 0x08] (fun s => s.RIP = 0x100e02) (rolR32Effect 0x100e02 4 14 8)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR32Effect_footprint 0x100e02 4 14 8).toInstrSpec (rol_r32_imm8_rex_effect_step 0x100e02 0x41 0xc6 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100e06 [0x44, 0x01, 0xF0] (fun s => s.RIP = 0x100e06) (addR32R32Effect 0x100e06 3 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100e06 3 0 14).toInstrSpec (add_r32_r32_rex_effect_step 0x100e06 0x44 0xf0 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x100e09 [0x31, 0xC5] (fun s => s.RIP = 0x100e09) (xorR32R32Effect 0x100e09 2 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100e09 2 5 0).toInstrSpec (xor_r32_r32_effect_step 0x100e09 0xc5 (by decide)) pre_rip
  have f11 : InstrSpec 0x100e0b [0xC1, 0xC5, 0x07] (fun s => s.RIP = 0x100e0b) (rolR32Effect 0x100e0b 3 5 7)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (rolR32Effect_footprint 0x100e0b 3 5 7).toInstrSpec (rol_r32_imm8_effect_step 0x100e0b 0xc5 0x7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ded) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100df0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100df4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100df7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100df9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dfc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dff) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e02) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e06) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e09) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 3), (4, 4), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e0b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 3), (4, 4), (5, 75), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e0e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l100dea [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100dea :=
  Rest.liftedBlock (rest_l100dea code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100dea x hx)

theorem rest_l100e0e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e0e bytes_l100e0e) (entryMap (live .l100e0e))
      2 0x100e0e bytes_l100e0e b_l100e0e := by
  have f0 : InstrSpec 0x100e0e [0x48, 0xFF, 0x4C, 0x24, 0x78] (StorePre 0x100e0e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x100e0e + BitVec.ofNat 64 5)) 8) (decMEffect 0x100e0e 5 64 (.sib 4 none 0 (.d8 0x78)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (decMEffect64_footprint 0x100e0e 5 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (dec_m64_effect_step 0x100e0e 0x48 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.fresh (n := 53) f0 .ZF (fun _ => rfl) (decMEffect64_fresh 0x100e0e 5 (.sib 4 none 0 (.d8 0x78)) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e13) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x100e13 5 0xfffffeb7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100e0e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e0e :=
  Rest.liftedBlock (rest_l100e0e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e0e x hx)

theorem rest_l100e19 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e19 bytes_l100e19) (entryMap (live .l100e19))
      20 0x100e19 bytes_l100e19 b_l100e19 := by
  have f0 : InstrSpec 0x100e19 [0x03, 0x5C, 0x24, 0x58] (LoadPre 0x100e19 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100e19 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x100e19 4 3 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 3, .gpr 4] [] [.reg 3, .flags, .rip] :=
    (addR32M32Effect_footprint 0x100e19 4 3 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (add_r32_m32_effect_step 0x100e19 3 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100e1d [0x89, 0x9C, 0x24, 0xF0, 0x00, 0x00, 0x00] (StorePre 0x100e1d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x100e1d + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100e1d 3 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100e1d 3 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_m32_r32_low_effect_step 0x100e1d 3 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x100e24 [0x44, 0x03, 0x6C, 0x24, 0x10] (LoadPre 0x100e24 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100e24 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x100e24 5 13 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 13, .gpr 4] [] [.reg 13, .flags, .rip] :=
    (addR32M32Effect_footprint 0x100e24 5 13 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (add_r32_m32_rex_effect_step 0x100e24 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x100e29 [0x44, 0x89, 0xAC, 0x24, 0xF4, 0x00, 0x00, 0x00] (StorePre 0x100e29 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf4)) s (0x100e29 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100e29 13 (.sib 4 none 0 (.d32 0xf4)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100e29 13 (.sib 4 none 0 (.d32 0xf4))).toInstrSpec (mov_m32_r32_effect_step 0x100e29 0x44 (by decide) 5 (.sib 4 none 0 (.d32 0xf4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x100e31 [0x44, 0x03, 0x64, 0x24, 0x0C] (LoadPre 0x100e31 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100e31 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x100e31 5 12 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 12, .gpr 4] [] [.reg 12, .flags, .rip] :=
    (addR32M32Effect_footprint 0x100e31 5 12 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (add_r32_m32_rex_effect_step 0x100e31 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x100e36 [0x44, 0x89, 0xA4, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x100e36 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x100e36 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100e36 12 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100e36 12 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_m32_r32_effect_step 0x100e36 0x44 (by decide) 4 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x100e3e [0x44, 0x03, 0x54, 0x24, 0x40] (LoadPre 0x100e3e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100e3e + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x100e3e 5 10 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 10, .gpr 4] [] [.reg 10, .flags, .rip] :=
    (addR32M32Effect_footprint 0x100e3e 5 10 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (add_r32_m32_rex_effect_step 0x100e3e 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x100e43 [0x44, 0x89, 0x94, 0x24, 0xFC, 0x00, 0x00, 0x00] (StorePre 0x100e43 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xfc)) s (0x100e43 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100e43 10 (.sib 4 none 0 (.d32 0xfc)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100e43 10 (.sib 4 none 0 (.d32 0xfc))).toInstrSpec (mov_m32_r32_effect_step 0x100e43 0x44 (by decide) 2 (.sib 4 none 0 (.d32 0xfc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x100e4b [0x44, 0x8B, 0x54, 0x24, 0x38] (LoadPre 0x100e4b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x100e4b + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100e4b 10 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x100e4b 10 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r32_m32_effect_step 0x100e4b 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x100e50 [0x44, 0x01, 0xD5] (fun s => s.RIP = 0x100e50) (addR32R32Effect 0x100e50 3 5 10)
      [.gpr 5, .gpr 10] [] [.reg 5, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100e50 3 5 10).toInstrSpec (add_r32_r32_rex_effect_step 0x100e50 0x44 0xd5 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x100e53 [0x89, 0xAC, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x100e53 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x100e53 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100e53 5 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100e53 5 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m32_r32_low_effect_step 0x100e53 5 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x100e5a [0x03, 0x4C, 0x24, 0x34] (LoadPre 0x100e5a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x100e5a + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x100e5a 4 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (addR32M32Effect_footprint 0x100e5a 4 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (add_r32_m32_effect_step 0x100e5a 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x100e5e [0x89, 0x8C, 0x24, 0x04, 0x01, 0x00, 0x00] (StorePre 0x100e5e 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x104)) s (0x100e5e + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100e5e 1 (.sib 4 none 0 (.d32 0x104)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100e5e 1 (.sib 4 none 0 (.d32 0x104))).toInstrSpec (mov_m32_r32_low_effect_step 0x100e5e 1 (.sib 4 none 0 (.d32 0x104)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x100e65 [0x03, 0x54, 0x24, 0x30] (LoadPre 0x100e65 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100e65 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x100e65 4 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (addR32M32Effect_footprint 0x100e65 4 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (add_r32_m32_effect_step 0x100e65 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x100e69 [0x89, 0x94, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x100e69 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x100e69 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100e69 2 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100e69 2 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m32_r32_low_effect_step 0x100e69 2 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x100e70 [0x44, 0x03, 0x5C, 0x24, 0x2C] (LoadPre 0x100e70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x100e70 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x100e70 5 11 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 11, .gpr 4] [] [.reg 11, .flags, .rip] :=
    (addR32M32Effect_footprint 0x100e70 5 11 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (add_r32_m32_rex_effect_step 0x100e70 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x100e75 [0x44, 0x89, 0x9C, 0x24, 0x0C, 0x01, 0x00, 0x00] (StorePre 0x100e75 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10c)) s (0x100e75 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100e75 11 (.sib 4 none 0 (.d32 0x10c)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100e75 11 (.sib 4 none 0 (.d32 0x10c))).toInstrSpec (mov_m32_r32_effect_step 0x100e75 0x44 (by decide) 3 (.sib 4 none 0 (.d32 0x10c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x100e7d [0x44, 0x8B, 0x9C, 0x24, 0x84, 0x00, 0x00, 0x00] (LoadPre 0x100e7d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x100e7d + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x100e7d 11 (.sib 4 none 0 (.d32 0x84)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR32M32Effect_footprint 0x100e7d 11 (.sib 4 none 0 (.d32 0x84))).toInstrSpec (mov_r32_m32_effect_step 0x100e7d 0x44 (by decide) 3 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x100e85 [0x8B, 0x4C, 0x24, 0x04] (LoadPre 0x100e85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100e85 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100e85 1 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x100e85 1 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x100e85 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x100e89 [0x44, 0x01, 0xD9] (fun s => s.RIP = 0x100e89) (addR32R32Effect 0x100e89 3 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100e89 3 1 11).toInstrSpec (add_r32_r32_rex_effect_step 0x100e89 0x44 0xd9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e1d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e24) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e29) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e31) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e36) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e3e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 62), (11, 11), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e43) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 62), (11, 11), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e4b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 11), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e50) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 11), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e53) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 11), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e5a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 70), (2, 2), (3, 53), (4, 4), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 11), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e5e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 70), (2, 2), (3, 53), (4, 4), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 11), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e65) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 70), (2, 73), (3, 53), (4, 4), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 11), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e69) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 70), (2, 73), (3, 53), (4, 4), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 11), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e70) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 70), (2, 73), (3, 53), (4, 4), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 76), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e75) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 70), (2, 73), (3, 53), (4, 4), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 76), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e7d) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 70), (2, 73), (3, 53), (4, 4), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 79), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e85) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 81), (2, 73), (3, 53), (4, 4), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 79), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e89) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 83), (2, 73), (3, 53), (4, 4), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 79), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e8c) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 85) (by decide) rfl

theorem block_l100e19 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e19 :=
  Rest.liftedBlock (rest_l100e19 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e19 x hx)

theorem rest_l100e8c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e8c bytes_l100e8c) (entryMap (live .l100e8c))
      20 0x100e8c bytes_l100e8c b_l100e8c := by
  have f0 : InstrSpec 0x100e8c [0x89, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x100e8c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x100e8c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100e8c 1 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100e8c 1 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m32_r32_low_effect_step 0x100e8c 1 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x100e93 [0x03, 0x44, 0x24, 0x28] (LoadPre 0x100e93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100e93 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x100e93 4 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (addR32M32Effect_footprint 0x100e93 4 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (add_r32_m32_effect_step 0x100e93 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100e97 [0x89, 0x84, 0x24, 0x14, 0x01, 0x00, 0x00] (StorePre 0x100e97 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x114)) s (0x100e97 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100e97 0 (.sib 4 none 0 (.d32 0x114)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100e97 0 (.sib 4 none 0 (.d32 0x114))).toInstrSpec (mov_m32_r32_low_effect_step 0x100e97 0 (.sib 4 none 0 (.d32 0x114)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100e9e [0x03, 0x74, 0x24, 0x24] (LoadPre 0x100e9e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x100e9e + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x100e9e 4 6 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (addR32M32Effect_footprint 0x100e9e 4 6 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (add_r32_m32_effect_step 0x100e9e 6 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x100ea2 [0x89, 0xB4, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x100ea2 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x100ea2 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100ea2 6 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100ea2 6 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m32_r32_low_effect_step 0x100ea2 6 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x100ea9 [0x44, 0x03, 0x44, 0x24, 0x20] (LoadPre 0x100ea9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100ea9 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x100ea9 5 8 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 8, .gpr 4] [] [.reg 8, .flags, .rip] :=
    (addR32M32Effect_footprint 0x100ea9 5 8 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (add_r32_m32_rex_effect_step 0x100ea9 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x100eae [0x44, 0x89, 0x84, 0x24, 0x1C, 0x01, 0x00, 0x00] (StorePre 0x100eae 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11c)) s (0x100eae + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100eae 8 (.sib 4 none 0 (.d32 0x11c)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100eae 8 (.sib 4 none 0 (.d32 0x11c))).toInstrSpec (mov_m32_r32_effect_step 0x100eae 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0x11c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x100eb6 [0x44, 0x8B, 0x64, 0x24, 0x3C] (LoadPre 0x100eb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x100eb6 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100eb6 12 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR32M32Effect_footprint 0x100eb6 12 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_effect_step 0x100eb6 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x100ebb [0x45, 0x01, 0xE1] (fun s => s.RIP = 0x100ebb) (addR32R32Effect 0x100ebb 3 9 12)
      [.gpr 9, .gpr 12] [] [.reg 9, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100ebb 3 9 12).toInstrSpec (add_r32_r32_rex_effect_step 0x100ebb 0x45 0xe1 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100ebe [0x44, 0x89, 0x8C, 0x24, 0x20, 0x01, 0x00, 0x00] (StorePre 0x100ebe 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x100ebe + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100ebe 9 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100ebe 9 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_m32_r32_effect_step 0x100ebe 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x100ec6 [0x44, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x100ec6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x100ec6 + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x100ec6 8 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x100ec6 8 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r32_m32_effect_step 0x100ec6 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x100ece [0x44, 0x01, 0xC7] (fun s => s.RIP = 0x100ece) (addR32R32Effect 0x100ece 3 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (addR32R32Effect_footprint 0x100ece 3 7 8).toInstrSpec (add_r32_r32_rex_effect_step 0x100ece 0x44 0xc7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x100ed1 [0x44, 0x03, 0x74, 0x24, 0x1C] (LoadPre 0x100ed1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x100ed1 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x100ed1 5 14 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 14, .gpr 4] [] [.reg 14, .flags, .rip] :=
    (addR32M32Effect_footprint 0x100ed1 5 14 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (add_r32_m32_rex_effect_step 0x100ed1 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x100ed6 [0x44, 0x03, 0x7C, 0x24, 0x18] (LoadPre 0x100ed6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100ed6 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x100ed6 5 15 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 15, .gpr 4] [] [.reg 15, .flags, .rip] :=
    (addR32M32Effect_footprint 0x100ed6 5 15 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (add_r32_m32_rex_effect_step 0x100ed6 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x100edb [0x89, 0xBC, 0x24, 0x24, 0x01, 0x00, 0x00] (StorePre 0x100edb 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x124)) s (0x100edb + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100edb 7 (.sib 4 none 0 (.d32 0x124)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100edb 7 (.sib 4 none 0 (.d32 0x124))).toInstrSpec (mov_m32_r32_low_effect_step 0x100edb 7 (.sib 4 none 0 (.d32 0x124)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x100ee2 [0x44, 0x89, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00] (StorePre 0x100ee2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x100ee2 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100ee2 14 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100ee2 14 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_m32_r32_effect_step 0x100ee2 0x44 (by decide) 6 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x100eea [0x44, 0x89, 0xBC, 0x24, 0x2C, 0x01, 0x00, 0x00] (StorePre 0x100eea 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x12c)) s (0x100eea + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100eea 15 (.sib 4 none 0 (.d32 0x12c)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100eea 15 (.sib 4 none 0 (.d32 0x12c))).toInstrSpec (mov_m32_r32_effect_step 0x100eea 0x44 (by decide) 7 (.sib 4 none 0 (.d32 0x12c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x100ef2 [0x48, 0x8B, 0x7C, 0x24, 0x70] (LoadPre 0x100ef2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x100ef2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100ef2 7 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x100ef2 7 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x100ef2 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x100ef7 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x100ef7) (movR64R64Effect 0x100ef7 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100ef7 0 7).toInstrSpec (mov_r64_r64_effect_step 0x100ef7 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x100efa [0x48, 0xC1, 0xE0, 0x06] (fun s => s.RIP = 0x100efa) (shlR64Effect 0x100efa 4 0 6)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x100efa 4 0 6).toInstrSpec (shl_r64_imm8_effect_step 0x100efa 0x48 0xe0 0x6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e93) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e97) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e9e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ea2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ea9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 57), (7, 7), (8, 60), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100eae) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 57), (7, 7), (8, 60), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100eb6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 57), (7, 7), (8, 60), (9, 9), (10, 10), (11, 11), (12, 63), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ebb) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 57), (7, 7), (8, 60), (9, 65), (10, 10), (11, 11), (12, 63), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ebe) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 57), (7, 7), (8, 60), (9, 65), (10, 10), (11, 11), (12, 63), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ec6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 57), (7, 7), (8, 68), (9, 65), (10, 10), (11, 11), (12, 63), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ece) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 57), (7, 70), (8, 68), (9, 65), (10, 10), (11, 11), (12, 63), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ed1) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 57), (7, 70), (8, 68), (9, 65), (10, 10), (11, 11), (12, 63), (14, 72), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ed6) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 57), (7, 70), (8, 68), (9, 65), (10, 10), (11, 11), (12, 63), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100edb) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 57), (7, 70), (8, 68), (9, 65), (10, 10), (11, 11), (12, 63), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ee2) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 57), (7, 70), (8, 68), (9, 65), (10, 10), (11, 11), (12, 63), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100eea) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 57), (7, 70), (8, 68), (9, 65), (10, 10), (11, 11), (12, 63), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ef2) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 54), (1, 1), (4, 4), (6, 57), (7, 79), (8, 68), (9, 65), (10, 10), (11, 11), (12, 63), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ef7) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 1), (4, 4), (6, 57), (7, 79), (8, 68), (9, 65), (10, 10), (11, 11), (12, 63), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100efa) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 1), (4, 4), (6, 57), (7, 79), (8, 68), (9, 65), (10, 10), (11, 11), (12, 63), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100efe) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 85) (by decide) rfl

theorem block_l100e8c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e8c :=
  Rest.liftedBlock (rest_l100e8c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e8c x hx)

theorem rest_l100efe [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100efe bytes_l100efe) (entryMap (live .l100efe))
      20 0x100efe bytes_l100efe b_l100efe := by
  have f0 : InstrSpec 0x100efe [0x48, 0x8B, 0x54, 0x24, 0x68] (LoadPre 0x100efe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x100efe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100efe 2 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x100efe 2 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x100efe 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100f03 [0x48, 0x8B, 0x4C, 0x02, 0x38] (LoadPre 0x100f03 (fun s => AddrMode.addr (.sib 2 (some 0) 0 (.d8 0x38)) s (0x100f03 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100f03 1 (.sib 2 (some 0) 0 (.d8 0x38)))
      [.gpr 2, .gpr 0] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100f03 1 (.sib 2 (some 0) 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x100f03 0x48 (by decide) 1 (.sib 2 (some 0) 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100f08 [0x48, 0x89, 0x8C, 0x24, 0x68, 0x01, 0x00, 0x00] (StorePre 0x100f08 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x100f08 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f08 1 (.sib 4 none 0 (.d32 0x168)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f08 1 (.sib 4 none 0 (.d32 0x168))).toInstrSpec (mov_m64_r64_effect_step 0x100f08 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100f10 [0x48, 0x8B, 0x4C, 0x02, 0x30] (LoadPre 0x100f10 (fun s => AddrMode.addr (.sib 2 (some 0) 0 (.d8 0x30)) s (0x100f10 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100f10 1 (.sib 2 (some 0) 0 (.d8 0x30)))
      [.gpr 2, .gpr 0] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100f10 1 (.sib 2 (some 0) 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x100f10 0x48 (by decide) 1 (.sib 2 (some 0) 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x100f15 [0x48, 0x89, 0x8C, 0x24, 0x60, 0x01, 0x00, 0x00] (StorePre 0x100f15 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x100f15 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f15 1 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f15 1 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (mov_m64_r64_effect_step 0x100f15 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x100f1d [0x48, 0x8B, 0x4C, 0x02, 0x28] (LoadPre 0x100f1d (fun s => AddrMode.addr (.sib 2 (some 0) 0 (.d8 0x28)) s (0x100f1d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100f1d 1 (.sib 2 (some 0) 0 (.d8 0x28)))
      [.gpr 2, .gpr 0] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100f1d 1 (.sib 2 (some 0) 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x100f1d 0x48 (by decide) 1 (.sib 2 (some 0) 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x100f22 [0x48, 0x89, 0x8C, 0x24, 0x58, 0x01, 0x00, 0x00] (StorePre 0x100f22 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x100f22 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f22 1 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f22 1 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (mov_m64_r64_effect_step 0x100f22 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x100f2a [0x48, 0x8B, 0x4C, 0x02, 0x20] (LoadPre 0x100f2a (fun s => AddrMode.addr (.sib 2 (some 0) 0 (.d8 0x20)) s (0x100f2a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100f2a 1 (.sib 2 (some 0) 0 (.d8 0x20)))
      [.gpr 2, .gpr 0] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100f2a 1 (.sib 2 (some 0) 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x100f2a 0x48 (by decide) 1 (.sib 2 (some 0) 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x100f2f [0x48, 0x89, 0x8C, 0x24, 0x50, 0x01, 0x00, 0x00] (StorePre 0x100f2f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x100f2f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f2f 1 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f2f 1 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (mov_m64_r64_effect_step 0x100f2f 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x100f37 [0x48, 0x8B, 0x4C, 0x02, 0x18] (LoadPre 0x100f37 (fun s => AddrMode.addr (.sib 2 (some 0) 0 (.d8 0x18)) s (0x100f37 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100f37 1 (.sib 2 (some 0) 0 (.d8 0x18)))
      [.gpr 2, .gpr 0] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100f37 1 (.sib 2 (some 0) 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x100f37 0x48 (by decide) 1 (.sib 2 (some 0) 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x100f3c [0x48, 0x89, 0x8C, 0x24, 0x48, 0x01, 0x00, 0x00] (StorePre 0x100f3c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x100f3c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f3c 1 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f3c 1 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (mov_m64_r64_effect_step 0x100f3c 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x100f44 [0x48, 0x8B, 0x4C, 0x02, 0x10] (LoadPre 0x100f44 (fun s => AddrMode.addr (.sib 2 (some 0) 0 (.d8 0x10)) s (0x100f44 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100f44 1 (.sib 2 (some 0) 0 (.d8 0x10)))
      [.gpr 2, .gpr 0] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100f44 1 (.sib 2 (some 0) 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x100f44 0x48 (by decide) 1 (.sib 2 (some 0) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x100f49 [0x48, 0x89, 0x8C, 0x24, 0x40, 0x01, 0x00, 0x00] (StorePre 0x100f49 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x100f49 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f49 1 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f49 1 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_m64_r64_effect_step 0x100f49 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x100f51 [0x48, 0x8B, 0x0C, 0x02] (LoadPre 0x100f51 (fun s => AddrMode.addr (.sib 2 (some 0) 0 .none) s (0x100f51 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100f51 1 (.sib 2 (some 0) 0 .none))
      [.gpr 2, .gpr 0] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100f51 1 (.sib 2 (some 0) 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x100f51 0x48 (by decide) 1 (.sib 2 (some 0) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x100f55 [0x48, 0x8B, 0x54, 0x02, 0x08] (LoadPre 0x100f55 (fun s => AddrMode.addr (.sib 2 (some 0) 0 (.d8 0x8)) s (0x100f55 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100f55 2 (.sib 2 (some 0) 0 (.d8 0x8)))
      [.gpr 2, .gpr 0] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x100f55 2 (.sib 2 (some 0) 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x100f55 0x48 (by decide) 2 (.sib 2 (some 0) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x100f5a [0x48, 0x89, 0x94, 0x24, 0x38, 0x01, 0x00, 0x00] (StorePre 0x100f5a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x100f5a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f5a 2 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f5a 2 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_m64_r64_effect_step 0x100f5a 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x100f62 [0x48, 0x89, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00] (StorePre 0x100f62 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x100f62 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f62 1 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f62 1 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_m64_r64_effect_step 0x100f62 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x100f6a [0x48, 0xC7, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100f6a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x100f6a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100f6a (.sib 4 none 0 (.d32 0xe8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100f6a (.sib 4 none 0 (.d32 0xe8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100f6a 0x48 (by decide) (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x100f76 [0x48, 0xC7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100f76 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x100f76 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100f76 (.sib 4 none 0 (.d32 0xe0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100f76 (.sib 4 none 0 (.d32 0xe0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100f76 0x48 (by decide) (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x100f82 [0x48, 0xC7, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100f82 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x100f82 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100f82 (.sib 4 none 0 (.d32 0xd8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100f82 (.sib 4 none 0 (.d32 0xd8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100f82 0x48 (by decide) (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f03) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f08) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 55), (2, 53), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f10) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 58), (2, 53), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f15) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 58), (2, 53), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f1d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 53), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f22) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 61), (2, 53), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f2a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 64), (2, 53), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f2f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 64), (2, 53), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f37) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 53), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f3c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 67), (2, 53), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f44) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 70), (2, 53), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f49) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 70), (2, 53), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f51) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 73), (2, 53), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f55) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 73), (2, 75), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f5a) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 73), (2, 75), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f62) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 73), (2, 75), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f6a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 73), (2, 75), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f76) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 73), (2, 75), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f82) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 73), (2, 75), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f8e) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 82) (by decide) rfl

theorem block_l100efe [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100efe :=
  Rest.liftedBlock (rest_l100efe code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100efe x hx)

theorem rest_l100f8e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100f8e bytes_l100f8e) (entryMap (live .l100f8e))
      7 0x100f8e bytes_l100f8e b_l100f8e := by
  have f0 : InstrSpec 0x100f8e [0x48, 0xC7, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100f8e 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x100f8e + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100f8e (.sib 4 none 0 (.d32 0xd0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100f8e (.sib 4 none 0 (.d32 0xd0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100f8e 0x48 (by decide) (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x100f9a [0x48, 0xC7, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100f9a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x100f9a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100f9a (.sib 4 none 0 (.d32 0xc8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100f9a (.sib 4 none 0 (.d32 0xc8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100f9a 0x48 (by decide) (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x100fa6 [0x48, 0xC7, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100fa6 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x100fa6 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100fa6 (.sib 4 none 0 (.d32 0xc0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100fa6 (.sib 4 none 0 (.d32 0xc0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100fa6 0x48 (by decide) (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100fb2 [0x48, 0xC7, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100fb2 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x100fb2 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100fb2 (.sib 4 none 0 (.d32 0xb8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100fb2 (.sib 4 none 0 (.d32 0xb8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100fb2 0x48 (by decide) (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x100fbe [0x48, 0xC7, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x100fbe 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x100fbe + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100fbe (.sib 4 none 0 (.d32 0xb0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x100fbe (.sib 4 none 0 (.d32 0xb0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x100fbe 0x48 (by decide) (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x100fca [0xB9, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100fca) (movR32Imm32Effect 0x100fca 5 1 0x3)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x100fca 5 1 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x100fca 0xb9 (by decide) 0x3) pre_rip
  have f6 : InstrSpec 0x100fcf [0x90] (fun s => s.RIP = 0x100fcf) (fun _ => nopEffect 0x100fcf 1)
      [] [] [.rip] :=
    (nopEffect_footprint 0x100fcf 1).toInstrSpec (nop_effect_step 0x100fcf) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f9a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fa6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fb2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fbe) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fca) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 58), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fcf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 58), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fd0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l100f8e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100f8e :=
  Rest.liftedBlock (rest_l100f8e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100f8e x hx)

theorem rest_l100fd0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100fd0 bytes_l100fd0) (entryMap (live .l100fd0))
      15 0x100fd0 bytes_l100fd0 b_l100fd0 := by
  have f0 : InstrSpec 0x100fd0 [0x0F, 0xB6, 0x94, 0x0C, 0xED, 0x00, 0x00, 0x00] (LoadPre 0x100fd0 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xed)) s (0x100fd0 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x100fd0 8 2 (.sib 4 (some 1) 0 (.d32 0xed)))
      [.gpr 4, .gpr 1] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x100fd0 8 2 (.sib 4 (some 1) 0 (.d32 0xed))).toInstrSpec (movzx_r32_m8_effect_step 0x100fd0 2 (.sib 4 (some 1) 0 (.d32 0xed)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100fd8 [0x0F, 0xB6, 0xB4, 0x0C, 0xEE, 0x00, 0x00, 0x00] (LoadPre 0x100fd8 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xee)) s (0x100fd8 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x100fd8 8 6 (.sib 4 (some 1) 0 (.d32 0xee)))
      [.gpr 4, .gpr 1] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x100fd8 8 6 (.sib 4 (some 1) 0 (.d32 0xee))).toInstrSpec (movzx_r32_m8_effect_step 0x100fd8 6 (.sib 4 (some 1) 0 (.d32 0xee)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100fe0 [0x32, 0x94, 0x0C, 0x2D, 0x01, 0x00, 0x00] (LoadPre 0x100fe0 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0x12d)) s (0x100fe0 + BitVec.ofNat 64 7)) 1) (xorR8M8Effect 0x100fe0 7 2 (.sib 4 (some 1) 0 (.d32 0x12d)))
      [.gpr 2, .gpr 4, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x100fe0 7 2 (.sib 4 (some 1) 0 (.d32 0x12d))).toInstrSpec (xor_r8_m8_effect_step 0x100fe0 2 (by decide) (.sib 4 (some 1) 0 (.d32 0x12d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x100fe7 [0x40, 0x32, 0xB4, 0x0C, 0x2E, 0x01, 0x00, 0x00] (LoadPre 0x100fe7 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0x12e)) s (0x100fe7 + BitVec.ofNat 64 8)) 1) (xorR8M8Effect 0x100fe7 8 6 (.sib 4 (some 1) 0 (.d32 0x12e)))
      [.gpr 6, .gpr 4, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x100fe7 8 6 (.sib 4 (some 1) 0 (.d32 0x12e))).toInstrSpec (xor_r8_m8_rex_effect_step 0x100fe7 0x40 (by decide) 6 (.sib 4 (some 1) 0 (.d32 0x12e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x100fef [0x88, 0x94, 0x0C, 0xAD, 0x00, 0x00, 0x00] (StorePre 0x100fef 7 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xad)) s (0x100fef + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x100fef 7 2 (.sib 4 (some 1) 0 (.d32 0xad)))
      [.gpr 2, .gpr 4, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x100fef 7 2 (.sib 4 (some 1) 0 (.d32 0xad))).toInstrSpec (mov_m8_r8_effect_step 0x100fef 2 (by decide) (.sib 4 (some 1) 0 (.d32 0xad)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x100ff6 [0x0F, 0xB6, 0x94, 0x0C, 0xEF, 0x00, 0x00, 0x00] (LoadPre 0x100ff6 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xef)) s (0x100ff6 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x100ff6 8 2 (.sib 4 (some 1) 0 (.d32 0xef)))
      [.gpr 4, .gpr 1] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x100ff6 8 2 (.sib 4 (some 1) 0 (.d32 0xef))).toInstrSpec (movzx_r32_m8_effect_step 0x100ff6 2 (.sib 4 (some 1) 0 (.d32 0xef)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x100ffe [0x32, 0x94, 0x0C, 0x2F, 0x01, 0x00, 0x00] (LoadPre 0x100ffe (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0x12f)) s (0x100ffe + BitVec.ofNat 64 7)) 1) (xorR8M8Effect 0x100ffe 7 2 (.sib 4 (some 1) 0 (.d32 0x12f)))
      [.gpr 2, .gpr 4, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x100ffe 7 2 (.sib 4 (some 1) 0 (.d32 0x12f))).toInstrSpec (xor_r8_m8_effect_step 0x100ffe 2 (by decide) (.sib 4 (some 1) 0 (.d32 0x12f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x101005 [0x40, 0x88, 0xB4, 0x0C, 0xAE, 0x00, 0x00, 0x00] (StorePre 0x101005 8 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xae)) s (0x101005 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x101005 8 6 (.sib 4 (some 1) 0 (.d32 0xae)))
      [.gpr 6, .gpr 4, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x101005 8 6 (.sib 4 (some 1) 0 (.d32 0xae))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101005 0x40 (by decide) 6 (.sib 4 (some 1) 0 (.d32 0xae)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10100d [0x0F, 0xB6, 0xB4, 0x0C, 0xF0, 0x00, 0x00, 0x00] (LoadPre 0x10100d (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xf0)) s (0x10100d + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10100d 8 6 (.sib 4 (some 1) 0 (.d32 0xf0)))
      [.gpr 4, .gpr 1] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x10100d 8 6 (.sib 4 (some 1) 0 (.d32 0xf0))).toInstrSpec (movzx_r32_m8_effect_step 0x10100d 6 (.sib 4 (some 1) 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x101015 [0x40, 0x32, 0xB4, 0x0C, 0x30, 0x01, 0x00, 0x00] (LoadPre 0x101015 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0x130)) s (0x101015 + BitVec.ofNat 64 8)) 1) (xorR8M8Effect 0x101015 8 6 (.sib 4 (some 1) 0 (.d32 0x130)))
      [.gpr 6, .gpr 4, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101015 8 6 (.sib 4 (some 1) 0 (.d32 0x130))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101015 0x40 (by decide) 6 (.sib 4 (some 1) 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x10101d [0x88, 0x94, 0x0C, 0xAF, 0x00, 0x00, 0x00] (StorePre 0x10101d 7 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xaf)) s (0x10101d + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10101d 7 2 (.sib 4 (some 1) 0 (.d32 0xaf)))
      [.gpr 2, .gpr 4, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x10101d 7 2 (.sib 4 (some 1) 0 (.d32 0xaf))).toInstrSpec (mov_m8_r8_effect_step 0x10101d 2 (by decide) (.sib 4 (some 1) 0 (.d32 0xaf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x101024 [0x40, 0x88, 0xB4, 0x0C, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x101024 8 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xb0)) s (0x101024 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x101024 8 6 (.sib 4 (some 1) 0 (.d32 0xb0)))
      [.gpr 6, .gpr 4, .gpr 1] [] [.rip] :=
    (movM8R8Effect_footprint 0x101024 8 6 (.sib 4 (some 1) 0 (.d32 0xb0))).toInstrSpec (mov_m8_r8_rex_effect_step 0x101024 0x40 (by decide) 6 (.sib 4 (some 1) 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10102c [0x48, 0x83, 0xC1, 0x04] (fun s => s.RIP = 0x10102c) (addR64Imm8Effect 0x10102c 1 0x4)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10102c 1 0x4).toInstrSpec (add_r64_imm8_effect_step 0x10102c 0x48 0xc1 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101030 [0x48, 0x83, 0xF9, 0x43] (fun s => s.RIP = 0x101030) (cmpR64Imm8Effect 0x101030 1 0x43)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x101030 1 0x43).toInstrSpec (cmp_r64_imm8_effect_step 0x101030 0x48 0xf9 0x43 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fd8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fe0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (4, 4), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fe7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 57), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fef) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 57), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ff6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 62), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ffe) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 64), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101005) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 64), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10100d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 64), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101015) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 64), (4, 4), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10101d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 64), (4, 4), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101024) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 64), (4, 4), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10102c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 73), (2, 64), (4, 4), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101030) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 73), (2, 64), (4, 4), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101034) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 77) (jcc_rel8_effect_step 0x101034 5 0x9a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100fd0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100fd0 :=
  Rest.liftedBlock (rest_l100fd0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100fd0 x hx)

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

theorem_by block_l100d02_eval :
    program.runBlock (dialect code) ⟨.l100d02, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100d26_eval :
    program.runBlock (dialect code) ⟨.l100d26, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100d4a_eval :
    program.runBlock (dialect code) ⟨.l100d4a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100d72_eval :
    program.runBlock (dialect code) ⟨.l100d72, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100d94_eval :
    program.runBlock (dialect code) ⟨.l100d94, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100dba_eval :
    program.runBlock (dialect code) ⟨.l100dba, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100dea_eval :
    program.runBlock (dialect code) ⟨.l100dea, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e0e_eval :
    program.runBlock (dialect code) ⟨.l100e0e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e19_eval :
    program.runBlock (dialect code) ⟨.l100e19, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e8c_eval :
    program.runBlock (dialect code) ⟨.l100e8c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100efe_eval :
    program.runBlock (dialect code) ⟨.l100efe, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100f8e_eval :
    program.runBlock (dialect code) ⟨.l100f8e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100fd0_eval :
    program.runBlock (dialect code) ⟨.l100fd0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
