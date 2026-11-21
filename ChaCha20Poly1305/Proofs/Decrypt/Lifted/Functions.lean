import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Program
import X86Proofs.Instructions.Branch.Triple
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Values

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

theorem rest_l101aa0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101aa0 bytes_l101aa0) (entryMap (live .l101aa0))
      1 0x101aa0 bytes_l101aa0 b_l101aa0 := by
  have f0 : InstrSpec 0x101aa0 [0xC3] (RetPre 0x101aa0) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101aa0).toInstrSpec (ret_effect_step 0x101aa0) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f0 (by decide) rfl rfl rfl (by decide)

theorem block_l101aa0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101aa0 :=
  Rest.liftedBlock (rest_l101aa0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101aa0 x hx)

theorem rest_l101e40_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x101e40 bytes_l101e40) [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 88), (7, 72), (8, 78), (9, 84), (10, 86), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x101e9f bytes_l101e40_1 b_l101e40_1 := by
  have f20 : InstrSpec 0x101e9f [0x4C, 0x89, 0x10] (StorePre 0x101e9f 3 (fun s => AddrMode.addr (.base 0 .none) s (0x101e9f + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x101e9f 10 (.base 0 .none))
      [.gpr 10, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x101e9f 10 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x101e9f 0x4c (by decide) 2 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x101ea2 [0x48, 0x89, 0x70, 0x08] (StorePre 0x101ea2 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x101ea2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101ea2 6 (.base 0 (.d8 0x8)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x101ea2 6 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x101ea2 0x48 (by decide) 6 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x101ea6 [0x89, 0x48, 0x10] (StorePre 0x101ea6 3 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x101ea6 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101ea6 1 (.base 0 (.d8 0x10)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101ea6 1 (.base 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_low_effect_step 0x101ea6 1 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x101ea9 [0x89, 0x50, 0x14] (StorePre 0x101ea9 3 (fun s => AddrMode.addr (.base 0 (.d8 0x14)) s (0x101ea9 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101ea9 2 (.base 0 (.d8 0x14)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101ea9 2 (.base 0 (.d8 0x14))).toInstrSpec (mov_m32_r32_low_effect_step 0x101ea9 2 (.base 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x101eac [0x89, 0x78, 0x18] (StorePre 0x101eac 3 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x101eac + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101eac 7 (.base 0 (.d8 0x18)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101eac 7 (.base 0 (.d8 0x18))).toInstrSpec (mov_m32_r32_low_effect_step 0x101eac 7 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x101eaf [0x44, 0x89, 0x40, 0x1C] (StorePre 0x101eaf 4 (fun s => AddrMode.addr (.base 0 (.d8 0x1c)) s (0x101eaf + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101eaf 8 (.base 0 (.d8 0x1c)))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM32R32Effect_footprint 0x101eaf 8 (.base 0 (.d8 0x1c))).toInstrSpec (mov_m32_r32_effect_step 0x101eaf 0x44 (by decide) 0 (.base 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x101eb3 [0x44, 0x89, 0x48, 0x20] (StorePre 0x101eb3 4 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x101eb3 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101eb3 9 (.base 0 (.d8 0x20)))
      [.gpr 9, .gpr 0] [] [.rip] :=
    (movM32R32Effect_footprint 0x101eb3 9 (.base 0 (.d8 0x20))).toInstrSpec (mov_m32_r32_effect_step 0x101eb3 0x44 (by decide) 1 (.base 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x101eb7 [0xC3] (RetPre 0x101eb7) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101eb7).toInstrSpec (ret_effect_step 0x101eb7) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 88), (7, 72), (8, 78), (9, 84), (10, 86), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ea2) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 88), (7, 72), (8, 78), (9, 84), (10, 86), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ea6) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 88), (7, 72), (8, 78), (9, 84), (10, 86), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ea9) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 88), (7, 72), (8, 78), (9, 84), (10, 86), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101eac) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 88), (7, 72), (8, 78), (9, 84), (10, 86), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101eaf) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 88), (7, 72), (8, 78), (9, 84), (10, 86), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101eb3) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 88), (7, 72), (8, 78), (9, 84), (10, 86), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101eb7) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f27 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 98) f27 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 99) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 98), (5, 5), (6, 88), (7, 72), (8, 78), (9, 84), (10, 86), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f27 (by decide) rfl rfl rfl (by decide)

theorem rest_l101e40 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e40 bytes_l101e40) (entryMap (live .l101e40))
      28 0x101e40 bytes_l101e40 b_l101e40 := by
  have f0 : InstrSpec 0x101e40 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x101e40) (movR64R64Effect 0x101e40 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x101e40 0 7).toInstrSpec (mov_r64_r64_effect_step 0x101e40 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101e43 [0xC7, 0x47, 0x34, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101e43 7 (fun s => AddrMode.addr (.base 7 (.d8 0x34)) s (0x101e43 + BitVec.ofNat 64 7)) 4) (movM32Imm32Effect 0x101e43 7 (.base 7 (.d8 0x34)) 0x0)
      [.gpr 7] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x101e43 7 (.base 7 (.d8 0x34)) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x101e43 (.base 7 (.d8 0x34)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x101e4a [0x48, 0xC7, 0x47, 0x2C, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101e4a 8 (fun s => AddrMode.addr (.base 7 (.d8 0x2c)) s (0x101e4a + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x101e4a (.base 7 (.d8 0x2c)) 0x0)
      [.gpr 7] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101e4a (.base 7 (.d8 0x2c)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101e4a 0x48 (by decide) (.base 7 (.d8 0x2c)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101e52 [0x48, 0xC7, 0x47, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x101e52 8 (fun s => AddrMode.addr (.base 7 (.d8 0x24)) s (0x101e52 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x101e52 (.base 7 (.d8 0x24)) 0x0)
      [.gpr 7] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x101e52 (.base 7 (.d8 0x24)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x101e52 0x48 (by decide) (.base 7 (.d8 0x24)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101e5a [0xB9, 0xFF, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101e5a) (movR32Imm32Effect 0x101e5a 5 1 0x3ffffff)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x101e5a 5 1 0x3ffffff).toInstrSpec (mov_r32_imm32_effect_step 0x101e5a 0xb9 (by decide) 0x3ffffff) pre_rip
  have f5 : InstrSpec 0x101e5f [0x23, 0x0E] (LoadPre 0x101e5f (fun s => AddrMode.addr (.base 6 .none) s (0x101e5f + BitVec.ofNat 64 2)) 4) (andR32M32Effect 0x101e5f 2 1 (.base 6 .none))
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR32M32Effect_footprint 0x101e5f 2 1 (.base 6 .none)).toInstrSpec (and_r32_m32_effect_step 0x101e5f 1 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x101e61 [0x8B, 0x56, 0x03] (LoadPre 0x101e61 (fun s => AddrMode.addr (.base 6 (.d8 0x3)) s (0x101e61 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101e61 2 (.base 6 (.d8 0x3)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x101e61 2 (.base 6 (.d8 0x3))).toInstrSpec (mov_r32_m32_low_effect_step 0x101e61 2 (.base 6 (.d8 0x3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x101e64 [0x8B, 0x7E, 0x06] (LoadPre 0x101e64 (fun s => AddrMode.addr (.base 6 (.d8 0x6)) s (0x101e64 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101e64 7 (.base 6 (.d8 0x6)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x101e64 7 (.base 6 (.d8 0x6))).toInstrSpec (mov_r32_m32_low_effect_step 0x101e64 7 (.base 6 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x101e67 [0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x101e67) (shrR32Effect 0x101e67 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x101e67 3 2 2).toInstrSpec (shr_r32_imm8_effect_step 0x101e67 0xea 0x2 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101e6a [0x81, 0xE2, 0x03, 0xFF, 0xFF, 0x03] (fun s => s.RIP = 0x101e6a) (andR32Imm32Effect 0x101e6a 6 2 0x3ffff03)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101e6a 6 2 0x3ffff03).toInstrSpec (and_r32_imm32_effect_step 0x101e6a 0xe2 0x3ffff03 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101e70 [0xC1, 0xEF, 0x04] (fun s => s.RIP = 0x101e70) (shrR32Effect 0x101e70 3 7 4)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x101e70 3 7 4).toInstrSpec (shr_r32_imm8_effect_step 0x101e70 0xef 0x4 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101e73 [0x81, 0xE7, 0xFF, 0xC0, 0xFF, 0x03] (fun s => s.RIP = 0x101e73) (andR32Imm32Effect 0x101e73 6 7 0x3ffc0ff)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101e73 6 7 0x3ffc0ff).toInstrSpec (and_r32_imm32_effect_step 0x101e73 0xe7 0x3ffc0ff (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101e79 [0x44, 0x8B, 0x46, 0x09] (LoadPre 0x101e79 (fun s => AddrMode.addr (.base 6 (.d8 0x9)) s (0x101e79 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101e79 8 (.base 6 (.d8 0x9)))
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x101e79 8 (.base 6 (.d8 0x9))).toInstrSpec (mov_r32_m32_effect_step 0x101e79 0x44 (by decide) 0 (.base 6 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x101e7d [0x41, 0xC1, 0xE8, 0x06] (fun s => s.RIP = 0x101e7d) (shrR32Effect 0x101e7d 4 8 6)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x101e7d 4 8 6).toInstrSpec (shr_r32_imm8_rex_effect_step 0x101e7d 0x41 0xe8 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x101e81 [0x41, 0x81, 0xE0, 0xFF, 0x3F, 0xF0, 0x03] (fun s => s.RIP = 0x101e81) (andR32Imm32Effect 0x101e81 7 8 0x3f03fff)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101e81 7 8 0x3f03fff).toInstrSpec (and_r32_imm32_rex_effect_step 0x101e81 0x41 0xe0 0x3f03fff (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x101e88 [0x44, 0x8B, 0x4E, 0x0C] (LoadPre 0x101e88 (fun s => AddrMode.addr (.base 6 (.d8 0xc)) s (0x101e88 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101e88 9 (.base 6 (.d8 0xc)))
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x101e88 9 (.base 6 (.d8 0xc))).toInstrSpec (mov_r32_m32_effect_step 0x101e88 0x44 (by decide) 1 (.base 6 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x101e8c [0x41, 0xC1, 0xE9, 0x08] (fun s => s.RIP = 0x101e8c) (shrR32Effect 0x101e8c 4 9 8)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x101e8c 4 9 8).toInstrSpec (shr_r32_imm8_rex_effect_step 0x101e8c 0x41 0xe9 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x101e90 [0x41, 0x81, 0xE1, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x101e90) (andR32Imm32Effect 0x101e90 7 9 0xfffff)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x101e90 7 9 0xfffff).toInstrSpec (and_r32_imm32_rex_effect_step 0x101e90 0x41 0xe1 0xfffff (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x101e97 [0x4C, 0x8B, 0x56, 0x10] (LoadPre 0x101e97 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x101e97 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101e97 10 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x101e97 10 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x101e97 0x4c (by decide) 2 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x101e9b [0x48, 0x8B, 0x76, 0x18] (LoadPre 0x101e9b (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x101e9b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101e9b 6 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x101e9b 6 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101e9b 0x48 (by decide) 6 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e43) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e4a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e52) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e5a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e5f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 60), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e61) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 60), (2, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e64) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 60), (2, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e67) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 60), (2, 66), (3, 3), (4, 4), (5, 5), (6, 6), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e6a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 6), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e70) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 6), (7, 70), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e73) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 6), (7, 72), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e79) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 6), (7, 72), (8, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e7d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 6), (7, 72), (8, 76), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e81) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 6), (7, 72), (8, 78), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e88) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 6), (7, 72), (8, 78), (9, 80), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e8c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 6), (7, 72), (8, 78), (9, 82), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e90) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 6), (7, 72), (8, 78), (9, 84), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e97) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f18 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 6), (7, 72), (8, 78), (9, 84), (10, 86), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e9b) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 53), (1, 60), (2, 68), (3, 3), (4, 4), (5, 5), (6, 88), (7, 72), (8, 78), (9, 84), (10, 86), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e9f) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101e40_1 code

theorem block_l101e40 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e40 :=
  Rest.liftedBlock (rest_l101e40 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e40 x hx)

theorem rest_l102020 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102020 bytes_l102020) (entryMap (live .l102020))
      2 0x102020 bytes_l102020 b_l102020 := by
  have f0 : InstrSpec 0x102020 [0x48, 0x3B, 0x77, 0x10] (LoadPre 0x102020 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x102020 + BitVec.ofNat 64 4)) 8) (cmpR64M64Effect 0x102020 6 (.base 7 (.d8 0x10)))
      [.gpr 6, .gpr 7] [] [.flags, .rip] :=
    (cmpR64M64Effect_footprint 0x102020 6 (.base 7 (.d8 0x10))).toInstrSpec (cmp_r64_m64_effect_step 0x102020 0x48 (by decide) 6 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102024) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x102024 7 0x4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102020 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102020 :=
  Rest.liftedBlock (rest_l102020 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102020 x hx)

theorem rest_l102026 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102026 bytes_l102026) (entryMap (live .l102026))
      1 0x102026 bytes_l102026 b_l102026 := by
  have f0 : InstrSpec 0x102026 [0x48, 0x89, 0x77, 0x10] (StorePre 0x102026 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x102026 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102026 6 (.base 7 (.d8 0x10)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x102026 6 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x102026 0x48 (by decide) 6 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10202a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l102026 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102026 :=
  Rest.liftedBlock (rest_l102026 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102026 x hx)

theorem rest_l10202a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10202a bytes_l10202a) (entryMap (live .l10202a))
      1 0x10202a bytes_l10202a b_l10202a := by
  have f0 : InstrSpec 0x10202a [0xC3] (RetPre 0x10202a) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10202a).toInstrSpec (ret_effect_step 0x10202a) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f0 (by decide) rfl rfl rfl (by decide)

theorem block_l10202a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10202a :=
  Rest.liftedBlock (rest_l10202a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10202a x hx)

theorem rest_l102d70_1 [Bindings] (code : CodeMap) :
    Rest (n := 94) code lifted (codeRange 0x102d70 bytes_l102d70) [(0, 92), (1, 90), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x102db4 bytes_l102d70_1 b_l102d70_1 := by
  have f20 : InstrSpec 0x102db4 [0xC3] (RetPre 0x102db4) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x102db4).toInstrSpec (ret_effect_step 0x102db4) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f20 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 95) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 96) (ρ' := [(0, 92), (1, 90), (2, 55), (3, 3), (4, 95), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f20 (by decide) rfl rfl rfl (by decide)

theorem rest_l102d70 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102d70 bytes_l102d70) (entryMap (live .l102d70))
      21 0x102d70 bytes_l102d70 b_l102d70 := by
  have f0 : InstrSpec 0x102d70 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x102d70) (movR64R64Effect 0x102d70 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x102d70 8 2).toInstrSpec (mov_r64_r64_effect_step 0x102d70 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102d73 [0x48, 0x89, 0xFA] (fun s => s.RIP = 0x102d73) (movR64R64Effect 0x102d73 2 7)
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x102d73 2 7).toInstrSpec (mov_r64_r64_effect_step 0x102d73 0x48 0xfa (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102d76 [0x40, 0x0F, 0xB6, 0xCE] (fun s => s.RIP = 0x102d76) (movzxR32R8Effect 0x102d76 4 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x102d76 4 1 6).toInstrSpec (movzx_r32_r8_rex_effect_step 0x102d76 0x40 (by decide) 0xce (by decide)) pre_rip
  have f3 : InstrSpec 0x102d7a [0x48, 0xB8, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01] (fun s => s.RIP = 0x102d7a) (movR64Imm64Effect 0x102d7a 0 0x101010101010101)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x102d7a 0 0x101010101010101).toInstrSpec (mov_r64_imm64_effect_step 0x102d7a 0x48 0xb8 (by decide) (by decide) 0x101010101010101) pre_rip
  have f4 : InstrSpec 0x102d84 [0x48, 0x0F, 0xAF, 0xC1] (fun s => s.RIP = 0x102d84) (imulR64R64Effect 0x102d84 4 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x102d84 4 0 1).toInstrSpec (imul_r64_r64_effect_step 0x102d84 0x48 (by decide) 0xc1 (by decide)) pre_rip
  have f5 : InstrSpec 0x102d88 [0x89, 0xD1] (fun s => s.RIP = 0x102d88) (movR32R32Effect 0x102d88 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x102d88 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x102d88 0xd1 (by decide)) pre_rip
  have f6 : InstrSpec 0x102d8a [0xF7, 0xD9] (fun s => s.RIP = 0x102d8a) (negR32Effect 0x102d8a 2 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR32Effect_footprint 0x102d8a 2 1).toInstrSpec (neg_r32_effect_step 0x102d8a 0xd9 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102d8c [0x83, 0xE1, 0x07] (fun s => s.RIP = 0x102d8c) (andR32Imm8Effect 0x102d8c 3 1 0x7)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x102d8c 3 1 0x7).toInstrSpec (and_r32_imm8_effect_step 0x102d8c 0xe1 0x7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102d8f [0x49, 0x39, 0xC8] (fun s => s.RIP = 0x102d8f) (cmpR64R64Effect 0x102d8f 8 1)
      [.gpr 8, .gpr 1] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x102d8f 8 1).toInstrSpec (cmp_r64_r64_effect_step 0x102d8f 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x102d92 [0x49, 0x0F, 0x42, 0xC8] (fun s => s.RIP = 0x102d92) (atFlags (condHolds 2) (cmovR64R64Effect 0x102d92 4 1 8))
      [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .rip] :=
    (cmovR64R64Effect_footprint 0x102d92 4 1 8 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x102d92 2 0x49 (by decide) 0xc8 (by decide) c)) pre_rip
  have f10 : InstrSpec 0x102d96 [0x49, 0x29, 0xC8] (fun s => s.RIP = 0x102d96) (subR64R64Effect 0x102d96 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x102d96 8 1).toInstrSpec (sub_r64_r64_effect_step 0x102d96 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x102d99 [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x102d99) (movR64R64Effect 0x102d99 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102d99 6 8).toInstrSpec (mov_r64_r64_effect_step 0x102d99 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x102d9c [0x48, 0xC1, 0xEE, 0x03] (fun s => s.RIP = 0x102d9c) (shrR64Effect 0x102d9c 4 6 3)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x102d9c 4 6 3).toInstrSpec (shr_r64_imm8_effect_step 0x102d9c 0x48 0xee 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x102da0 [0x41, 0x83, 0xE0, 0x07] (fun s => s.RIP = 0x102da0) (andR32Imm8Effect 0x102da0 4 8 0x7)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x102da0 4 8 0x7).toInstrSpec (and_r32_imm8_rex_effect_step 0x102da0 0x41 0xe0 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x102da4 [0xF3, 0xAA] (RepPre 0x102da4 (RepStosbPre 0x102da4)) (repStosbEffect 0x102da4)
      [.gpr 0, .gpr 7, .gpr 1, .df] [] [.reg 7, .reg 1, .rip] :=
    (repStosbEffect_footprint 0x102da4).toInstrSpecOfRuns (rep_stosb_runs hstride 0x102da4) (RepStosOk.of_stateOf RepStosbPre.iff (by lift_reads) (by lift_reads) (by lift_reads))
  have f15 : InstrSpec 0x102da6 [0x48, 0x89, 0xF1] (fun s => s.RIP = 0x102da6) (movR64R64Effect 0x102da6 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102da6 1 6).toInstrSpec (mov_r64_r64_effect_step 0x102da6 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x102da9 [0xF3, 0x48, 0xAB] (RepPre 0x102da9 (RepStosqPre 0x102da9)) (repStosqEffect 0x102da9)
      [.gpr 0, .gpr 7, .gpr 1, .df] [] [.reg 7, .reg 1, .rip] :=
    (repStosqEffect_footprint 0x102da9).toInstrSpecOfRuns (rep_stosq_runs hstride 0x102da9 0x48 (by decide)) (RepStosOk.of_stateOf RepStosqPre.iff (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x102dac [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x102dac) (movR64R64Effect 0x102dac 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102dac 1 8).toInstrSpec (mov_r64_r64_effect_step 0x102dac 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x102daf [0xF3, 0xAA] (RepPre 0x102daf (RepStosbPre 0x102daf)) (repStosbEffect 0x102daf)
      [.gpr 0, .gpr 7, .gpr 1, .df] [] [.reg 7, .reg 1, .rip] :=
    (repStosbEffect_footprint 0x102daf).toInstrSpecOfRuns (rep_stosb_runs hstride 0x102daf) (RepStosOk.of_stateOf RepStosbPre.iff (by lift_reads) (by lift_reads) (by lift_reads))
  have f19 : InstrSpec 0x102db1 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x102db1) (movR64R64Effect 0x102db1 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x102db1 0 2).toInstrSpec (mov_r64_r64_effect_step 0x102db1 0x48 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d73) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d76) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d7a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d84) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d88) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d8a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 65), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d8c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 67), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d8f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 67), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d92) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d96) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 73), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d99) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 75), (7, 7), (8, 73), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102d9c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 7), (8, 73), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102da0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 7), (8, 79), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102da4) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 81), (8, 79), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102da6) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 61), (1, 83), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 81), (8, 79), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102da9) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 85), (8, 79), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dac) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 61), (1, 87), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 85), (8, 79), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102daf) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 90) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 91) (ρ' := [(0, 61), (1, 90), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102db1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 92), (1, 90), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102db4) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l102d70_1 code

theorem block_l102d70 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102d70 :=
  Rest.liftedBlock (rest_l102d70 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102d70 x hx)

theorem rest_l102dc0 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102dc0 bytes_l102dc0) (entryMap (live .l102dc0))
      16 0x102dc0 bytes_l102dc0 b_l102dc0 := by
  have f0 : InstrSpec 0x102dc0 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x102dc0) (movR64R64Effect 0x102dc0 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x102dc0 0 7).toInstrSpec (mov_r64_r64_effect_step 0x102dc0 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102dc3 [0x41, 0x89, 0xC0] (fun s => s.RIP = 0x102dc3) (movR32R32Effect 0x102dc3 3 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x102dc3 3 8 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x102dc3 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102dc6 [0x41, 0xF7, 0xD8] (fun s => s.RIP = 0x102dc6) (negR32Effect 0x102dc6 3 8)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (negR32Effect_footprint 0x102dc6 3 8).toInstrSpec (neg_r32_rex_effect_step 0x102dc6 0x41 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102dc9 [0x41, 0x83, 0xE0, 0x07] (fun s => s.RIP = 0x102dc9) (andR32Imm8Effect 0x102dc9 4 8 0x7)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x102dc9 4 8 0x7).toInstrSpec (and_r32_imm8_rex_effect_step 0x102dc9 0x41 0xe0 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x102dcd [0x4C, 0x39, 0xC2] (fun s => s.RIP = 0x102dcd) (cmpR64R64Effect 0x102dcd 2 8)
      [.gpr 2, .gpr 8] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x102dcd 2 8).toInstrSpec (cmp_r64_r64_effect_step 0x102dcd 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x102dd0 [0x4C, 0x0F, 0x42, 0xC2] (fun s => s.RIP = 0x102dd0) (atFlags (condHolds 2) (cmovR64R64Effect 0x102dd0 4 8 2))
      [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .rip] :=
    (cmovR64R64Effect_footprint 0x102dd0 4 8 2 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x102dd0 2 0x4c (by decide) 0xc2 (by decide) c)) pre_rip
  have f6 : InstrSpec 0x102dd4 [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x102dd4) (movR64R64Effect 0x102dd4 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102dd4 1 8).toInstrSpec (mov_r64_r64_effect_step 0x102dd4 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102dd7 [0xF3, 0xA4] (RepPre 0x102dd7 (RepMovsbPre 0x102dd7)) (repMovsbEffect 0x102dd7)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsbEffect_footprint 0x102dd7).toInstrSpecOfRuns (rep_movsb_runs hstride 0x102dd7) (RepMovsOk.of_stateOf RepMovsbPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f8 : InstrSpec 0x102dd9 [0x4C, 0x29, 0xC2] (fun s => s.RIP = 0x102dd9) (subR64R64Effect 0x102dd9 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x102dd9 2 8).toInstrSpec (sub_r64_r64_effect_step 0x102dd9 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x102ddc [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x102ddc) (movR64R64Effect 0x102ddc 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102ddc 1 2).toInstrSpec (mov_r64_r64_effect_step 0x102ddc 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x102ddf [0x48, 0xC1, 0xE9, 0x03] (fun s => s.RIP = 0x102ddf) (shrR64Effect 0x102ddf 4 1 3)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x102ddf 4 1 3).toInstrSpec (shr_r64_imm8_effect_step 0x102ddf 0x48 0xe9 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x102de3 [0xF3, 0x48, 0xA5] (RepPre 0x102de3 (RepMovsqPre 0x102de3)) (repMovsqEffect 0x102de3)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x102de3).toInstrSpecOfRuns (rep_movsq_runs hstride 0x102de3 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f12 : InstrSpec 0x102de6 [0x83, 0xE2, 0x07] (fun s => s.RIP = 0x102de6) (andR32Imm8Effect 0x102de6 3 2 0x7)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x102de6 3 2 0x7).toInstrSpec (and_r32_imm8_effect_step 0x102de6 0xe2 0x7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x102de9 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x102de9) (movR64R64Effect 0x102de9 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x102de9 1 2).toInstrSpec (mov_r64_r64_effect_step 0x102de9 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x102dec [0xF3, 0xA4] (RepPre 0x102dec (RepMovsbPre 0x102dec)) (repMovsbEffect 0x102dec)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsbEffect_footprint 0x102dec).toInstrSpecOfRuns (rep_movsb_runs hstride 0x102dec) (RepMovsOk.of_stateOf RepMovsbPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f15 : InstrSpec 0x102dee [0xC3] (RetPre 0x102dee) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x102dee).toInstrSpec (ret_effect_step 0x102dee) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dc3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dc6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dc9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dcd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dd0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dd4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dd7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dd9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (2, 70), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ddc) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 72), (2, 70), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ddf) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 74), (2, 70), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102de3) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (2, 70), (3, 3), (4, 4), (5, 5), (6, 76), (7, 77), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102de6) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (2, 79), (3, 3), (4, 4), (5, 5), (6, 76), (7, 77), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102de9) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 81), (2, 79), (3, 3), (4, 4), (5, 5), (6, 76), (7, 77), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dec) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 84) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 85) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 86) (ρ' := [(0, 53), (1, 85), (2, 79), (3, 3), (4, 4), (5, 5), (6, 83), (7, 84), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102dee) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f15 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 88) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 89) (ρ' := [(0, 53), (1, 85), (2, 79), (3, 3), (4, 88), (5, 5), (6, 83), (7, 84), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f15 (by decide) rfl rfl rfl (by decide)

theorem block_l102dc0 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102dc0 :=
  Rest.liftedBlock (rest_l102dc0 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102dc0 x hx)

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

theorem_by block_l101aa0_eval :
    program.runBlock (dialect code) ⟨.l101aa0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e40_eval :
    program.runBlock (dialect code) ⟨.l101e40, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102020_eval :
    program.runBlock (dialect code) ⟨.l102020, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102026_eval :
    program.runBlock (dialect code) ⟨.l102026, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10202a_eval :
    program.runBlock (dialect code) ⟨.l10202a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102d70_eval :
    program.runBlock (dialect code) ⟨.l102d70, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102dc0_eval :
    program.runBlock (dialect code) ⟨.l102dc0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
