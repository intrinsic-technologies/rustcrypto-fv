import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Core.l1179fa_1
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1179fa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111f1a bytes_l1179fa) (entryMap (live .l1179fa))
      22 0x111f1a bytes_l1179fa b_l1179fa := by
  have f0 : InstrSpec 0x111f1a [0x89, 0xD0] (fun s => s.RIP = 0x111f1a) (movR32R32Effect 0x111f1a 2 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x111f1a 2 0 2).toInstrSpec (mov_r32_r32_effect_step 0x111f1a 0xd0 (by decide)) pre_rip
  have f1 : InstrSpec 0x111f1c [0xF7, 0xD0] (fun s => s.RIP = 0x111f1c) (notR32Effect 0x111f1c 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR32Effect_footprint 0x111f1c 2 0).toInstrSpec (not_r32_effect_step 0x111f1c 0xd0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x111f1e [0x8D, 0x4A, 0xC2] (fun s => s.RIP = 0x111f1e) (leaR32Effect 0x111f1e 3 1 (.base 2 (.d8 0xc2)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x111f1e 3 1 (.base 2 (.d8 0xc2))).toInstrSpec (lea_r32_effect_step 0x111f1e 1 (.base 2 (.d8 0xc2)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x111f21 [0x21, 0xC1] (fun s => s.RIP = 0x111f21) (andR32R32Effect 0x111f21 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR32R32Effect_footprint 0x111f21 2 1 0).toInstrSpec (and_r32_r32_effect_step 0x111f21 0xc1 (by decide)) pre_rip
  have f4 : InstrSpec 0x111f23 [0xC1, 0xE9, 0x1F] (fun s => s.RIP = 0x111f23) (shrR32Effect 0x111f23 3 1 31)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x111f23 3 1 31).toInstrSpec (shr_r32_imm8_effect_step 0x111f23 0xe9 0x1f (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x111f26 [0x88, 0x4C, 0x24, 0x08] (StorePre 0x111f26 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111f26 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111f26 4 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111f26 4 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_effect_step 0x111f26 1 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x111f2a [0x0F, 0xB6, 0x44, 0x24, 0x08] (LoadPre 0x111f2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111f2a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111f2a 5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x111f2a 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x111f2a 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x111f2f [0xF7, 0xD8] (fun s => s.RIP = 0x111f2f) (negR32Effect 0x111f2f 2 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR32Effect_footprint 0x111f2f 2 0).toInstrSpec (neg_r32_effect_step 0x111f2f 0xd8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111f31 [0x48, 0x89, 0x94, 0x24, 0x50, 0x01, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111f31 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x111f31 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111f31 2 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111f31 2 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111f31 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f9 : InstrSpec 0x111f39 [0x41, 0x89, 0xD0] (fun s => s.RIP = 0x111f39) (movR32R32Effect 0x111f39 3 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x111f39 3 8 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x111f39 0x41 0xd0 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x111f3c [0x41, 0x83, 0xF0, 0x3E] (fun s => s.RIP = 0x111f3c) (xorR32Imm8Effect 0x111f3c 4 8 0x3e)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x111f3c 4 8 0x3e).toInstrSpec (xor_r32_imm8_rex_effect_step 0x111f3c 0x41 0xf0 0x3e (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x111f40 [0x41, 0x21, 0xC0] (fun s => s.RIP = 0x111f40) (andR32R32Effect 0x111f40 3 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (andR32R32Effect_footprint 0x111f40 3 8 0).toInstrSpec (and_r32_r32_rex_effect_step 0x111f40 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x111f43 [0x41, 0x83, 0xF0, 0x3E] (fun s => s.RIP = 0x111f43) (xorR32Imm8Effect 0x111f43 4 8 0x3e)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x111f43 4 8 0x3e).toInstrSpec (xor_r32_imm8_rex_effect_step 0x111f43 0x41 0xf0 0x3e (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111f47 [0x48, 0x8B, 0x4C, 0x24, 0x58] (LoadPre 0x111f47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x111f47 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111f47 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x111f47 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x111f47 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x111f4c [0x0F, 0xB6, 0x44, 0x24, 0x78] (LoadPre 0x111f4c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x111f4c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111f4c 5 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x111f4c 5 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (movzx_r32_m8_effect_step 0x111f4c 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x111f51 [0x88, 0x44, 0x24, 0x08] (StorePre 0x111f51 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111f51 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111f51 4 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111f51 4 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_effect_step 0x111f51 0 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x111f55 [0x0F, 0xB6, 0x54, 0x24, 0x08] (LoadPre 0x111f55 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111f55 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111f55 5 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x111f55 5 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x111f55 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x111f5a [0x48, 0x8B, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x111f5a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x111f5a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111f5a 6 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x111f5a 6 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x111f5a 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x111f62 [0x0F, 0xB6, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x111f62 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x111f62 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x111f62 8 0 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x111f62 8 0 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (movzx_r32_m8_effect_step 0x111f62 0 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x111f6a [0x88, 0x44, 0x24, 0x08] (StorePre 0x111f6a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111f6a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111f6a 4 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111f6a 4 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_effect_step 0x111f6a 0 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f1c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f1e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f21) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f23) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f26) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f2a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f2f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f31) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f39) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 66), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (8, 69), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f3c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 66), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (8, 71), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f40) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 66), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (8, 73), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f43) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f12 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 77) (ρ' := [(0, 66), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (8, 75), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f47) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 66), (1, 78), (2, 2), (3, 3), (4, 4), (5, 5), (8, 75), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f4c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 78), (2, 2), (3, 3), (4, 4), (5, 5), (8, 75), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f51) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 78), (2, 2), (3, 3), (4, 4), (5, 5), (8, 75), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f55) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 80), (1, 78), (2, 83), (3, 3), (4, 4), (5, 5), (8, 75), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f5a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 80), (1, 78), (2, 83), (3, 3), (4, 4), (5, 5), (6, 85), (8, 75), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f62) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 78), (2, 83), (3, 3), (4, 4), (5, 5), (6, 85), (8, 75), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f6a) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 87), (1, 78), (2, 83), (3, 3), (4, 4), (5, 5), (6, 85), (8, 75), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x111f6e) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1179fa_1 code

theorem block_l1179fa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1179fa :=
  Rest.liftedBlock (rest_l1179fa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1179fa x hx)

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

theorem_by block_l1179fa_eval :
    program.runBlock (dialect code) ⟨.l1179fa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
