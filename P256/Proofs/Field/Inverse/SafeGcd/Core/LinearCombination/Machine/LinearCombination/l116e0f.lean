import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116e0f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11132f bytes_l116e0f) (entryMap (live .l116e0f))
      19 0x11132f bytes_l116e0f b_l116e0f := by
  have f0 : InstrSpec 0x11132f [0x41, 0x89, 0xD3] (fun s => s.RIP = 0x11132f) (movR32R32Effect 0x11132f 3 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x11132f 3 11 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x11132f 0x41 0xd3 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x111332 [0x45, 0x30, 0xC3] (fun s => s.RIP = 0x111332) (xorR8R8Effect 0x111332 3 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (xorR8R8Effect_footprint 0x111332 3 11 8).toInstrSpec (xor_r8_r8_rex_effect_step 0x111332 0x45 0xc3 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x111335 [0x44, 0x88, 0x5C, 0x24, 0x10] (StorePre 0x111335 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111335 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x111335 5 11 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111335 5 11 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x111335 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x11133a [0x41, 0x80, 0xF3, 0x01] (fun s => s.RIP = 0x11133a) (xorR8Imm8Effect 0x11133a 4 11 0x1)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR8Imm8Effect_footprint 0x11133a 4 11 0x1).toInstrSpec (xor_r8_imm8_rex_effect_step 0x11133a 0x41 0xf3 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11133e [0x4C, 0x8B, 0x74, 0x24, 0x28] (LoadPre 0x11133e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11133e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11133e 14 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x11133e 14 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x11133e 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x111343 [0x4D, 0x89, 0xF5] (fun s => s.RIP = 0x111343) (movR64R64Effect 0x111343 13 14)
      [.gpr 14] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x111343 13 14).toInstrSpec (mov_r64_r64_effect_step 0x111343 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111346 [0x49, 0xF7, 0xDD] (fun s => s.RIP = 0x111346) (negR64Effect 0x111346 13)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (negR64Effect_footprint 0x111346 13).toInstrSpec (neg_r64_effect_step 0x111346 0x49 0xdd (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111349 [0xBD, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x111349) (movR32Imm32Effect 0x111349 5 5 0x0)
      [] [] [.reg 5, .rip] :=
    (movR32Imm32Effect_footprint 0x111349 5 5 0x0).toInstrSpec (mov_r32_imm32_effect_step 0x111349 0xbd (by decide) 0x0) pre_rip
  have f8 : InstrSpec 0x11134e [0x4C, 0x19, 0xFD] (fun s => s.RIP = 0x11134e) (atFlags StatusFlags.CF (sbbR64R64Effect 0x11134e 5 15))
      [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x11134e 5 15).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x11134e 0x4c 0xfd c (by decide) (by decide))) pre_rip
  have f9 : InstrSpec 0x111351 [0x41, 0xB8, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x111351) (movR32Imm32Effect 0x111351 6 8 0x0)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x111351 6 8 0x0).toInstrSpec (mov_r32_imm32_rex_effect_step 0x111351 0x41 0xb8 (by decide) (by decide) 0x0) pre_rip
  have f10 : InstrSpec 0x111357 [0x49, 0x19, 0xF0] (fun s => s.RIP = 0x111357) (atFlags StatusFlags.CF (sbbR64R64Effect 0x111357 8 6))
      [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x111357 8 6).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x111357 0x49 0xf0 c (by decide) (by decide))) pre_rip
  have f11 : InstrSpec 0x11135a [0xBA, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11135a) (movR32Imm32Effect 0x11135a 5 2 0x0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x11135a 5 2 0x0).toInstrSpec (mov_r32_imm32_effect_step 0x11135a 0xba (by decide) 0x0) pre_rip
  have f12 : InstrSpec 0x11135f [0x48, 0x19, 0xC2] (fun s => s.RIP = 0x11135f) (atFlags StatusFlags.CF (sbbR64R64Effect 0x11135f 2 0))
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x11135f 2 0).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x11135f 0x48 0xc2 c (by decide) (by decide))) pre_rip
  have f13 : InstrSpec 0x111362 [0x0F, 0x93, 0x04, 0x24] (StorePre 0x111362 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111362 + BitVec.ofNat 64 4)) 1) (atFlags (condHolds 3) (setccM8Effect 0x111362 4 (.sib 4 none 0 .none)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.rip] :=
    (setccM8Effect_footprint 0x111362 4 (.sib 4 none 0 .none) 3).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x111362 3 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x111366 [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x111366) (movR64R64Effect 0x111366 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x111366 6 4).toInstrSpec (mov_r64_r64_effect_step 0x111366 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x111369 [0x0F, 0xB6, 0x34, 0x24] (LoadPre 0x111369 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111369 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x111369 4 6 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x111369 4 6 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x111369 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x11136d [0x48, 0x89, 0x74, 0x24, 0x38] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11136d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11136d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11136d 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11136d 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x11136d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f17 : InstrSpec 0x111372 [0x44, 0x88, 0x1C, 0x24] (StorePre 0x111372 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111372 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111372 4 11 (.sib 4 none 0 .none))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111372 4 11 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x111372 0x44 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x111376 [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x111376) (movR64R64Effect 0x111376 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x111376 6 4).toInstrSpec (mov_r64_r64_effect_step 0x111376 0x48 0xe6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111332) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111335) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11133a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 58), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11133e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 58), (12, 12), (14, 60), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111343) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 58), (12, 12), (13, 62), (14, 60), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111346) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f6 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 58), (12, 12), (13, 64), (14, 60), (15, 15), (16, 65), (22, 22), (39, 39), (51, 51)]) (p' := 0x111349) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 58), (12, 12), (13, 64), (14, 60), (15, 15), (16, 65), (22, 22), (39, 39), (51, 51)]) (p' := 0x11134e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 70) f8 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x11134e 5 15 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 58), (12, 12), (13, 64), (14, 60), (15, 15), (16, 70), (22, 22), (39, 39), (51, 51)]) (p' := 0x111351) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 69), (6, 6), (7, 7), (8, 72), (9, 9), (10, 10), (11, 58), (12, 12), (13, 64), (14, 60), (15, 15), (16, 70), (22, 22), (39, 39), (51, 51)]) (p' := 0x111357) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 75) f10 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x111357 8 6 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 69), (6, 6), (7, 7), (8, 74), (9, 9), (10, 10), (11, 58), (12, 12), (13, 64), (14, 60), (15, 15), (16, 75), (22, 22), (39, 39), (51, 51)]) (p' := 0x11135a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 77), (3, 3), (4, 4), (5, 69), (6, 6), (7, 7), (8, 74), (9, 9), (10, 10), (11, 58), (12, 12), (13, 64), (14, 60), (15, 15), (16, 75), (22, 22), (39, 39), (51, 51)]) (p' := 0x11135f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 80) f12 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x11135f 2 0 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 79), (3, 3), (4, 4), (5, 69), (6, 6), (7, 7), (8, 74), (9, 9), (10, 10), (11, 58), (12, 12), (13, 64), (14, 60), (15, 15), (16, 80), (22, 22), (39, 39), (51, 51)]) (p' := 0x111362) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 79), (3, 3), (4, 4), (5, 69), (6, 6), (7, 7), (8, 74), (9, 9), (10, 10), (11, 58), (12, 12), (13, 64), (14, 60), (15, 15), (16, 80), (22, 22), (39, 39), (51, 51)]) (p' := 0x111366) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 1), (2, 79), (3, 3), (4, 4), (5, 69), (7, 7), (8, 74), (9, 9), (10, 10), (11, 58), (12, 12), (13, 64), (14, 60), (15, 15), (16, 80), (22, 22), (39, 39), (51, 51)]) (p' := 0x111369) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 1), (2, 79), (3, 3), (4, 4), (5, 69), (6, 84), (7, 7), (8, 74), (9, 9), (10, 10), (11, 58), (12, 12), (13, 64), (14, 60), (15, 15), (16, 80), (22, 22), (39, 39), (51, 51)]) (p' := 0x11136d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 79), (3, 3), (4, 4), (5, 69), (6, 84), (7, 7), (8, 74), (9, 9), (10, 10), (11, 58), (12, 12), (13, 64), (14, 60), (15, 15), (16, 80), (22, 22), (39, 39), (51, 51)]) (p' := 0x111372) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 1), (2, 79), (3, 3), (4, 4), (5, 69), (6, 84), (7, 7), (8, 74), (9, 9), (10, 10), (11, 58), (12, 12), (13, 64), (14, 60), (15, 15), (16, 80), (22, 22), (39, 39), (51, 51)]) (p' := 0x111376) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 79), (3, 3), (4, 4), (5, 69), (7, 7), (8, 74), (9, 9), (10, 10), (11, 58), (12, 12), (13, 64), (14, 60), (15, 15), (16, 80), (22, 22), (39, 39), (51, 51)]) (p' := 0x111379) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 89) (by decide) rfl

theorem block_l116e0f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l116e0f :=
  Rest.liftedBlock (rest_l116e0f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l116e0f x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
