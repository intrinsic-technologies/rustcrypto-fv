import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l118420_1 [Bindings] (code : CodeMap) :
    Rest (n := 99) code lifted (codeRange 0x112940 bytes_l118420) [(0, 91), (1, 89), (2, 92), (3, 3), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 96), (11, 82), (12, 12), (13, 13), (14, 62), (15, 94), (16, 97), (22, 22), (39, 39), (51, 51)]
      17 0x11298d bytes_l118420_1 b_l118420_1 := by
  have f20 : InstrSpec 0x11298d [0x48, 0x13, 0x5C, 0x24, 0x18] (LoadPre 0x11298d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11298d + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11298d 3 (.sib 4 none 0 (.d8 0x18))))
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x11298d 3 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x11298d 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x112992 [0x0F, 0xB6, 0x4C, 0x24, 0x08] (LoadPre 0x112992 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112992 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x112992 5 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x112992 5 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x112992 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x112997 [0x4C, 0x11, 0xE9] (fun s => s.RIP = 0x112997) (atFlags StatusFlags.CF (adcR64R64Effect 0x112997 1 13))
      [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112997 1 13).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112997 0x4c 0xe9 c (by decide) (by decide))) pre_rip
  have f23 : InstrSpec 0x11299a [0x0F, 0x92, 0x44, 0x24, 0x08] (StorePre 0x11299a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11299a + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 2) (setccM8Effect 0x11299a 5 (.sib 4 none 0 (.d8 0x8))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.rip] :=
    (setccM8Effect_footprint 0x11299a 5 (.sib 4 none 0 (.d8 0x8)) 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x11299a 2 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x11299f [0x49, 0x01, 0xC2] (fun s => s.RIP = 0x11299f) (addR64R64Effect 0x11299f 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11299f 10 0).toInstrSpec (add_r64_r64_effect_step 0x11299f 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x1129a2 [0x49, 0x83, 0xD7, 0x00] (fun s => s.RIP = 0x1129a2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1129a2 15 0x0))
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x1129a2 15 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x1129a2 0x49 0xd7 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f26 : InstrSpec 0x1129a6 [0x49, 0x01, 0xF2] (fun s => s.RIP = 0x1129a6) (addR64R64Effect 0x1129a6 10 6)
      [.gpr 10, .gpr 6] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1129a6 10 6).toInstrSpec (add_r64_r64_effect_step 0x1129a6 0x49 0xf2 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x1129a9 [0x49, 0x83, 0xD7, 0x00] (fun s => s.RIP = 0x1129a9) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1129a9 15 0x0))
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x1129a9 15 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x1129a9 0x49 0xd7 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f28 : InstrSpec 0x1129ad [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x1129ad) (movR64R64Effect 0x1129ad 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1129ad 0 13).toInstrSpec (mov_r64_r64_effect_step 0x1129ad 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x1129b0 [0xBA, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x1129b0) (movR32Imm32Effect 0x1129b0 5 2 0xffffffff)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1129b0 5 2 0xffffffff).toInstrSpec (mov_r32_imm32_effect_step 0x1129b0 0xba (by decide) 0xffffffff) pre_rip
  have f30 : InstrSpec 0x1129b5 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x1129b5) (mulR64Effect 0x1129b5 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1129b5 2).toInstrSpec (mul_r64_effect_step 0x1129b5 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x1129b8 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x1129b8) (movR64R64Effect 0x1129b8 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1129b8 14 2).toInstrSpec (mov_r64_r64_effect_step 0x1129b8 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x1129bb [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x1129bb) (movR64R64Effect 0x1129bb 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1129bb 13 0).toInstrSpec (mov_r64_r64_effect_step 0x1129bb 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x1129be [0x49, 0x01, 0xDD] (fun s => s.RIP = 0x1129be) (addR64R64Effect 0x1129be 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1129be 13 3).toInstrSpec (add_r64_r64_effect_step 0x1129be 0x49 0xdd (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x1129c1 [0x49, 0x83, 0xD6, 0x00] (fun s => s.RIP = 0x1129c1) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1129c1 14 0x0))
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x1129c1 14 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x1129c1 0x49 0xd6 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f35 : InstrSpec 0x1129c5 [0x4D, 0x8B, 0x60, 0x10] (LoadPre 0x1129c5 (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x1129c5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1129c5 12 (.base 8 (.d8 0x10)))
      [.gpr 8] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x1129c5 12 (.base 8 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1129c5 0x4d (by decide) 4 (.base 8 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x1129c9 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x1129c9) (movR64R64Effect 0x1129c9 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1129c9 0 12).toInstrSpec (mov_r64_r64_effect_step 0x1129c9 0x4c 0xe0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f20 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 100) f20 .CF (fun _ => rfl) (adcR64M64Effect_fresh 0x11298d 3 (.sib 4 none 0 (.d8 0x18)) _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 101) (ρ' := [(0, 91), (1, 89), (2, 92), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 96), (11, 82), (12, 12), (13, 13), (14, 62), (15, 94), (16, 100), (22, 22), (39, 39), (51, 51)]) (p' := 0x112992) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 91), (1, 102), (2, 92), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 96), (11, 82), (12, 12), (13, 13), (14, 62), (15, 94), (16, 100), (22, 22), (39, 39), (51, 51)]) (p' := 0x112997) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 105) f22 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x112997 1 13 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 106) (ρ' := [(0, 91), (1, 104), (2, 92), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 96), (11, 82), (12, 12), (13, 13), (14, 62), (15, 94), (16, 105), (22, 22), (39, 39), (51, 51)]) (p' := 0x11299a) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 91), (1, 104), (2, 92), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 96), (11, 82), (12, 12), (13, 13), (14, 62), (15, 94), (16, 105), (22, 22), (39, 39), (51, 51)]) (p' := 0x11299f) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f24 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 109) f24 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 110) (ρ' := [(0, 91), (1, 104), (2, 92), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 108), (11, 82), (12, 12), (13, 13), (14, 62), (15, 94), (16, 109), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129a2) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f25 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 91), (1, 104), (2, 92), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 108), (11, 82), (12, 12), (13, 13), (14, 62), (15, 111), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129a6) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f26 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 114) f26 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 115) (ρ' := [(0, 91), (1, 104), (2, 92), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 113), (11, 82), (12, 12), (13, 13), (14, 62), (15, 111), (16, 114), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129a9) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f27 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 91), (1, 104), (2, 92), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 113), (11, 82), (12, 12), (13, 13), (14, 62), (15, 116), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129ad) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f28 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 118), (1, 104), (2, 92), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 113), (11, 82), (12, 12), (13, 13), (14, 62), (15, 116), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129b0) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f29 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 118), (1, 104), (2, 120), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 113), (11, 82), (12, 12), (13, 13), (14, 62), (15, 116), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129b5) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f30 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 123) f30 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 124) (ρ' := [(0, 122), (1, 104), (2, 123), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 113), (11, 82), (12, 12), (13, 13), (14, 62), (15, 116), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129b8) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f31 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 122), (1, 104), (2, 123), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 113), (11, 82), (12, 12), (13, 13), (14, 125), (15, 116), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129bb) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f32 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 122), (1, 104), (2, 123), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 113), (11, 82), (12, 12), (13, 127), (14, 125), (15, 116), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129be) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f33 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 130) f33 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 131) (ρ' := [(0, 122), (1, 104), (2, 123), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 113), (11, 82), (12, 12), (13, 129), (14, 125), (15, 116), (16, 130), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129c1) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f34 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 122), (1, 104), (2, 123), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 113), (11, 82), (12, 12), (13, 129), (14, 132), (15, 116), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129c5) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f35 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 122), (1, 104), (2, 123), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 113), (11, 82), (12, 134), (13, 129), (14, 132), (15, 116), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129c9) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f36 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 136), (1, 104), (2, 123), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 113), (11, 82), (12, 134), (13, 129), (14, 132), (15, 116), (22, 22), (39, 39), (51, 51)]) (p' := 0x1129cc) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 138) (by decide) rfl

theorem rest_l118420 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112940 bytes_l118420) (entryMap (live .l118420))
      37 0x112940 bytes_l118420 b_l118420 := by
  have f0 : InstrSpec 0x112940 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x112940) (movR64R64Effect 0x112940 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112940 0 13).toInstrSpec (mov_r64_r64_effect_step 0x112940 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x112943 [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x112943) (mulR64Effect 0x112943 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112943 9).toInstrSpec (mul_r64_effect_step 0x112943 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112946 [0x48, 0x89, 0xC5] (fun s => s.RIP = 0x112946) (movR64R64Effect 0x112946 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x112946 5 0).toInstrSpec (mov_r64_r64_effect_step 0x112946 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x112949 [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x112949) (movR64R64Effect 0x112949 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x112949 9 2).toInstrSpec (mov_r64_r64_effect_step 0x112949 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11294c [0x49, 0x83, 0xE6, 0xFE] (fun s => s.RIP = 0x11294c) (andR64Imm8Effect 0x11294c 14 0xfe)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x11294c 14 0xfe).toInstrSpec (and_r64_imm8_effect_step 0x11294c 0x49 0xe6 0xfe (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112950 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x112950) (movR64R64Effect 0x112950 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112950 0 13).toInstrSpec (mov_r64_r64_effect_step 0x112950 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112953 [0x48, 0xB9, 0x21, 0x6C, 0x1A, 0xDF, 0x52, 0x05, 0x19, 0x43] (fun s => s.RIP = 0x112953) (movR64Imm64Effect 0x112953 1 0x43190552df1a6c21)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x112953 1 0x43190552df1a6c21).toInstrSpec (mov_r64_imm64_effect_step 0x112953 0x48 0xb9 (by decide) (by decide) 0x43190552df1a6c21) pre_rip
  have f7 : InstrSpec 0x11295d [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x11295d) (mulR64Effect 0x11295d 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11295d 1).toInstrSpec (mul_r64_effect_step 0x11295d 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x112960 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x112960) (movR64R64Effect 0x112960 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x112960 6 2).toInstrSpec (mov_r64_r64_effect_step 0x112960 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112963 [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x112963) (movR64R64Effect 0x112963 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x112963 11 0).toInstrSpec (mov_r64_r64_effect_step 0x112963 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x112966 [0x4D, 0x01, 0xFB] (fun s => s.RIP = 0x112966) (addR64R64Effect 0x112966 11 15)
      [.gpr 11, .gpr 15] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112966 11 15).toInstrSpec (add_r64_r64_effect_step 0x112966 0x4d 0xfb (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x112969 [0x48, 0x83, 0xD6, 0x00] (fun s => s.RIP = 0x112969) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112969 6 0x0))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112969 6 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112969 0x48 0xd6 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f12 : InstrSpec 0x11296d [0x4C, 0x01, 0xF5] (fun s => s.RIP = 0x11296d) (addR64R64Effect 0x11296d 5 14)
      [.gpr 5, .gpr 14] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11296d 5 14).toInstrSpec (add_r64_r64_effect_step 0x11296d 0x4c 0xf5 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x112970 [0x4D, 0x11, 0xCB] (fun s => s.RIP = 0x112970) (atFlags StatusFlags.CF (adcR64R64Effect 0x112970 11 9))
      [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112970 11 9).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112970 0x4d 0xcb c (by decide) (by decide))) pre_rip
  have f14 : InstrSpec 0x112973 [0x48, 0x83, 0xD6, 0x00] (fun s => s.RIP = 0x112973) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112973 6 0x0))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112973 6 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112973 0x48 0xd6 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f15 : InstrSpec 0x112977 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x112977) (movR64R64Effect 0x112977 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112977 0 13).toInstrSpec (mov_r64_r64_effect_step 0x112977 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11297a [0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x11297a) (movR64Imm64Effect 0x11297a 1 0xfffffffeffffffff)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x11297a 1 0xfffffffeffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x11297a 0x48 0xb9 (by decide) (by decide) 0xfffffffeffffffff) pre_rip
  have f17 : InstrSpec 0x112984 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x112984) (mulR64Effect 0x112984 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x112984 1).toInstrSpec (mul_r64_effect_step 0x112984 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x112987 [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x112987) (movR64R64Effect 0x112987 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x112987 15 2).toInstrSpec (mov_r64_r64_effect_step 0x112987 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11298a [0x4D, 0x01, 0xE2] (fun s => s.RIP = 0x11298a) (addR64R64Effect 0x11298a 10 12)
      [.gpr 10, .gpr 12] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11298a 10 12).toInstrSpec (add_r64_r64_effect_step 0x11298a 0x4d 0xe2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112943) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 55), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112946) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (2, 56), (3, 3), (4, 4), (5, 58), (7, 7), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112949) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (2, 56), (3, 3), (4, 4), (5, 58), (7, 7), (8, 8), (9, 60), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11294c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (2, 56), (3, 3), (4, 4), (5, 58), (7, 7), (8, 8), (9, 60), (10, 10), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112950) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (2, 56), (3, 3), (4, 4), (5, 58), (7, 7), (8, 8), (9, 60), (10, 10), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112953) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 66), (2, 56), (3, 3), (4, 4), (5, 58), (7, 7), (8, 8), (9, 60), (10, 10), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11295d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 66), (2, 69), (3, 3), (4, 4), (5, 58), (7, 7), (8, 8), (9, 60), (10, 10), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112960) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 68), (1, 66), (2, 69), (3, 3), (4, 4), (5, 58), (6, 71), (7, 7), (8, 8), (9, 60), (10, 10), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112963) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f9 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 68), (1, 66), (2, 69), (3, 3), (4, 4), (5, 58), (6, 71), (7, 7), (8, 8), (9, 60), (10, 10), (11, 73), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112966) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f10 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 77) (ρ' := [(0, 68), (1, 66), (2, 69), (3, 3), (4, 4), (5, 58), (6, 71), (7, 7), (8, 8), (9, 60), (10, 10), (11, 75), (12, 12), (13, 13), (14, 62), (15, 15), (16, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x112969) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 68), (1, 66), (2, 69), (3, 3), (4, 4), (5, 58), (6, 78), (7, 7), (8, 8), (9, 60), (10, 10), (11, 75), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11296d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f12 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 68), (1, 66), (2, 69), (3, 3), (4, 4), (6, 78), (7, 7), (8, 8), (9, 60), (10, 10), (11, 75), (12, 12), (13, 13), (14, 62), (15, 15), (16, 80), (22, 22), (39, 39), (51, 51)]) (p' := 0x112970) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f13 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 83) f13 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x112970 11 9 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 68), (1, 66), (2, 69), (3, 3), (4, 4), (6, 78), (7, 7), (8, 8), (9, 60), (10, 10), (11, 82), (12, 12), (13, 13), (14, 62), (15, 15), (16, 83), (22, 22), (39, 39), (51, 51)]) (p' := 0x112973) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 68), (1, 66), (2, 69), (3, 3), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 10), (11, 82), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112977) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 66), (2, 69), (3, 3), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 10), (11, 82), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11297a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 87), (1, 89), (2, 69), (3, 3), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 10), (11, 82), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112984) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 92) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 93) (ρ' := [(0, 91), (1, 89), (2, 92), (3, 3), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 10), (11, 82), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112987) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f18 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 91), (1, 89), (2, 92), (3, 3), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 10), (11, 82), (12, 12), (13, 13), (14, 62), (15, 94), (22, 22), (39, 39), (51, 51)]) (p' := 0x11298a) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 97) f19 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 98) (ρ' := [(0, 91), (1, 89), (2, 92), (3, 3), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 96), (11, 82), (12, 12), (13, 13), (14, 62), (15, 94), (16, 97), (22, 22), (39, 39), (51, 51)]) (p' := 0x11298d) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l118420_1 code

theorem block_l118420 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l118420 :=
  Rest.liftedBlock (rest_l118420 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l118420 x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
