import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l116de3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111303 bytes_l116de3) (entryMap (live .l116de3))
      10 0x111303 bytes_l116de3 b_l116de3 := by
  have f0 : InstrSpec 0x111303 [0x4C, 0x03, 0x7C, 0x24, 0x10] (LoadPre 0x111303 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111303 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x111303 15 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 15, .gpr 4] [] [.reg 15, .flags, .rip] :=
    (addR64M64Effect_footprint 0x111303 15 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (add_r64_m64_effect_step 0x111303 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x111308 [0x4C, 0x13, 0x74, 0x24, 0x08] (LoadPre 0x111308 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111308 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111308 14 (.sib 4 none 0 (.d8 0x8))))
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x111308 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x111308 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11130d [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x11130d) (movR64R64Effect 0x11130d 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11130d 6 14).toInstrSpec (mov_r64_r64_effect_step 0x11130d 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x111310 [0x4C, 0x89, 0x74, 0x24, 0x30] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111310 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x111310 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111310 14 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111310 14 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111310 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f4 : InstrSpec 0x111315 [0x48, 0x11, 0xE8] (fun s => s.RIP = 0x111315) (atFlags StatusFlags.CF (adcR64R64Effect 0x111315 0 5))
      [.gpr 0, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x111315 0 5).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x111315 0x48 0xe8 c (by decide) (by decide))) pre_rip
  have f5 : InstrSpec 0x111318 [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x111318) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111318 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x111318 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x111318 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f6 : InstrSpec 0x11131c [0x48, 0x89, 0x54, 0x24, 0x08] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11131c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11131c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11131c 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11131c 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x11131c 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f7 : InstrSpec 0x111321 [0x48, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x111321 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111321 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111321 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x111321 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x111321 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x111326 [0x41, 0x32, 0x53, 0x20] (LoadPre 0x111326 (fun s => AddrMode.addr (.base 11 (.d8 0x20)) s (0x111326 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x111326 4 2 (.base 11 (.d8 0x20)))
      [.gpr 2, .gpr 11] [] [.reg 2, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x111326 4 2 (.base 11 (.d8 0x20))).toInstrSpec (xor_r8_m8_rex_effect_step 0x111326 0x41 (by decide) 2 (.base 11 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x11132a [0x48, 0x89, 0x54, 0x24, 0x18] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11132a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11132a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11132a 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11132a 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x11132a 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 53), (16, 54), (22, 22), (39, 39), (51, 51)]) (p' := 0x111308) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 57) f1 .CF (fun _ => rfl) (adcR64M64Effect_fresh 0x111308 14 (.sib 4 none 0 (.d8 0x8)) _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 56), (15, 53), (16, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x11130d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 56), (15, 53), (16, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x111310) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 56), (15, 53), (16, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x111315) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 63) f4 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x111315 0 5 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 56), (15, 53), (16, 63), (22, 22), (39, 39), (51, 51)]) (p' := 0x111318) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (1, 1), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 56), (15, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x11131c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 1), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 56), (15, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111321) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 62), (1, 1), (2, 68), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 56), (15, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x111326) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 62), (1, 1), (2, 70), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 56), (15, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x11132a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 62), (1, 1), (2, 70), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 56), (15, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x11132f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 73) (by decide) rfl

theorem block_l116de3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l116de3 :=
  Rest.liftedBlock (rest_l116de3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l116de3 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
