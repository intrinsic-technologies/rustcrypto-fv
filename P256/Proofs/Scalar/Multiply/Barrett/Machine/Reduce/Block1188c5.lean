import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1188c5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112de5 bytes_l1188c5) (entryMap (live .l1188c5))
      9 0x112de5 bytes_l1188c5 b_l1188c5 := by
  have f0 : InstrSpec 0x112de5 [0x4D, 0x01, 0xC7] (fun s => s.RIP = 0x112de5) (addR64R64Effect 0x112de5 15 8)
      [.gpr 15, .gpr 8] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112de5 15 8).toInstrSpec (add_r64_r64_effect_step 0x112de5 0x4d 0xc7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x112de8 [0x49, 0x11, 0xC3] (fun s => s.RIP = 0x112de8) (atFlags StatusFlags.CF (adcR64R64Effect 0x112de8 11 0))
      [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112de8 11 0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112de8 0x49 0xc3 c (by decide) (by decide))) pre_rip
  have f2 : InstrSpec 0x112deb [0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x112deb) (atFlags (condHolds 2) (setccR8Effect 0x112deb 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x112deb 3 0 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x112deb 2 0xc0 (by decide) (by decide) c)) pre_rip
  have f3 : InstrSpec 0x112dee [0x49, 0x83, 0xD1, 0x00] (fun s => s.RIP = 0x112dee) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112dee 9 0x0))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 9, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x112dee 9 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x112dee 0x49 0xd1 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f4 : InstrSpec 0x112df2 [0x49, 0xB8, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x112df2) (movR64Imm64Effect 0x112df2 8 0xffffffff00000000)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x112df2 8 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x112df2 0x49 0xb8 (by decide) (by decide) 0xffffffff00000000) pre_rip
  have f5 : InstrSpec 0x112dfc [0x49, 0x21, 0xC8] (fun s => s.RIP = 0x112dfc) (andR64R64Effect 0x112dfc 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112dfc 8 1).toInstrSpec (and_r64_r64_effect_step 0x112dfc 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112dff [0x04, 0xFF] (fun s => s.RIP = 0x112dff) (addAlImm8Effect 0x112dff 0xff)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addAlImm8Effect_footprint 0x112dff 0xff).toInstrSpec (add_al_imm8_effect_step 0x112dff 0xff) pre_rip
  have f7 : InstrSpec 0x112e01 [0x48, 0x11, 0xD1] (fun s => s.RIP = 0x112e01) (atFlags StatusFlags.CF (adcR64R64Effect 0x112e01 1 2))
      [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112e01 1 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112e01 0x48 0xd1 c (by decide) (by decide))) pre_rip
  have f8 : InstrSpec 0x112e04 [0x49, 0x11, 0xF0] (fun s => s.RIP = 0x112e04) (atFlags StatusFlags.CF (adcR64R64Effect 0x112e04 8 6))
      [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112e04 8 6).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112e04 0x49 0xf0 c (by decide) (by decide))) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (15, 53), (16, 54), (22, 22), (39, 39), (51, 51)]) (p' := 0x112de8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 57) f1 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x112de8 11 0 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 56), (15, 53), (16, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x112deb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 56), (15, 53), (16, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x112dee) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 61), (11, 56), (15, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x112df2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 63), (9, 61), (11, 56), (15, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x112dfc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 65), (9, 61), (11, 56), (15, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x112dff) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f6 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 67), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 65), (9, 61), (11, 56), (15, 53), (16, 68), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e01) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.fresh (n := 70) f7 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x112e01 1 2 _ (.head _)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 67), (2, 2), (4, 4), (6, 6), (7, 7), (8, 65), (9, 61), (11, 56), (15, 53), (16, 70), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e04) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 67), (2, 2), (4, 4), (6, 6), (7, 7), (8, 72), (9, 61), (11, 56), (15, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e07) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 74) (by decide) rfl

theorem block_l1188c5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1188c5 :=
  Rest.liftedBlock (rest_l1188c5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1188c5 x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
