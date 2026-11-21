import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117244 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111764 bytes_l117244) (entryMap (live .l117244))
      5 0x111764 bytes_l117244 b_l117244 := by
  have f0 : InstrSpec 0x111764 [0x4D, 0x01, 0xFB] (fun s => s.RIP = 0x111764) (addR64R64Effect 0x111764 11 15)
      [.gpr 11, .gpr 15] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x111764 11 15).toInstrSpec (add_r64_r64_effect_step 0x111764 0x4d 0xfb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x111767 [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x111767 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x111767 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111767 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x111767 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x111767 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11176c [0x4D, 0x11, 0xE2] (fun s => s.RIP = 0x11176c) (atFlags StatusFlags.CF (adcR64R64Effect 0x11176c 10 12))
      [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11176c 10 12).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11176c 0x4d 0xe2 c (by decide) (by decide))) pre_rip
  have f3 : InstrSpec 0x11176f [0x4C, 0x11, 0xE8] (fun s => s.RIP = 0x11176f) (atFlags StatusFlags.CF (adcR64R64Effect 0x11176f 0 13))
      [.gpr 0, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11176f 0 13).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11176f 0x4c 0xe8 c (by decide) (by decide))) pre_rip
  have f4 : InstrSpec 0x111772 [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x111772) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111772 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x111772 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x111772 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 54), (22, 22), (39, 39), (51, 51)]) (p' := 0x111767) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 56), (8, 8), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 54), (22, 22), (39, 39), (51, 51)]) (p' := 0x11176c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 59) f2 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11176c 10 12 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 56), (8, 8), (10, 58), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (51, 51)]) (p' := 0x11176f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 62) f3 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11176f 0 13 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 56), (8, 8), (10, 58), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111772) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 1), (2, 64), (3, 3), (4, 4), (6, 6), (7, 56), (8, 8), (10, 58), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111776) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 66) (by decide) rfl

theorem block_l117244 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117244 :=
  Rest.liftedBlock (rest_l117244 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117244 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
