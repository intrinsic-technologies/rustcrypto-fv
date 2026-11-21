import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117393 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1118b3 bytes_l117393) (entryMap (live .l117393))
      12 0x1118b3 bytes_l117393 b_l117393 := by
  have f0 : InstrSpec 0x1118b3 [0x0F, 0xB6, 0x54, 0x24, 0x10] (LoadPre 0x1118b3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118b3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1118b3 5 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1118b3 5 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x1118b3 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1118b8 [0x0F, 0x95, 0x44, 0x24, 0x10] (StorePre 0x1118b8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118b8 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x1118b8 5 (.sib 4 none 0 (.d8 0x10))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x1118b8 5 (.sib 4 none 0 (.d8 0x10)) 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x1118b8 5 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1118bd [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x10] (LoadPre 0x1118bd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118bd + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1118bd 6 15 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x1118bd 6 15 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1118bd 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1118c3 [0x0F, 0x95, 0x44, 0x24, 0x10] (StorePre 0x1118c3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118c3 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x1118c3 5 (.sib 4 none 0 (.d8 0x10))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x1118c3 5 (.sib 4 none 0 (.d8 0x10)) 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x1118c3 5 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1118c8 [0x44, 0x0F, 0xB6, 0x74, 0x24, 0x10] (LoadPre 0x1118c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118c8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1118c8 6 14 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x1118c8 6 14 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1118c8 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1118ce [0x0F, 0x95, 0x44, 0x24, 0x10] (StorePre 0x1118ce 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118ce + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x1118ce 5 (.sib 4 none 0 (.d8 0x10))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x1118ce 5 (.sib 4 none 0 (.d8 0x10)) 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x1118ce 5 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1118d3 [0x0F, 0xB6, 0x7C, 0x24, 0x10] (LoadPre 0x1118d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118d3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1118d3 5 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1118d3 5 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x1118d3 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1118d8 [0x0F, 0x95, 0x44, 0x24, 0x10] (StorePre 0x1118d8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118d8 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x1118d8 5 (.sib 4 none 0 (.d8 0x10))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x1118d8 5 (.sib 4 none 0 (.d8 0x10)) 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x1118d8 5 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1118dd [0x4C, 0x8D, 0x4C, 0x24, 0x10] (fun s => s.RIP = 0x1118dd) (leaR64Effect 0x1118dd 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x1118dd 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1118dd 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1118e2 [0x41, 0x0F, 0x95, 0xC1] (fun s => s.RIP = 0x1118e2) (atFlags (condHolds 5) (setccR8Effect 0x1118e2 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x1118e2 4 9 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1118e2 5 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f10 : InstrSpec 0x1118e6 [0x83, 0x7C, 0x24, 0x44, 0x40] (LoadPre 0x1118e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x1118e6 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x1118e6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x40)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x1118e6 5 (.sib 4 none 0 (.d8 0x44)) 0x40).toInstrSpec (cmp_m32_imm8_effect_step 0x1118e6 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide) 0x40) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118b8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118bd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (15, 56), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118c3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (15, 56), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118c8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 56), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118ce) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 56), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118d3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 62), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 56), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118d8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 62), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 56), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118dd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 62), (8, 8), (9, 65), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 56), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118e2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 62), (8, 8), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 56), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118e6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 62), (8, 8), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 56), (16, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118eb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel32_effect_step 0x1118eb 3 0x248) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l117393 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117393 :=
  Rest.liftedBlock (rest_l117393 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117393 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
