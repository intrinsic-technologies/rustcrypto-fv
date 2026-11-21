import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11734e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11186e bytes_l11734e) (entryMap (live .l11734e))
      16 0x11186e bytes_l11734e b_l11734e := by
  have f0 : InstrSpec 0x11186e [0x48, 0x8D, 0x54, 0x24, 0x10] (fun s => s.RIP = 0x11186e) (leaR64Effect 0x11186e 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x11186e 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x11186e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x111873 [0x48, 0x89, 0x6C, 0x24, 0x48] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111873 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x111873 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111873 5 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111873 5 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111873 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f2 : InstrSpec 0x111878 [0x48, 0x89, 0xEB] (fun s => s.RIP = 0x111878) (movR64R64Effect 0x111878 3 5)
      [.gpr 5] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x111878 3 5).toInstrSpec (mov_r64_r64_effect_step 0x111878 0x48 0xeb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11187b [0x48, 0xF7, 0xDB] (fun s => s.RIP = 0x11187b) (negR64Effect 0x11187b 3)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (negR64Effect_footprint 0x11187b 3).toInstrSpec (neg_r64_effect_step 0x11187b 0x48 0xdb (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11187e [0x41, 0xB8, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11187e) (movR32Imm32Effect 0x11187e 6 8 0x0)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x11187e 6 8 0x0).toInstrSpec (mov_r32_imm32_rex_effect_step 0x11187e 0x41 0xb8 (by decide) (by decide) 0x0) pre_rip
  have f5 : InstrSpec 0x111884 [0x4D, 0x19, 0xE0] (fun s => s.RIP = 0x111884) (atFlags StatusFlags.CF (sbbR64R64Effect 0x111884 8 12))
      [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x111884 8 12).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x111884 0x4d 0xe0 c (by decide) (by decide))) pre_rip
  have f6 : InstrSpec 0x111887 [0xBD, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x111887) (movR32Imm32Effect 0x111887 5 5 0x0)
      [] [] [.reg 5, .rip] :=
    (movR32Imm32Effect_footprint 0x111887 5 5 0x0).toInstrSpec (mov_r32_imm32_effect_step 0x111887 0xbd (by decide) 0x0) pre_rip
  have f7 : InstrSpec 0x11188c [0x4C, 0x19, 0xDD] (fun s => s.RIP = 0x11188c) (atFlags StatusFlags.CF (sbbR64R64Effect 0x11188c 5 11))
      [.gpr 5, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x11188c 5 11).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x11188c 0x4c 0xdd c (by decide) (by decide))) pre_rip
  have f8 : InstrSpec 0x11188f [0x4D, 0x19, 0xEA] (fun s => s.RIP = 0x11188f) (atFlags StatusFlags.CF (sbbR64R64Effect 0x11188f 10 13))
      [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x11188f 10 13).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x11188f 0x4d 0xea c (by decide) (by decide))) pre_rip
  have f9 : InstrSpec 0x111892 [0x48, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x111892 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111892 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111892 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x111892 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x111892 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x111897 [0x0F, 0x93, 0x44, 0x24, 0x10] (StorePre 0x111897 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111897 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 3) (setccM8Effect 0x111897 5 (.sib 4 none 0 (.d8 0x10))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.rip] :=
    (setccM8Effect_footprint 0x111897 5 (.sib 4 none 0 (.d8 0x10)) 3).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x111897 3 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x11189c [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x11189c) (testR64R64Effect 0x11189c 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x11189c 2 2).toInstrSpec (test_r64_r64_effect_step 0x11189c 0x48 0xd2 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11189f [0x48, 0x8D, 0x54, 0x24, 0x10] (fun s => s.RIP = 0x11189f) (leaR64Effect 0x11189f 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x11189f 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x11189f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1118a4 [0x0F, 0xB6, 0x74, 0x24, 0x10] (LoadPre 0x1118a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118a4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1118a4 5 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1118a4 5 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x1118a4 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1118a9 [0x0F, 0x95, 0x44, 0x24, 0x10] (StorePre 0x1118a9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118a9 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x1118a9 5 (.sib 4 none 0 (.d8 0x10))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x1118a9 5 (.sib 4 none 0 (.d8 0x10)) 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x1118a9 5 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1118ae [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x1118ae) (leaR64Effect 0x1118ae 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1118ae 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1118ae 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x111873) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x111878) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 55), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x11187b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (3, 57), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (16, 58), (22, 22), (39, 39), (51, 51)]) (p' := 0x11187e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (3, 57), (4, 4), (5, 5), (8, 60), (10, 10), (11, 11), (12, 12), (13, 13), (16, 58), (22, 22), (39, 39), (51, 51)]) (p' := 0x111884) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 63) f5 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x111884 8 12 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (3, 57), (4, 4), (5, 5), (8, 62), (10, 10), (11, 11), (12, 12), (13, 13), (16, 63), (22, 22), (39, 39), (51, 51)]) (p' := 0x111887) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (3, 57), (4, 4), (5, 65), (8, 62), (10, 10), (11, 11), (12, 12), (13, 13), (16, 63), (22, 22), (39, 39), (51, 51)]) (p' := 0x11188c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 68) f7 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x11188c 5 11 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (3, 57), (4, 4), (5, 67), (8, 62), (10, 10), (11, 11), (12, 12), (13, 13), (16, 68), (22, 22), (39, 39), (51, 51)]) (p' := 0x11188f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f8 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 71) f8 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x11188f 10 13 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (3, 57), (4, 4), (5, 67), (8, 62), (10, 70), (11, 11), (12, 12), (13, 13), (16, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x111892) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 73), (3, 57), (4, 4), (5, 67), (8, 62), (10, 70), (11, 11), (12, 12), (13, 13), (16, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x111897) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 73), (3, 57), (4, 4), (5, 67), (8, 62), (10, 70), (11, 11), (12, 12), (13, 13), (16, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x11189c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 73), (3, 57), (4, 4), (5, 67), (8, 62), (10, 70), (11, 11), (12, 12), (13, 13), (19, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x11189f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (3, 57), (4, 4), (5, 67), (8, 62), (10, 70), (11, 11), (12, 12), (13, 13), (19, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118a4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (3, 57), (4, 4), (5, 67), (6, 79), (8, 62), (10, 70), (11, 11), (12, 12), (13, 13), (19, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118a9) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (3, 57), (4, 4), (5, 67), (6, 79), (8, 62), (10, 70), (11, 11), (12, 12), (13, 13), (19, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118ae) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (3, 57), (4, 4), (5, 67), (6, 79), (8, 62), (10, 70), (11, 11), (12, 12), (13, 13), (19, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x1118b3) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 83) (by decide) rfl

theorem block_l11734e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11734e :=
  Rest.liftedBlock (rest_l11734e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11734e x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
