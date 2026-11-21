import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11754e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111a6e bytes_l11754e) (entryMap (live .l11754e))
      17 0x111a6e bytes_l11754e b_l11754e := by
  have f0 : InstrSpec 0x111a6e [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x111a6e) (xorR32R32Effect 0x111a6e 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x111a6e 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x111a6e 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x111a71 [0x89, 0xE9] (fun s => s.RIP = 0x111a71) (movR32R32Effect 0x111a71 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x111a71 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x111a71 0xe9 (by decide)) pre_rip
  have f2 : InstrSpec 0x111a73 [0x49, 0xD3, 0xED] (fun s => s.RIP = 0x111a73) (shrR64ClEffect 0x111a73 3 13)
      [.gpr 13, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x111a73 3 13).toInstrSpec (shr_r64_cl_effect_step 0x111a73 0x49 0xed (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x111a76 [0x4C, 0x2B, 0x44, 0x24, 0x10] (LoadPre 0x111a76 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111a76 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x111a76 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 8, .gpr 4] [] [.reg 8, .flags, .rip] :=
    (subR64M64Effect_footprint 0x111a76 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x111a76 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x111a7b [0x0F, 0xB6, 0x6C, 0x24, 0x0F] (LoadPre 0x111a7b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x111a7b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111a7b 5 5 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x111a7b 5 5 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x111a7b 5 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x111a80 [0x40, 0x32, 0x6C, 0x24, 0x0E] (LoadPre 0x111a80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x111a80 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x111a80 5 5 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 5, .gpr 4] [] [.reg 5, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x111a80 5 5 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (xor_r8_m8_rex_effect_step 0x111a80 0x40 (by decide) 5 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x111a85 [0x4D, 0x85, 0xED] (fun s => s.RIP = 0x111a85) (testR64R64Effect 0x111a85 13 13)
      [.gpr 13, .gpr 13] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x111a85 13 13).toInstrSpec (test_r64_r64_effect_step 0x111a85 0x4d 0xed (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111a88 [0x0F, 0x94, 0xC1] (fun s => s.RIP = 0x111a88) (atFlags (condHolds 4) (setccR8Effect 0x111a88 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x111a88 3 1 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x111a88 4 0xc1 (by decide) (by decide) c)) pre_rip
  have f8 : InstrSpec 0x111a8b [0x44, 0x20, 0xC1] (fun s => s.RIP = 0x111a8b) (andR8R8Effect 0x111a8b 3 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (andR8R8Effect_footprint 0x111a8b 3 1 8).toInstrSpec (and_r8_r8_rex_effect_step 0x111a8b 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x111a8e [0x88, 0x4C, 0x24, 0x10] (StorePre 0x111a8e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111a8e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111a8e 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111a8e 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x111a8e 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x111a92 [0x4C, 0x8D, 0x54, 0x24, 0x10] (fun s => s.RIP = 0x111a92) (leaR64Effect 0x111a92 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x111a92 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x111a92 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x111a97 [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x10] (LoadPre 0x111a97 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111a97 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x111a97 6 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x111a97 6 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x111a97 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x111a9d [0x49, 0xFF, 0xCA] (fun s => s.RIP = 0x111a9d) (decR64Effect 0x111a9d 10)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (decR64Effect_footprint 0x111a9d 10).toInstrSpec (dec_r64_effect_step 0x111a9d 0x49 0xca (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111aa0 [0x4D, 0x21, 0xC2] (fun s => s.RIP = 0x111aa0) (andR64R64Effect 0x111aa0 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111aa0 10 8).toInstrSpec (and_r64_r64_effect_step 0x111aa0 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x111aa3 [0x49, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x111aa3) (sarR64Effect 0x111aa3 4 10 63)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (sarR64Effect_footprint 0x111aa3 4 10 63).toInstrSpec (sar_r64_imm8_effect_step 0x111aa3 0x49 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x111aa7 [0x4D, 0x01, 0xEA] (fun s => s.RIP = 0x111aa7) (addR64R64Effect 0x111aa7 10 13)
      [.gpr 10, .gpr 13] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x111aa7 10 13).toInstrSpec (add_r64_r64_effect_step 0x111aa7 0x4d 0xea (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x111aaa [0x49, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x111aaa) (shrR64Effect 0x111aaa 4 10 63)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x111aaa 4 10 63).toInstrSpec (shr_r64_imm8_effect_step 0x111aaa 0x49 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a71) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a73) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (12, 12), (13, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a76) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (11, 11), (12, 12), (13, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a7b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 7), (8, 59), (9, 9), (11, 11), (12, 12), (13, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a80) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 59), (9, 9), (11, 11), (12, 12), (13, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a85) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 59), (9, 9), (11, 11), (12, 12), (13, 57), (19, 65), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a88) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 59), (9, 9), (11, 11), (12, 12), (13, 57), (19, 65), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a8b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 59), (9, 9), (11, 11), (12, 12), (13, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a8e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 69), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 59), (9, 9), (11, 11), (12, 12), (13, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a92) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 69), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 59), (9, 9), (11, 11), (12, 12), (13, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a97) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 69), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 59), (9, 9), (10, 73), (11, 11), (12, 12), (13, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a9d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 69), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 59), (9, 9), (10, 75), (11, 11), (12, 12), (13, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x111aa0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 69), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 59), (9, 9), (10, 77), (11, 11), (12, 12), (13, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x111aa3) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 69), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 59), (9, 9), (10, 79), (11, 11), (12, 12), (13, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x111aa7) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 69), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 59), (9, 9), (10, 81), (11, 11), (12, 12), (13, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x111aaa) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 69), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 59), (9, 9), (10, 83), (11, 11), (12, 12), (13, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x111aae) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 85) (by decide) rfl

theorem block_l11754e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11754e :=
  Rest.liftedBlock (rest_l11754e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11754e x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
