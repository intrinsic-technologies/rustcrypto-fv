import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Correction.l1181ad

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1181e3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112703 bytes_l1181e3) (entryMap (live .l1181e3))
      17 0x112703 bytes_l1181e3 b_l1181e3 := by
  have f0 : InstrSpec 0x112703 [0x4C, 0x8D, 0x64, 0x24, 0x08] (fun s => s.RIP = 0x112703) (leaR64Effect 0x112703 12 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x112703 12 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x112703 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x112708 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x112708) (xorR32R32Effect 0x112708 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x112708 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x112708 0x45 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11270b [0x31, 0xF6] (fun s => s.RIP = 0x11270b) (xorR32R32Effect 0x11270b 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11270b 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x11270b 0xf6 (by decide)) pre_rip
  have f3 : InstrSpec 0x11270d [0x48, 0x2B, 0x74, 0x24, 0x08] (LoadPre 0x11270d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11270d + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11270d 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11270d 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x11270d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x112712 [0x48, 0x8B, 0x59, 0x08] (LoadPre 0x112712 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x112712 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112712 3 (.base 1 (.d8 0x8)))
      [.gpr 1] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x112712 3 (.base 1 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x112712 0x48 (by decide) 3 (.base 1 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x112716 [0x49, 0x89, 0xDF] (fun s => s.RIP = 0x112716) (movR64R64Effect 0x112716 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x112716 15 3).toInstrSpec (mov_r64_r64_effect_step 0x112716 0x49 0xdf (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112719 [0x4D, 0x29, 0xCF] (fun s => s.RIP = 0x112719) (subR64R64Effect 0x112719 15 9)
      [.gpr 15, .gpr 9] [] [.reg 15, .flags, .rip] :=
    (subR64R64Effect_footprint 0x112719 15 9).toInstrSpec (sub_r64_r64_effect_step 0x112719 0x4d 0xcf (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11271c [0x48, 0xC1, 0xFE, 0x3F] (fun s => s.RIP = 0x11271c) (sarR64Effect 0x11271c 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (sarR64Effect_footprint 0x11271c 4 6 63).toInstrSpec (sar_r64_imm8_effect_step 0x11271c 0x48 0xfe 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x112720 [0x4C, 0x01, 0xFE] (fun s => s.RIP = 0x112720) (addR64R64Effect 0x112720 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112720 6 15).toInstrSpec (add_r64_r64_effect_step 0x112720 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112723 [0x48, 0xF7, 0xD3] (fun s => s.RIP = 0x112723) (notR64Effect 0x112723 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (notR64Effect_footprint 0x112723 3).toInstrSpec (not_r64_effect_step 0x112723 0x48 0xd3 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x112726 [0x4D, 0x89, 0xCF] (fun s => s.RIP = 0x112726) (movR64R64Effect 0x112726 15 9)
      [.gpr 9] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x112726 15 9).toInstrSpec (mov_r64_r64_effect_step 0x112726 0x4d 0xcf (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x112729 [0x49, 0x21, 0xDF] (fun s => s.RIP = 0x112729) (andR64R64Effect 0x112729 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112729 15 3).toInstrSpec (and_r64_r64_effect_step 0x112729 0x49 0xdf (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11272c [0x4C, 0x09, 0xCB] (fun s => s.RIP = 0x11272c) (orR64R64Effect 0x11272c 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11272c 3 9).toInstrSpec (or_r64_r64_effect_step 0x11272c 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11272f [0x48, 0x21, 0xF3] (fun s => s.RIP = 0x11272f) (andR64R64Effect 0x11272f 3 6)
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11272f 3 6).toInstrSpec (and_r64_r64_effect_step 0x11272f 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x112732 [0x4C, 0x09, 0xFB] (fun s => s.RIP = 0x112732) (orR64R64Effect 0x112732 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x112732 3 15).toInstrSpec (or_r64_r64_effect_step 0x112732 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x112735 [0x48, 0xC1, 0xEB, 0x3F] (fun s => s.RIP = 0x112735) (shrR64Effect 0x112735 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x112735 4 3 63).toInstrSpec (shr_r64_imm8_effect_step 0x112735 0x48 0xeb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x112739 [0x48, 0x89, 0x5C, 0x24, 0x08] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112739 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112739 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112739 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112739 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112739 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x112708) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (22, 22), (39, 39), (51, 51)]) (p' := 0x11270b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 56), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (22, 22), (39, 39), (51, 51)]) (p' := 0x11270d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (22, 22), (39, 39), (51, 51)]) (p' := 0x112712) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (22, 22), (39, 39), (51, 51)]) (p' := 0x112716) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (15, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x112719) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (15, 64), (22, 22), (39, 39), (51, 51)]) (p' := 0x11271c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (15, 64), (22, 22), (39, 39), (51, 51)]) (p' := 0x112720) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (15, 64), (22, 22), (39, 39), (51, 51)]) (p' := 0x112723) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 70), (4, 4), (5, 5), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (15, 64), (22, 22), (39, 39), (51, 51)]) (p' := 0x112726) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 70), (4, 4), (5, 5), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (15, 72), (22, 22), (39, 39), (51, 51)]) (p' := 0x112729) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 70), (4, 4), (5, 5), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (15, 74), (22, 22), (39, 39), (51, 51)]) (p' := 0x11272c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 76), (4, 4), (5, 5), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (15, 74), (22, 22), (39, 39), (51, 51)]) (p' := 0x11272f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 78), (4, 4), (5, 5), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (15, 74), (22, 22), (39, 39), (51, 51)]) (p' := 0x112732) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 80), (4, 4), (5, 5), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (15, 74), (22, 22), (39, 39), (51, 51)]) (p' := 0x112735) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 82), (4, 4), (5, 5), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (15, 74), (22, 22), (39, 39), (51, 51)]) (p' := 0x112739) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 82), (4, 4), (5, 5), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (15, 74), (22, 22), (39, 39), (51, 51)]) (p' := 0x11273e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 85) (by decide) rfl

theorem block_l1181e3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1181e3 :=
  Rest.liftedBlock (rest_l1181e3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1181e3 x hx)

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine
