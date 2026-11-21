import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Correction.l1181e3

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11821e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11273e bytes_l11821e) (entryMap (live .l11821e))
      15 0x11273e bytes_l11821e b_l11821e := by
  have f0 : InstrSpec 0x11273e [0x31, 0xDB] (fun s => s.RIP = 0x11273e) (xorR32R32Effect 0x11273e 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11273e 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x11273e 0xdb (by decide)) pre_rip
  have f1 : InstrSpec 0x112740 [0x48, 0x2B, 0x5C, 0x24, 0x08] (LoadPre 0x112740 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112740 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x112740 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.reg 3, .flags, .rip] :=
    (subR64M64Effect_footprint 0x112740 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x112740 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x112745 [0x4C, 0x8B, 0x79, 0x10] (LoadPre 0x112745 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x112745 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112745 15 (.base 1 (.d8 0x10)))
      [.gpr 1] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x112745 15 (.base 1 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x112745 0x4c (by decide) 7 (.base 1 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x112749 [0x4D, 0x89, 0xFD] (fun s => s.RIP = 0x112749) (movR64R64Effect 0x112749 13 15)
      [.gpr 15] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x112749 13 15).toInstrSpec (mov_r64_r64_effect_step 0x112749 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11274c [0x4D, 0x29, 0xC5] (fun s => s.RIP = 0x11274c) (subR64R64Effect 0x11274c 13 8)
      [.gpr 13, .gpr 8] [] [.reg 13, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11274c 13 8).toInstrSpec (sub_r64_r64_effect_step 0x11274c 0x4d 0xc5 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11274f [0x48, 0xC1, 0xFB, 0x3F] (fun s => s.RIP = 0x11274f) (sarR64Effect 0x11274f 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (sarR64Effect_footprint 0x11274f 4 3 63).toInstrSpec (sar_r64_imm8_effect_step 0x11274f 0x48 0xfb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112753 [0x4C, 0x01, 0xEB] (fun s => s.RIP = 0x112753) (addR64R64Effect 0x112753 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112753 3 13).toInstrSpec (add_r64_r64_effect_step 0x112753 0x4c 0xeb (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x112756 [0x49, 0xF7, 0xD7] (fun s => s.RIP = 0x112756) (notR64Effect 0x112756 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (notR64Effect_footprint 0x112756 15).toInstrSpec (not_r64_effect_step 0x112756 0x49 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x112759 [0x4D, 0x89, 0xC5] (fun s => s.RIP = 0x112759) (movR64R64Effect 0x112759 13 8)
      [.gpr 8] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x112759 13 8).toInstrSpec (mov_r64_r64_effect_step 0x112759 0x4d 0xc5 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11275c [0x4D, 0x21, 0xFD] (fun s => s.RIP = 0x11275c) (andR64R64Effect 0x11275c 13 15)
      [.gpr 13, .gpr 15] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11275c 13 15).toInstrSpec (and_r64_r64_effect_step 0x11275c 0x4d 0xfd (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11275f [0x4D, 0x09, 0xC7] (fun s => s.RIP = 0x11275f) (orR64R64Effect 0x11275f 15 8)
      [.gpr 15, .gpr 8] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11275f 15 8).toInstrSpec (or_r64_r64_effect_step 0x11275f 0x4d 0xc7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x112762 [0x49, 0x21, 0xDF] (fun s => s.RIP = 0x112762) (andR64R64Effect 0x112762 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112762 15 3).toInstrSpec (and_r64_r64_effect_step 0x112762 0x49 0xdf (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x112765 [0x4D, 0x09, 0xEF] (fun s => s.RIP = 0x112765) (orR64R64Effect 0x112765 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x112765 15 13).toInstrSpec (or_r64_r64_effect_step 0x112765 0x4d 0xef (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x112768 [0x49, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x112768) (shrR64Effect 0x112768 4 15 63)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x112768 4 15 63).toInstrSpec (shr_r64_imm8_effect_step 0x112768 0x49 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11276c [0x4C, 0x89, 0x7C, 0x24, 0x08] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11276c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11276c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11276c 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11276c 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x11276c 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x112740) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x112745) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x112749) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 59), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x11274c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 61), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x11274f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 61), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x112753) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 61), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x112756) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 61), (14, 14), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x112759) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 69), (14, 14), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x11275c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 71), (14, 14), (15, 67), (22, 22), (39, 39), (51, 51)]) (p' := 0x11275f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 71), (14, 14), (15, 73), (22, 22), (39, 39), (51, 51)]) (p' := 0x112762) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 71), (14, 14), (15, 75), (22, 22), (39, 39), (51, 51)]) (p' := 0x112765) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 71), (14, 14), (15, 77), (22, 22), (39, 39), (51, 51)]) (p' := 0x112768) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 71), (14, 14), (15, 79), (22, 22), (39, 39), (51, 51)]) (p' := 0x11276c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 71), (14, 14), (15, 79), (22, 22), (39, 39), (51, 51)]) (p' := 0x112771) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 82) (by decide) rfl

theorem block_l11821e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11821e :=
  Rest.liftedBlock (rest_l11821e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11821e x hx)

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine
