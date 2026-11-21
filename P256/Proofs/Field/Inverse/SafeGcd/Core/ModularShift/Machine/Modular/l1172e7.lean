import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1172e7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111807 bytes_l1172e7) (entryMap (live .l1172e7))
      15 0x111807 bytes_l1172e7 b_l1172e7 := by
  have f0 : InstrSpec 0x111807 [0x48, 0x89, 0x5C, 0x24, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111807 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111807 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111807 3 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111807 3 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111807 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11180c [0x45, 0x31, 0xED] (fun s => s.RIP = 0x11180c) (xorR32R32Effect 0x11180c 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11180c 3 13 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x11180c 0x45 0xed (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11180f [0x4C, 0x2B, 0x6C, 0x24, 0x10] (LoadPre 0x11180f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11180f + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11180f 13 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 13, .gpr 4] [] [.reg 13, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11180f 13 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x11180f 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x111814 [0x49, 0x89, 0xF8] (fun s => s.RIP = 0x111814) (movR64R64Effect 0x111814 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x111814 8 7).toInstrSpec (mov_r64_r64_effect_step 0x111814 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x111817 [0x49, 0x29, 0xC0] (fun s => s.RIP = 0x111817) (subR64R64Effect 0x111817 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x111817 8 0).toInstrSpec (sub_r64_r64_effect_step 0x111817 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11181a [0x49, 0xC1, 0xFD, 0x3F] (fun s => s.RIP = 0x11181a) (sarR64Effect 0x11181a 4 13 63)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (sarR64Effect_footprint 0x11181a 4 13 63).toInstrSpec (sar_r64_imm8_effect_step 0x11181a 0x49 0xfd 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11181e [0x4D, 0x01, 0xC5] (fun s => s.RIP = 0x11181e) (addR64R64Effect 0x11181e 13 8)
      [.gpr 13, .gpr 8] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11181e 13 8).toInstrSpec (add_r64_r64_effect_step 0x11181e 0x4d 0xc5 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111821 [0x48, 0xF7, 0xD7] (fun s => s.RIP = 0x111821) (notR64Effect 0x111821 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (notR64Effect_footprint 0x111821 7).toInstrSpec (not_r64_effect_step 0x111821 0x48 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111824 [0x49, 0x89, 0xC0] (fun s => s.RIP = 0x111824) (movR64R64Effect 0x111824 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x111824 8 0).toInstrSpec (mov_r64_r64_effect_step 0x111824 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x111827 [0x49, 0x21, 0xF8] (fun s => s.RIP = 0x111827) (andR64R64Effect 0x111827 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111827 8 7).toInstrSpec (and_r64_r64_effect_step 0x111827 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11182a [0x48, 0x09, 0xC7] (fun s => s.RIP = 0x11182a) (orR64R64Effect 0x11182a 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11182a 7 0).toInstrSpec (or_r64_r64_effect_step 0x11182a 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11182d [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x11182d) (xorR32R32Effect 0x11182d 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11182d 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x11182d 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x111830 [0x4C, 0x21, 0xEF] (fun s => s.RIP = 0x111830) (andR64R64Effect 0x111830 7 13)
      [.gpr 7, .gpr 13] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111830 7 13).toInstrSpec (and_r64_r64_effect_step 0x111830 0x4c 0xef (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111833 [0x4C, 0x09, 0xC7] (fun s => s.RIP = 0x111833) (orR64R64Effect 0x111833 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111833 7 8).toInstrSpec (or_r64_r64_effect_step 0x111833 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x111836 [0x48, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x111836) (shrR64Effect 0x111836 4 7 63)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x111836 4 7 63).toInstrSpec (shr_r64_imm8_effect_step 0x111836 0x48 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11180c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11180f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (10, 10), (11, 11), (12, 12), (13, 56), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111814) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 58), (10, 10), (11, 11), (12, 12), (13, 56), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111817) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 60), (10, 10), (11, 11), (12, 12), (13, 56), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11181a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 60), (10, 10), (11, 11), (12, 12), (13, 62), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11181e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 60), (10, 10), (11, 11), (12, 12), (13, 64), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111821) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 66), (8, 60), (10, 10), (11, 11), (12, 12), (13, 64), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111824) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 66), (8, 68), (10, 10), (11, 11), (12, 12), (13, 64), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111827) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 66), (8, 70), (10, 10), (11, 11), (12, 12), (13, 64), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11182a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 72), (8, 70), (10, 10), (11, 11), (12, 12), (13, 64), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11182d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 72), (8, 70), (10, 74), (11, 11), (12, 12), (13, 64), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111830) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 76), (8, 70), (10, 74), (11, 11), (12, 12), (13, 64), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111833) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 78), (8, 70), (10, 74), (11, 11), (12, 12), (13, 64), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111836) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 80), (8, 70), (10, 74), (11, 11), (12, 12), (13, 64), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11183a) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 82) (by decide) rfl

theorem block_l1172e7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1172e7 :=
  Rest.liftedBlock (rest_l1172e7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1172e7 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
