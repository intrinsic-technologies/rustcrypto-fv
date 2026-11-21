import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117477 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111997 bytes_l117477) (entryMap (live .l117477))
      12 0x111997 bytes_l117477 b_l117477 := by
  have f0 : InstrSpec 0x111997 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x111997) (movR64R64Effect 0x111997 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x111997 0 2).toInstrSpec (mov_r64_r64_effect_step 0x111997 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11199a [0x48, 0x8B, 0x7C, 0x24, 0x50] (LoadPre 0x11199a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11199a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11199a 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x11199a 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x11199a 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11199f [0x48, 0x29, 0xF8] (fun s => s.RIP = 0x11199f) (subR64R64Effect 0x11199f 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11199f 0 7).toInstrSpec (sub_r64_r64_effect_step 0x11199f 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1119a2 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x1119a2) (movR64R64Effect 0x1119a2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1119a2 1 2).toInstrSpec (mov_r64_r64_effect_step 0x1119a2 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1119a5 [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x1119a5) (notR64Effect 0x1119a5 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x1119a5 1).toInstrSpec (not_r64_effect_step 0x1119a5 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1119a8 [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x1119a8) (movR64R64Effect 0x1119a8 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1119a8 6 7).toInstrSpec (mov_r64_r64_effect_step 0x1119a8 0x48 0xfe (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1119ab [0x48, 0x21, 0xCE] (fun s => s.RIP = 0x1119ab) (andR64R64Effect 0x1119ab 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1119ab 6 1).toInstrSpec (and_r64_r64_effect_step 0x1119ab 0x48 0xce (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1119ae [0x48, 0x09, 0xF9] (fun s => s.RIP = 0x1119ae) (orR64R64Effect 0x1119ae 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1119ae 1 7).toInstrSpec (or_r64_r64_effect_step 0x1119ae 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1119b1 [0x48, 0x21, 0xC1] (fun s => s.RIP = 0x1119b1) (andR64R64Effect 0x1119b1 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1119b1 1 0).toInstrSpec (and_r64_r64_effect_step 0x1119b1 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1119b4 [0x48, 0x09, 0xF1] (fun s => s.RIP = 0x1119b4) (orR64R64Effect 0x1119b4 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1119b4 1 6).toInstrSpec (or_r64_r64_effect_step 0x1119b4 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1119b7 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x1119b7) (shrR64Effect 0x1119b7 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1119b7 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x1119b7 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1119bb [0x48, 0x89, 0x4C, 0x24, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1119bb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1119bb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1119bb 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1119bb 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1119bb 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x11199a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x11199f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119a2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119a5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119a8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 63), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119ab) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 65), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119ae) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 65), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119b1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 69), (2, 2), (3, 3), (4, 4), (5, 5), (6, 65), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119b4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 71), (2, 2), (3, 3), (4, 4), (5, 5), (6, 65), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119b7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 57), (1, 73), (2, 2), (3, 3), (4, 4), (5, 5), (6, 65), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119bb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 57), (1, 73), (2, 2), (3, 3), (4, 4), (5, 5), (6, 65), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x1119c0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 76) (by decide) rfl

theorem block_l117477 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117477 :=
  Rest.liftedBlock (rest_l117477 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117477 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
