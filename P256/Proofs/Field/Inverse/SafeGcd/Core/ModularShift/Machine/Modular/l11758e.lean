import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11758e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111aae bytes_l11758e) (entryMap (live .l11758e))
      15 0x111aae bytes_l11758e b_l11758e := by
  have f0 : InstrSpec 0x111aae [0x4C, 0x89, 0x54, 0x24, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111aae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111aae + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111aae 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111aae 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111aae 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x111ab3 [0x4C, 0x8D, 0x44, 0x24, 0x10] (fun s => s.RIP = 0x111ab3) (leaR64Effect 0x111ab3 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x111ab3 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x111ab3 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x111ab8 [0x88, 0x4C, 0x24, 0x10] (StorePre 0x111ab8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111ab8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111ab8 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111ab8 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x111ab8 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x111abc [0x4C, 0x8D, 0x54, 0x24, 0x10] (fun s => s.RIP = 0x111abc) (leaR64Effect 0x111abc 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x111abc 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x111abc 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x111ac1 [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x10] (LoadPre 0x111ac1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111ac1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x111ac1 6 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x111ac1 6 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x111ac1 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x111ac7 [0x48, 0x31, 0xC2] (fun s => s.RIP = 0x111ac7) (xorR64R64Effect 0x111ac7 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111ac7 2 0).toInstrSpec (xor_r64_r64_effect_step 0x111ac7 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111aca [0x49, 0xF7, 0xD8] (fun s => s.RIP = 0x111aca) (negR64Effect 0x111aca 8)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (negR64Effect_footprint 0x111aca 8).toInstrSpec (neg_r64_effect_step 0x111aca 0x49 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111acd [0x49, 0x21, 0xD0] (fun s => s.RIP = 0x111acd) (andR64R64Effect 0x111acd 8 2)
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111acd 8 2).toInstrSpec (and_r64_r64_effect_step 0x111acd 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111ad0 [0x49, 0x31, 0xC0] (fun s => s.RIP = 0x111ad0) (xorR64R64Effect 0x111ad0 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111ad0 8 0).toInstrSpec (xor_r64_r64_effect_step 0x111ad0 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x111ad3 [0x88, 0x4C, 0x24, 0x10] (StorePre 0x111ad3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111ad3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111ad3 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111ad3 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x111ad3 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x111ad7 [0x0F, 0xB6, 0x44, 0x24, 0x10] (LoadPre 0x111ad7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111ad7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111ad7 5 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x111ad7 5 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x111ad7 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x111adc [0x4C, 0x31, 0xCB] (fun s => s.RIP = 0x111adc) (xorR64R64Effect 0x111adc 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111adc 3 9).toInstrSpec (xor_r64_r64_effect_step 0x111adc 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x111adf [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x111adf) (negR64Effect 0x111adf 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x111adf 0).toInstrSpec (neg_r64_effect_step 0x111adf 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111ae2 [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x111ae2) (andR64R64Effect 0x111ae2 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111ae2 0 3).toInstrSpec (and_r64_r64_effect_step 0x111ae2 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x111ae5 [0x4C, 0x31, 0xC8] (fun s => s.RIP = 0x111ae5) (xorR64R64Effect 0x111ae5 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x111ae5 0 9).toInstrSpec (xor_r64_r64_effect_step 0x111ae5 0x4c 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ab3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ab8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111abc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ac1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ac7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111aca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 61), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111acd) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ad0) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ad3) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ad7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111adc) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 68), (1, 1), (2, 59), (3, 70), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111adf) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 1), (2, 59), (3, 70), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ae2) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 1), (2, 59), (3, 70), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ae5) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 1), (2, 59), (3, 70), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ae8) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 78) (by decide) rfl

theorem block_l11758e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11758e :=
  Rest.liftedBlock (rest_l11758e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11758e x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
