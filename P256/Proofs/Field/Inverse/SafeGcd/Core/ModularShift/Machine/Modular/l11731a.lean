import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11731a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11183a bytes_l11731a) (entryMap (live .l11731a))
      15 0x11183a bytes_l11731a b_l11731a := by
  have f0 : InstrSpec 0x11183a [0x48, 0x89, 0x7C, 0x24, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11183a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11183a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11183a 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11183a 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x11183a 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11183f [0x31, 0xC0] (fun s => s.RIP = 0x11183f) (xorR32R32Effect 0x11183f 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11183f 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x11183f 0xc0 (by decide)) pre_rip
  have f2 : InstrSpec 0x111841 [0x48, 0x2B, 0x44, 0x24, 0x10] (LoadPre 0x111841 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111841 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x111841 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (subR64M64Effect_footprint 0x111841 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x111841 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x111846 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x111846) (movR64R64Effect 0x111846 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x111846 6 14).toInstrSpec (mov_r64_r64_effect_step 0x111846 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x111849 [0x48, 0x29, 0xD6] (fun s => s.RIP = 0x111849) (subR64R64Effect 0x111849 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (subR64R64Effect_footprint 0x111849 6 2).toInstrSpec (sub_r64_r64_effect_step 0x111849 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11184c [0x49, 0xF7, 0xD6] (fun s => s.RIP = 0x11184c) (notR64Effect 0x11184c 14)
      [.gpr 14] [] [.reg 14, .rip] :=
    (notR64Effect_footprint 0x11184c 14).toInstrSpec (not_r64_effect_step 0x11184c 0x49 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11184f [0x48, 0x89, 0xD7] (fun s => s.RIP = 0x11184f) (movR64R64Effect 0x11184f 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11184f 7 2).toInstrSpec (mov_r64_r64_effect_step 0x11184f 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111852 [0x4C, 0x21, 0xF7] (fun s => s.RIP = 0x111852) (andR64R64Effect 0x111852 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111852 7 14).toInstrSpec (and_r64_r64_effect_step 0x111852 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111855 [0x49, 0x09, 0xD6] (fun s => s.RIP = 0x111855) (orR64R64Effect 0x111855 14 2)
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111855 14 2).toInstrSpec (or_r64_r64_effect_step 0x111855 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x111858 [0x48, 0xC1, 0xF8, 0x3F] (fun s => s.RIP = 0x111858) (sarR64Effect 0x111858 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (sarR64Effect_footprint 0x111858 4 0 63).toInstrSpec (sar_r64_imm8_effect_step 0x111858 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11185c [0x48, 0x01, 0xF0] (fun s => s.RIP = 0x11185c) (addR64R64Effect 0x11185c 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11185c 0 6).toInstrSpec (add_r64_r64_effect_step 0x11185c 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11185f [0x49, 0x21, 0xC6] (fun s => s.RIP = 0x11185f) (andR64R64Effect 0x11185f 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11185f 14 0).toInstrSpec (and_r64_r64_effect_step 0x11185f 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x111862 [0x49, 0x09, 0xFE] (fun s => s.RIP = 0x111862) (orR64R64Effect 0x111862 14 7)
      [.gpr 14, .gpr 7] [] [.reg 14, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111862 14 7).toInstrSpec (or_r64_r64_effect_step 0x111862 0x49 0xfe (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111865 [0x49, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x111865) (shrR64Effect 0x111865 4 14 63)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64Effect_footprint 0x111865 4 14 63).toInstrSpec (shr_r64_imm8_effect_step 0x111865 0x49 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x111869 [0x4C, 0x89, 0x74, 0x24, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111869 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111869 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111869 14 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111869 14 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111869 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11183f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111841) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (4, 4), (5, 5), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111846) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 1), (2, 2), (4, 4), (5, 5), (6, 58), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111849) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 56), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11184c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 56), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x11184f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 56), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 64), (10, 10), (11, 11), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111852) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 56), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111855) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 56), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (22, 22), (39, 39), (51, 51)]) (p' := 0x111858) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (22, 22), (39, 39), (51, 51)]) (p' := 0x11185c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (22, 22), (39, 39), (51, 51)]) (p' := 0x11185f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 72), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 74), (22, 22), (39, 39), (51, 51)]) (p' := 0x111862) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 72), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 76), (22, 22), (39, 39), (51, 51)]) (p' := 0x111865) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 72), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 78), (22, 22), (39, 39), (51, 51)]) (p' := 0x111869) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 72), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 78), (22, 22), (39, 39), (51, 51)]) (p' := 0x11186e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 81) (by decide) rfl

theorem block_l11731a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11731a :=
  Rest.liftedBlock (rest_l11731a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11731a x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
