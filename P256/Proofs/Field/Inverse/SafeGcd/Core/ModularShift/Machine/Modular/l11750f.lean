import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11750f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111a2f bytes_l11750f) (entryMap (live .l11750f))
      18 0x111a2f bytes_l11750f b_l11750f := by
  have f0 : InstrSpec 0x111a2f [0x48, 0x89, 0x7C, 0x24, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111a2f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111a2f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111a2f 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111a2f 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111a2f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x111a34 [0x31, 0xFF] (fun s => s.RIP = 0x111a34) (xorR32R32Effect 0x111a34 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x111a34 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x111a34 0xff (by decide)) pre_rip
  have f2 : InstrSpec 0x111a36 [0x48, 0x2B, 0x7C, 0x24, 0x10] (LoadPre 0x111a36 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111a36 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x111a36 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.reg 7, .flags, .rip] :=
    (subR64M64Effect_footprint 0x111a36 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x111a36 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x111a3b [0x4D, 0x09, 0xD3] (fun s => s.RIP = 0x111a3b) (orR64R64Effect 0x111a3b 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111a3b 11 10).toInstrSpec (or_r64_r64_effect_step 0x111a3b 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x111a3e [0x4D, 0x89, 0xD8] (fun s => s.RIP = 0x111a3e) (movR64R64Effect 0x111a3e 8 11)
      [.gpr 11] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x111a3e 8 11).toInstrSpec (mov_r64_r64_effect_step 0x111a3e 0x4d 0xd8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x111a41 [0x4C, 0x8B, 0x74, 0x24, 0x68] (LoadPre 0x111a41 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x111a41 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111a41 14 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x111a41 14 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x111a41 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x111a46 [0x4D, 0x29, 0xF0] (fun s => s.RIP = 0x111a46) (subR64R64Effect 0x111a46 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x111a46 8 14).toInstrSpec (sub_r64_r64_effect_step 0x111a46 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111a49 [0x48, 0xC1, 0xFF, 0x3F] (fun s => s.RIP = 0x111a49) (sarR64Effect 0x111a49 4 7 63)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (sarR64Effect_footprint 0x111a49 4 7 63).toInstrSpec (sar_r64_imm8_effect_step 0x111a49 0x48 0xff 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111a4d [0x4C, 0x01, 0xC7] (fun s => s.RIP = 0x111a4d) (addR64R64Effect 0x111a4d 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x111a4d 7 8).toInstrSpec (add_r64_r64_effect_step 0x111a4d 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x111a50 [0x4D, 0x89, 0xD8] (fun s => s.RIP = 0x111a50) (movR64R64Effect 0x111a50 8 11)
      [.gpr 11] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x111a50 8 11).toInstrSpec (mov_r64_r64_effect_step 0x111a50 0x4d 0xd8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x111a53 [0x49, 0xF7, 0xD0] (fun s => s.RIP = 0x111a53) (notR64Effect 0x111a53 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (notR64Effect_footprint 0x111a53 8).toInstrSpec (not_r64_effect_step 0x111a53 0x49 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x111a56 [0x4D, 0x89, 0xF2] (fun s => s.RIP = 0x111a56) (movR64R64Effect 0x111a56 10 14)
      [.gpr 14] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x111a56 10 14).toInstrSpec (mov_r64_r64_effect_step 0x111a56 0x4d 0xf2 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x111a59 [0x4D, 0x21, 0xC2] (fun s => s.RIP = 0x111a59) (andR64R64Effect 0x111a59 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111a59 10 8).toInstrSpec (and_r64_r64_effect_step 0x111a59 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111a5c [0x4D, 0x09, 0xF0] (fun s => s.RIP = 0x111a5c) (orR64R64Effect 0x111a5c 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111a5c 8 14).toInstrSpec (or_r64_r64_effect_step 0x111a5c 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x111a5f [0x49, 0x21, 0xF8] (fun s => s.RIP = 0x111a5f) (andR64R64Effect 0x111a5f 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x111a5f 8 7).toInstrSpec (and_r64_r64_effect_step 0x111a5f 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x111a62 [0x4D, 0x09, 0xD0] (fun s => s.RIP = 0x111a62) (orR64R64Effect 0x111a62 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111a62 8 10).toInstrSpec (or_r64_r64_effect_step 0x111a62 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x111a65 [0x49, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x111a65) (shrR64Effect 0x111a65 4 8 63)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x111a65 4 8 63).toInstrSpec (shr_r64_imm8_effect_step 0x111a65 0x49 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x111a69 [0x4C, 0x89, 0x44, 0x24, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111a69 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111a69 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111a69 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111a69 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111a69 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a34) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a36) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 56), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a3b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 56), (9, 9), (10, 10), (11, 58), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a3e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 56), (8, 60), (9, 9), (10, 10), (11, 58), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a41) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 56), (8, 60), (9, 9), (10, 10), (11, 58), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a46) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 56), (8, 64), (9, 9), (10, 10), (11, 58), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a49) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 66), (8, 64), (9, 9), (10, 10), (11, 58), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a4d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 68), (8, 64), (9, 9), (10, 10), (11, 58), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a50) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 68), (8, 70), (9, 9), (10, 10), (11, 58), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a53) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 68), (8, 72), (9, 9), (10, 10), (11, 58), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a56) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 68), (8, 72), (9, 9), (10, 74), (11, 58), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a59) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 68), (8, 72), (9, 9), (10, 76), (11, 58), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a5c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 68), (8, 78), (9, 9), (10, 76), (11, 58), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a5f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 68), (8, 80), (9, 9), (10, 76), (11, 58), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a62) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 68), (8, 82), (9, 9), (10, 76), (11, 58), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a65) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 68), (8, 84), (9, 9), (10, 76), (11, 58), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a69) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 68), (8, 84), (9, 9), (10, 76), (11, 58), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x111a6e) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 87) (by decide) rfl

theorem block_l11750f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11750f :=
  Rest.liftedBlock (rest_l11750f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11750f x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
