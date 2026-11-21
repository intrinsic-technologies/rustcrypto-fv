import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l118722 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112c42 bytes_l118722) (entryMap (live .l118722))
      15 0x112c42 bytes_l118722 b_l118722 := by
  have f0 : InstrSpec 0x112c42 [0x4C, 0x89, 0x04, 0x24] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112c42 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112c42 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112c42 8 (.sib 4 none 0 .none))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112c42 8 (.sib 4 none 0 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112c42 0x4c (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x112c46 [0x48, 0x89, 0xE2] (fun s => s.RIP = 0x112c46) (movR64R64Effect 0x112c46 2 4)
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x112c46 2 4).toInstrSpec (mov_r64_r64_effect_step 0x112c46 0x48 0xe2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112c49 [0x31, 0xD2] (fun s => s.RIP = 0x112c49) (xorR32R32Effect 0x112c49 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x112c49 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x112c49 0xd2 (by decide)) pre_rip
  have f3 : InstrSpec 0x112c4b [0x48, 0x2B, 0x14, 0x24] (LoadPre 0x112c4b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112c4b + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x112c4b 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x112c4b 2 (.sib 4 none 0 .none)).toInstrSpec (sub_r64_m64_effect_step 0x112c4b 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x112c4f [0x49, 0x89, 0xF0] (fun s => s.RIP = 0x112c4f) (movR64R64Effect 0x112c4f 8 6)
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x112c4f 8 6).toInstrSpec (mov_r64_r64_effect_step 0x112c4f 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112c52 [0x4D, 0x29, 0xC8] (fun s => s.RIP = 0x112c52) (subR64R64Effect 0x112c52 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x112c52 8 9).toInstrSpec (sub_r64_r64_effect_step 0x112c52 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112c55 [0x48, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x112c55) (sarR64Effect 0x112c55 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (sarR64Effect_footprint 0x112c55 4 2 63).toInstrSpec (sar_r64_imm8_effect_step 0x112c55 0x48 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x112c59 [0x4C, 0x01, 0xC2] (fun s => s.RIP = 0x112c59) (addR64R64Effect 0x112c59 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112c59 2 8).toInstrSpec (add_r64_r64_effect_step 0x112c59 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x112c5c [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x112c5c) (notR64Effect 0x112c5c 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x112c5c 6).toInstrSpec (not_r64_effect_step 0x112c5c 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112c5f [0x4D, 0x89, 0xC8] (fun s => s.RIP = 0x112c5f) (movR64R64Effect 0x112c5f 8 9)
      [.gpr 9] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x112c5f 8 9).toInstrSpec (mov_r64_r64_effect_step 0x112c5f 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x112c62 [0x49, 0x21, 0xF0] (fun s => s.RIP = 0x112c62) (andR64R64Effect 0x112c62 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112c62 8 6).toInstrSpec (and_r64_r64_effect_step 0x112c62 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x112c65 [0x4C, 0x09, 0xCE] (fun s => s.RIP = 0x112c65) (orR64R64Effect 0x112c65 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x112c65 6 9).toInstrSpec (or_r64_r64_effect_step 0x112c65 0x4c 0xce (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x112c68 [0x48, 0x21, 0xD6] (fun s => s.RIP = 0x112c68) (andR64R64Effect 0x112c68 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112c68 6 2).toInstrSpec (and_r64_r64_effect_step 0x112c68 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x112c6b [0x4C, 0x09, 0xC6] (fun s => s.RIP = 0x112c6b) (orR64R64Effect 0x112c6b 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x112c6b 6 8).toInstrSpec (or_r64_r64_effect_step 0x112c6b 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x112c6e [0x48, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x112c6e) (shrR64Effect 0x112c6e 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x112c6e 4 6 63).toInstrSpec (shr_r64_imm8_effect_step 0x112c6e 0x48 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c46) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 54), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c49) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c4b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c4f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 60), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c52) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c55) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 64), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c59) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 66), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c5c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 66), (3, 3), (4, 4), (6, 68), (7, 7), (8, 62), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c5f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 66), (3, 3), (4, 4), (6, 68), (7, 7), (8, 70), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c62) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 66), (3, 3), (4, 4), (6, 68), (7, 7), (8, 72), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c65) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 66), (3, 3), (4, 4), (6, 74), (7, 7), (8, 72), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c68) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 66), (3, 3), (4, 4), (6, 76), (7, 7), (8, 72), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c6b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 66), (3, 3), (4, 4), (6, 78), (7, 7), (8, 72), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c6e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 66), (3, 3), (4, 4), (6, 80), (7, 7), (8, 72), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c72) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 82) (by decide) rfl

theorem block_l118722 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l118722 :=
  Rest.liftedBlock (rest_l118722 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l118722 x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
