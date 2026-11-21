import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1186f3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112c13 bytes_l1186f3) (entryMap (live .l1186f3))
      14 0x112c13 bytes_l1186f3 b_l1186f3 := by
  have f0 : InstrSpec 0x112c13 [0x49, 0x01, 0xC6] (fun s => s.RIP = 0x112c13) (addR64R64Effect 0x112c13 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112c13 14 0).toInstrSpec (add_r64_r64_effect_step 0x112c13 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x112c16 [0x48, 0x11, 0xD3] (fun s => s.RIP = 0x112c16) (atFlags StatusFlags.CF (adcR64R64Effect 0x112c16 3 2))
      [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x112c16 3 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x112c16 0x48 0xd3 c (by decide) (by decide))) pre_rip
  have f2 : InstrSpec 0x112c19 [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x112c19) (movR64R64Effect 0x112c19 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112c19 0 8).toInstrSpec (mov_r64_r64_effect_step 0x112c19 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x112c1c [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x112c1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112c1c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112c1c 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x112c1c 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x112c1c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x112c21 [0x48, 0x29, 0xF0] (fun s => s.RIP = 0x112c21) (subR64R64Effect 0x112c21 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x112c21 0 6).toInstrSpec (sub_r64_r64_effect_step 0x112c21 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112c24 [0x49, 0xF7, 0xD0] (fun s => s.RIP = 0x112c24) (notR64Effect 0x112c24 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (notR64Effect_footprint 0x112c24 8).toInstrSpec (not_r64_effect_step 0x112c24 0x49 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112c27 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x112c27) (movR64R64Effect 0x112c27 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x112c27 2 6).toInstrSpec (mov_r64_r64_effect_step 0x112c27 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x112c2a [0x4C, 0x21, 0xC2] (fun s => s.RIP = 0x112c2a) (andR64R64Effect 0x112c2a 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112c2a 2 8).toInstrSpec (and_r64_r64_effect_step 0x112c2a 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x112c2d [0x49, 0x09, 0xF0] (fun s => s.RIP = 0x112c2d) (orR64R64Effect 0x112c2d 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x112c2d 8 6).toInstrSpec (or_r64_r64_effect_step 0x112c2d 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112c30 [0x48, 0x8B, 0x71, 0x08] (LoadPre 0x112c30 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x112c30 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112c30 6 (.base 1 (.d8 0x8)))
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x112c30 6 (.base 1 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x112c30 0x48 (by decide) 6 (.base 1 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x112c34 [0x48, 0x8B, 0x49, 0x10] (LoadPre 0x112c34 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x112c34 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112c34 1 (.base 1 (.d8 0x10)))
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x112c34 1 (.base 1 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x112c34 0x48 (by decide) 1 (.base 1 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x112c38 [0x49, 0x21, 0xC0] (fun s => s.RIP = 0x112c38) (andR64R64Effect 0x112c38 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112c38 8 0).toInstrSpec (and_r64_r64_effect_step 0x112c38 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x112c3b [0x49, 0x09, 0xD0] (fun s => s.RIP = 0x112c3b) (orR64R64Effect 0x112c3b 8 2)
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x112c3b 8 2).toInstrSpec (or_r64_r64_effect_step 0x112c3b 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x112c3e [0x49, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x112c3e) (shrR64Effect 0x112c3e 4 8 63)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x112c3e 4 8 63).toInstrSpec (shr_r64_imm8_effect_step 0x112c3e 0x49 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (13, 13), (14, 53), (15, 15), (16, 54), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c16) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 56), (4, 4), (7, 7), (8, 8), (9, 9), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c19) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 56), (4, 4), (7, 7), (8, 8), (9, 9), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c1c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 56), (4, 4), (6, 60), (7, 7), (8, 8), (9, 9), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c21) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 1), (2, 2), (3, 56), (4, 4), (6, 60), (7, 7), (8, 8), (9, 9), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c24) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 1), (2, 2), (3, 56), (4, 4), (6, 60), (7, 7), (8, 64), (9, 9), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c27) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 1), (2, 66), (3, 56), (4, 4), (6, 60), (7, 7), (8, 64), (9, 9), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c2a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 62), (1, 1), (2, 68), (3, 56), (4, 4), (6, 60), (7, 7), (8, 64), (9, 9), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c2d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 62), (1, 1), (2, 68), (3, 56), (4, 4), (6, 60), (7, 7), (8, 70), (9, 9), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c30) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 62), (1, 1), (2, 68), (3, 56), (4, 4), (6, 72), (7, 7), (8, 70), (9, 9), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c34) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 62), (1, 74), (2, 68), (3, 56), (4, 4), (6, 72), (7, 7), (8, 70), (9, 9), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c38) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 62), (1, 74), (2, 68), (3, 56), (4, 4), (6, 72), (7, 7), (8, 76), (9, 9), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c3b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 62), (1, 74), (2, 68), (3, 56), (4, 4), (6, 72), (7, 7), (8, 78), (9, 9), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c3e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 62), (1, 74), (2, 68), (3, 56), (4, 4), (6, 72), (7, 7), (8, 80), (9, 9), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112c42) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 82) (by decide) rfl

theorem block_l1186f3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1186f3 :=
  Rest.liftedBlock (rest_l1186f3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1186f3 x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
