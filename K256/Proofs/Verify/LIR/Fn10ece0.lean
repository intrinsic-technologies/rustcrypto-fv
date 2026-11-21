import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

theorem rest_l10ece0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ece0 bytes_l10ece0) (entryMap (live .l10ece0))
      12 0x10ece0 bytes_l10ece0 b_l10ece0 := by
  have f0 : InstrSpec 0x10ece0 [0x55] (PushPre 0x10ece0 1) (pushR64Effect 0x10ece0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ece0 1 5).toInstrSpec (push_r64_effect_step 0x10ece0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10ece1 [0x41, 0x57] (PushPre 0x10ece1 2) (pushR64Effect 0x10ece1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ece1 2 15).toInstrSpec (push_r64_rex_effect_step 0x10ece1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10ece3 [0x41, 0x56] (PushPre 0x10ece3 2) (pushR64Effect 0x10ece3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ece3 2 14).toInstrSpec (push_r64_rex_effect_step 0x10ece3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10ece5 [0x41, 0x55] (PushPre 0x10ece5 2) (pushR64Effect 0x10ece5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ece5 2 13).toInstrSpec (push_r64_rex_effect_step 0x10ece5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10ece7 [0x41, 0x54] (PushPre 0x10ece7 2) (pushR64Effect 0x10ece7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ece7 2 12).toInstrSpec (push_r64_rex_effect_step 0x10ece7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10ece9 [0x53] (PushPre 0x10ece9 1) (pushR64Effect 0x10ece9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ece9 1 3).toInstrSpec (push_r64_effect_step 0x10ece9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10ecea [0x48, 0x81, 0xEC, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ecea) (subR64Imm32Effect 0x10ecea 4 0xb8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10ecea 4 0xb8).toInstrSpec (sub_r64_imm32_effect_step 0x10ecea 0x48 0xec 0xb8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10ecf1 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x10ecf1) (movR64R64Effect 0x10ecf1 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10ecf1 14 6).toInstrSpec (mov_r64_r64_effect_step 0x10ecf1 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10ecf4 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x10ecf4) (movR64R64Effect 0x10ecf4 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10ecf4 3 7).toInstrSpec (mov_r64_r64_effect_step 0x10ecf4 0x48 0xfb (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10ecf7 [0x48, 0x83, 0xC6, 0x50] (fun s => s.RIP = 0x10ecf7) (addR64Imm8Effect 0x10ecf7 6 0x50)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10ecf7 6 0x50).toInstrSpec (add_r64_imm8_effect_step 0x10ecf7 0x48 0xc6 0x50 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10ecfb [0x48, 0x8D, 0x7C, 0x24, 0x58] (fun s => s.RIP = 0x10ecfb) (leaR64Effect 0x10ecfb 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10ecfb 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (lea_r64_effect_step 0x10ecfb 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10ed00 [0xE8, 0x2B, 0x5C, 0x00, 0x00] (PushPre 0x10ed00 5) (callEffect (fun _ => 0x114930) 0x10ed05)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10ed00 0x114930 0x10ed05).toInstrSpec (call_rel32_effect_step 0x10ed00 0x5c2b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ece1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ece3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ece5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ece7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ece9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecea) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecf1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecf4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(3, 69), (4, 65), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecf7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(3, 69), (4, 65), (5, 5), (6, 71), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ecfb) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(3, 69), (4, 65), (5, 5), (6, 71), (7, 73), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed00) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(3, 69), (4, 75), (5, 5), (6, 71), (7, 73), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114930) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l10ece0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ece0 :=
  Rest.liftedBlock (rest_l10ece0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ece0 x hx)

theorem rest_l10ed05_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x10ed05 bytes_l10ed05) [(0, 81), (1, 75), (2, 83), (3, 3), (4, 4), (5, 5), (6, 63), (7, 87), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x10ed55 bytes_l10ed05_1 b_l10ed05_1 := by
  have f20 : InstrSpec 0x10ed55 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x10ed55 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10ed55 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ed55 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ed55 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10ed55 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x10ed5a [0x48, 0x89, 0x7C, 0x24, 0x18] (StorePre 0x10ed5a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10ed5a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ed5a 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ed5a 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10ed5a 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x10ed5f [0x48, 0x8D, 0x7C, 0x24, 0x58] (fun s => s.RIP = 0x10ed5f) (leaR64Effect 0x10ed5f 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10ed5f 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (lea_r64_effect_step 0x10ed5f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x10ed64 [0x48, 0x89, 0xE6] (fun s => s.RIP = 0x10ed64) (movR64R64Effect 0x10ed64 6 4)
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10ed64 6 4).toInstrSpec (mov_r64_r64_effect_step 0x10ed64 0x48 0xe6 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x10ed67 [0x48, 0xB9, 0xCF, 0xCA, 0xDA, 0x2D, 0xE2, 0xF6, 0xC7, 0x27] (fun s => s.RIP = 0x10ed67) (movR64Imm64Effect 0x10ed67 1 0x27c7f6e22ddacacf)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x10ed67 1 0x27c7f6e22ddacacf).toInstrSpec (mov_r64_imm64_effect_step 0x10ed67 0x48 0xb9 (by decide) (by decide) 0x27c7f6e22ddacacf) pre_rip
  have f25 : InstrSpec 0x10ed71 [0x48, 0xC7, 0xC2, 0xE0, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x10ed71) (movR64Imm32Effect 0x10ed71 2 0x2021e0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10ed71 2 0x2021e0).toInstrSpec (mov_r64_imm32_effect_step 0x10ed71 0x48 0xc2 (by decide) (by decide) (by decide) 0x2021e0) pre_rip
  have f26 : InstrSpec 0x10ed78 [0x49, 0xC7, 0xC0, 0x80, 0x21, 0x20, 0x00] (fun s => s.RIP = 0x10ed78) (movR64Imm32Effect 0x10ed78 8 0x202180)
      [] [] [.reg 8, .rip] :=
    (movR64Imm32Effect_footprint 0x10ed78 8 0x202180).toInstrSpec (mov_r64_imm32_effect_step 0x10ed78 0x49 0xc0 (by decide) (by decide) (by decide) 0x202180) pre_rip
  have f27 : InstrSpec 0x10ed7f [0xE8, 0xAC, 0xA0, 0xFF, 0xFF] (PushPre 0x10ed7f 5) (callEffect (fun _ => 0x108e30) 0x10ed84)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10ed7f 0x108e30 0x10ed84).toInstrSpec (call_rel32_effect_step 0x10ed7f 0xffffa0ac (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 81), (1, 75), (2, 83), (3, 3), (4, 4), (5, 5), (6, 63), (7, 87), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed5a) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 81), (1, 75), (2, 83), (3, 3), (4, 4), (5, 5), (6, 63), (7, 87), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed5f) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f22 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 81), (1, 75), (2, 83), (3, 3), (4, 4), (5, 5), (6, 63), (7, 93), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed64) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 81), (1, 75), (2, 83), (3, 3), (4, 4), (5, 5), (6, 95), (7, 93), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed67) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 81), (1, 97), (2, 83), (3, 3), (4, 4), (5, 5), (6, 95), (7, 93), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed71) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 81), (1, 97), (2, 99), (3, 3), (4, 4), (5, 5), (6, 95), (7, 93), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed78) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f26 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 81), (1, 97), (2, 99), (3, 3), (4, 4), (5, 5), (6, 95), (7, 93), (8, 101), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed7f) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f27 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 81), (1, 97), (2, 99), (3, 3), (4, 103), (5, 5), (6, 95), (7, 93), (8, 101), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e30) f27 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 105) (by decide) (by decide) rfl rfl

theorem rest_l10ed05 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ed05 bytes_l10ed05) (entryMap (live .l10ed05))
      28 0x10ed05 bytes_l10ed05 b_l10ed05 := by
  have f0 : InstrSpec 0x10ed05 [0x48, 0x8B, 0x44, 0x24, 0x60] (LoadPre 0x10ed05 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10ed05 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed05 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ed05 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x10ed05 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10ed0a [0x48, 0x8B, 0x4C, 0x24, 0x68] (LoadPre 0x10ed0a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10ed0a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed0a 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10ed0a 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x10ed0a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10ed0f [0x48, 0x8B, 0x54, 0x24, 0x70] (LoadPre 0x10ed0f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10ed0f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed0f 2 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10ed0f 2 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x10ed0f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10ed14 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x10ed14) (movR64R64Effect 0x10ed14 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10ed14 6 0).toInstrSpec (mov_r64_r64_effect_step 0x10ed14 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10ed17 [0x48, 0xC1, 0xE6, 0x34] (fun s => s.RIP = 0x10ed17) (shlR64Effect 0x10ed17 4 6 52)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64Effect_footprint 0x10ed17 4 6 52).toInstrSpec (shl_r64_imm8_effect_step 0x10ed17 0x48 0xe6 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10ed1b [0x48, 0x0B, 0x74, 0x24, 0x58] (LoadPre 0x10ed1b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10ed1b + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x10ed1b 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (orR64M64Effect_footprint 0x10ed1b 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (or_r64_m64_effect_step 0x10ed1b 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10ed20 [0x48, 0x8B, 0x7C, 0x24, 0x78] (LoadPre 0x10ed20 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10ed20 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed20 7 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10ed20 7 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x10ed20 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10ed25 [0x48, 0xC1, 0xE8, 0x0C] (fun s => s.RIP = 0x10ed25) (shrR64Effect 0x10ed25 4 0 12)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x10ed25 4 0 12).toInstrSpec (shr_r64_imm8_effect_step 0x10ed25 0x48 0xe8 0xc (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10ed29 [0x49, 0x89, 0xC8] (fun s => s.RIP = 0x10ed29) (movR64R64Effect 0x10ed29 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10ed29 8 1).toInstrSpec (mov_r64_r64_effect_step 0x10ed29 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10ed2c [0x49, 0xC1, 0xE0, 0x28] (fun s => s.RIP = 0x10ed2c) (shlR64Effect 0x10ed2c 4 8 40)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64Effect_footprint 0x10ed2c 4 8 40).toInstrSpec (shl_r64_imm8_effect_step 0x10ed2c 0x49 0xe0 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10ed30 [0x49, 0x09, 0xC0] (fun s => s.RIP = 0x10ed30) (orR64R64Effect 0x10ed30 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10ed30 8 0).toInstrSpec (or_r64_r64_effect_step 0x10ed30 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10ed33 [0x48, 0xC1, 0xE9, 0x18] (fun s => s.RIP = 0x10ed33) (shrR64Effect 0x10ed33 4 1 24)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10ed33 4 1 24).toInstrSpec (shr_r64_imm8_effect_step 0x10ed33 0x48 0xe9 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10ed37 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x10ed37) (movR64R64Effect 0x10ed37 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10ed37 0 2).toInstrSpec (mov_r64_r64_effect_step 0x10ed37 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10ed3a [0x48, 0xC1, 0xE0, 0x1C] (fun s => s.RIP = 0x10ed3a) (shlR64Effect 0x10ed3a 4 0 28)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x10ed3a 4 0 28).toInstrSpec (shl_r64_imm8_effect_step 0x10ed3a 0x48 0xe0 0x1c (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10ed3e [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x10ed3e) (orR64R64Effect 0x10ed3e 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10ed3e 0 1).toInstrSpec (or_r64_r64_effect_step 0x10ed3e 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10ed41 [0x48, 0xC1, 0xEA, 0x24] (fun s => s.RIP = 0x10ed41) (shrR64Effect 0x10ed41 4 2 36)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10ed41 4 2 36).toInstrSpec (shr_r64_imm8_effect_step 0x10ed41 0x48 0xea 0x24 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10ed45 [0x48, 0xC1, 0xE7, 0x10] (fun s => s.RIP = 0x10ed45) (shlR64Effect 0x10ed45 4 7 16)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x10ed45 4 7 16).toInstrSpec (shl_r64_imm8_effect_step 0x10ed45 0x48 0xe7 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10ed49 [0x48, 0x09, 0xD7] (fun s => s.RIP = 0x10ed49) (orR64R64Effect 0x10ed49 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10ed49 7 2).toInstrSpec (or_r64_r64_effect_step 0x10ed49 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10ed4c [0x48, 0x89, 0x34, 0x24] (StorePre 0x10ed4c 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10ed4c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10ed4c 6 (.sib 4 none 0 .none))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ed4c 6 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10ed4c 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x10ed50 [0x4C, 0x89, 0x44, 0x24, 0x08] (StorePre 0x10ed50 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10ed50 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ed50 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ed50 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10ed50 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed0a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed0f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed14) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed17) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed1b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed20) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed25) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed29) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 69), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed2c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 67), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed30) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 67), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed33) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 67), (1, 75), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed37) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 75), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed3a) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 75), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed3e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 75), (2, 57), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed41) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 81), (1, 75), (2, 83), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed45) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 81), (1, 75), (2, 83), (3, 3), (4, 4), (5, 5), (6, 63), (7, 85), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed49) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 81), (1, 75), (2, 83), (3, 3), (4, 4), (5, 5), (6, 63), (7, 87), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed4c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 81), (1, 75), (2, 83), (3, 3), (4, 4), (5, 5), (6, 63), (7, 87), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed50) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 81), (1, 75), (2, 83), (3, 3), (4, 4), (5, 5), (6, 63), (7, 87), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed55) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10ed05_1 code

theorem block_l10ed05 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ed05 :=
  Rest.liftedBlock (rest_l10ed05 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ed05 x hx)

theorem rest_l10ed84 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ed84 bytes_l10ed84) (entryMap (live .l10ed84))
      6 0x10ed84 bytes_l10ed84 b_l10ed84 := by
  have f0 : InstrSpec 0x10ed84 [0x4C, 0x8B, 0x7C, 0x24, 0x58] (LoadPre 0x10ed84 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10ed84 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed84 15 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10ed84 15 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x10ed84 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10ed89 [0x4C, 0x8B, 0x64, 0x24, 0x60] (LoadPre 0x10ed89 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10ed89 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed89 12 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10ed89 12 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x10ed89 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10ed8e [0x4C, 0x8B, 0x6C, 0x24, 0x68] (LoadPre 0x10ed8e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10ed8e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed8e 13 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x10ed8e 13 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x10ed8e 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10ed93 [0x48, 0x8B, 0x6C, 0x24, 0x70] (LoadPre 0x10ed93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10ed93 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed93 5 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10ed93 5 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x10ed93 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10ed98 [0x8B, 0x7C, 0x24, 0x78] (LoadPre 0x10ed98 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10ed98 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10ed98 7 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x10ed98 7 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r32_m32_low_effect_step 0x10ed98 7 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10ed9c [0xE8, 0xAF, 0x8F, 0x01, 0x00] (PushPre 0x10ed9c 5) (callEffect (fun _ => 0x127d50) 0x10eda1)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10ed9c 0x127d50 0x10eda1).toInstrSpec (call_rel32_effect_step 0x10ed9c 0x18faf (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed89) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed8e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed93) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 59), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed98) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 59), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ed9c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 59), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l10ed84 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ed84 :=
  Rest.liftedBlock (rest_l10ed84 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ed84 x hx)

theorem rest_l10eda1_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x10eda1 bytes_l10eda1) [(0, 0), (1, 90), (2, 64), (3, 3), (4, 4), (5, 5), (6, 88), (7, 86), (8, 84), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      20 0x10ede6 bytes_l10eda1_1 b_l10eda1_1 := by
  have f20 : InstrSpec 0x10ede6 [0x44, 0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x10ede6) (movzxR32R8Effect 0x10ede6 4 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movzxR32R8Effect_footprint 0x10ede6 4 15 0).toInstrSpec (movzx_r32_r8_rex_effect_step 0x10ede6 0x44 (by decide) 0xf8 (by decide)) pre_rip
  have f21 : InstrSpec 0x10edea [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x10edea) (movR64R64Effect 0x10edea 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10edea 0 15).toInstrSpec (mov_r64_r64_effect_step 0x10edea 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10eded [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x10eded) (negR64Effect 0x10eded 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x10eded 0).toInstrSpec (neg_r64_effect_step 0x10eded 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x10edf0 [0x49, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x10edf0) (movR64Imm64Effect 0x10edf0 9 0xfffffffffffff)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x10edf0 9 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x10edf0 0x49 0xb9 (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f24 : InstrSpec 0x10edfa [0x49, 0x21, 0xC1] (fun s => s.RIP = 0x10edfa) (andR64R64Effect 0x10edfa 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10edfa 9 0).toInstrSpec (and_r64_r64_effect_step 0x10edfa 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x10edfd [0x4C, 0x21, 0xCA] (fun s => s.RIP = 0x10edfd) (andR64R64Effect 0x10edfd 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10edfd 2 9).toInstrSpec (and_r64_r64_effect_step 0x10edfd 0x4c 0xca (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10ee00 [0x4C, 0x21, 0xCE] (fun s => s.RIP = 0x10ee00) (andR64R64Effect 0x10ee00 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ee00 6 9).toInstrSpec (and_r64_r64_effect_step 0x10ee00 0x4c 0xce (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x10ee03 [0x4C, 0x21, 0xCF] (fun s => s.RIP = 0x10ee03) (andR64R64Effect 0x10ee03 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ee03 7 9).toInstrSpec (and_r64_r64_effect_step 0x10ee03 0x4c 0xcf (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10ee06 [0x4D, 0x21, 0xC1] (fun s => s.RIP = 0x10ee06) (andR64R64Effect 0x10ee06 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ee06 9 8).toInstrSpec (and_r64_r64_effect_step 0x10ee06 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x10ee09 [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x10ee09) (andR64R64Effect 0x10ee09 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ee09 0 1).toInstrSpec (and_r64_r64_effect_step 0x10ee09 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10ee0c [0x48, 0x89, 0x14, 0x24] (StorePre 0x10ee0c 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10ee0c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10ee0c 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ee0c 2 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10ee0c 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x10ee10 [0x48, 0x89, 0x74, 0x24, 0x08] (StorePre 0x10ee10 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10ee10 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ee10 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ee10 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10ee10 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x10ee15 [0x48, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x10ee15 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10ee15 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ee15 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ee15 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10ee15 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x10ee1a [0x4C, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x10ee1a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10ee1a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ee1a 9 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ee1a 9 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10ee1a 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x10ee1f [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x10ee1f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ee1f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ee1f 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ee1f 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10ee1f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x10ee24 [0x4C, 0x8D, 0x64, 0x24, 0x58] (fun s => s.RIP = 0x10ee24) (leaR64Effect 0x10ee24 12 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x10ee24 12 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (lea_r64_effect_step 0x10ee24 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10ee29 [0x48, 0x89, 0xE2] (fun s => s.RIP = 0x10ee29) (movR64R64Effect 0x10ee29 2 4)
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10ee29 2 4).toInstrSpec (mov_r64_r64_effect_step 0x10ee29 0x48 0xe2 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x10ee2c [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x10ee2c) (movR64R64Effect 0x10ee2c 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10ee2c 7 12).toInstrSpec (mov_r64_r64_effect_step 0x10ee2c 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x10ee2f [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10ee2f) (movR64R64Effect 0x10ee2f 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10ee2f 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10ee2f 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10ee32 [0xE8, 0x89, 0xF6, 0xFF, 0xFF] (PushPre 0x10ee32 5) (callEffect (fun _ => 0x10e4c0) 0x10ee37)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10ee32 0x10e4c0 0x10ee37).toInstrSpec (call_rel32_effect_step 0x10ee32 0xfffff689 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 0), (1, 90), (2, 64), (3, 3), (4, 4), (5, 5), (6, 88), (7, 86), (8, 84), (12, 12), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edea) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 94), (1, 90), (2, 64), (3, 3), (4, 4), (5, 5), (6, 88), (7, 86), (8, 84), (12, 12), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eded) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 96), (1, 90), (2, 64), (3, 3), (4, 4), (5, 5), (6, 88), (7, 86), (8, 84), (12, 12), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edf0) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f23 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 96), (1, 90), (2, 64), (3, 3), (4, 4), (5, 5), (6, 88), (7, 86), (8, 84), (9, 98), (12, 12), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edfa) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f24 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 96), (1, 90), (2, 64), (3, 3), (4, 4), (5, 5), (6, 88), (7, 86), (8, 84), (9, 100), (12, 12), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edfd) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 96), (1, 90), (2, 102), (3, 3), (4, 4), (5, 5), (6, 88), (7, 86), (8, 84), (9, 100), (12, 12), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee00) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f26 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 96), (1, 90), (2, 102), (3, 3), (4, 4), (5, 5), (6, 104), (7, 86), (8, 84), (9, 100), (12, 12), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee03) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f27 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 96), (1, 90), (2, 102), (3, 3), (4, 4), (5, 5), (6, 104), (7, 106), (8, 84), (9, 100), (12, 12), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee06) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f28 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 96), (1, 90), (2, 102), (3, 3), (4, 4), (5, 5), (6, 104), (7, 106), (8, 84), (9, 108), (12, 12), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee09) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 110), (1, 90), (2, 102), (3, 3), (4, 4), (5, 5), (6, 104), (7, 106), (8, 84), (9, 108), (12, 12), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee0c) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 110), (1, 90), (2, 102), (3, 3), (4, 4), (5, 5), (6, 104), (7, 106), (8, 84), (9, 108), (12, 12), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee10) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 110), (1, 90), (2, 102), (3, 3), (4, 4), (5, 5), (6, 104), (7, 106), (8, 84), (9, 108), (12, 12), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee15) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 114) (RestInside.exec (n := 114) (ρ' := [(0, 110), (1, 90), (2, 102), (3, 3), (4, 4), (5, 5), (6, 104), (7, 106), (8, 84), (9, 108), (12, 12), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee1a) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 110), (1, 90), (2, 102), (3, 3), (4, 4), (5, 5), (6, 104), (7, 106), (8, 84), (9, 108), (12, 12), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee1f) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.exec (n := 116) (ρ' := [(0, 110), (1, 90), (2, 102), (3, 3), (4, 4), (5, 5), (6, 104), (7, 106), (8, 84), (9, 108), (12, 12), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee24) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f35 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 110), (1, 90), (2, 102), (3, 3), (4, 4), (5, 5), (6, 104), (7, 106), (8, 84), (9, 108), (12, 117), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee29) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 110), (1, 90), (2, 119), (3, 3), (4, 4), (5, 5), (6, 104), (7, 106), (8, 84), (9, 108), (12, 117), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee2c) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f37 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 110), (1, 90), (2, 119), (3, 3), (4, 4), (5, 5), (6, 104), (7, 121), (8, 84), (9, 108), (12, 117), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee2f) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f38 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 110), (1, 90), (2, 119), (3, 3), (4, 4), (5, 5), (6, 123), (7, 121), (8, 84), (9, 108), (12, 117), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee32) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f39 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 110), (1, 90), (2, 119), (3, 3), (4, 125), (5, 5), (6, 123), (7, 121), (8, 84), (9, 108), (12, 117), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10e4c0) f39 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 127) (by decide) (by decide) rfl rfl

theorem rest_l10eda1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10eda1 bytes_l10eda1) (entryMap (live .l10eda1))
      40 0x10eda1 bytes_l10eda1 b_l10eda1 := by
  have f0 : InstrSpec 0x10eda1 [0x88, 0x04, 0x24] (StorePre 0x10eda1 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10eda1 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10eda1 3 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10eda1 3 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x10eda1 0 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10eda4 [0x48, 0x89, 0xE1] (fun s => s.RIP = 0x10eda4) (movR64R64Effect 0x10eda4 1 4)
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10eda4 1 4).toInstrSpec (mov_r64_r64_effect_step 0x10eda4 0x48 0xe1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10eda7 [0x44, 0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x10eda7 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10eda7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10eda7 5 8 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x10eda7 5 8 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10eda7 0x44 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10edac [0x31, 0xC9] (fun s => s.RIP = 0x10edac) (xorR32R32Effect 0x10edac 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10edac 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x10edac 0xc9 (by decide)) pre_rip
  have f4 : InstrSpec 0x10edae [0x31, 0xD2] (fun s => s.RIP = 0x10edae) (xorR32R32Effect 0x10edae 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10edae 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x10edae 0xd2 (by decide)) pre_rip
  have f5 : InstrSpec 0x10edb0 [0x45, 0x84, 0xC0] (fun s => s.RIP = 0x10edb0) (testR8R8Effect 0x10edb0 3 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10edb0 3 8 8).toInstrSpec (test_r8_r8_rex_effect_step 0x10edb0 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10edb3 [0x49, 0x0F, 0x45, 0xD7] (fun s => s.RIP = 0x10edb3) (atFlags (condHolds 5) (cmovR64R64Effect 0x10edb3 4 2 15))
      [.gpr 2, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x10edb3 4 2 15 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10edb3 5 0x49 (by decide) 0xd7 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x10edb7 [0x31, 0xF6] (fun s => s.RIP = 0x10edb7) (xorR32R32Effect 0x10edb7 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10edb7 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x10edb7 0xf6 (by decide)) pre_rip
  have f8 : InstrSpec 0x10edb9 [0x45, 0x84, 0xC0] (fun s => s.RIP = 0x10edb9) (testR8R8Effect 0x10edb9 3 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10edb9 3 8 8).toInstrSpec (test_r8_r8_rex_effect_step 0x10edb9 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10edbc [0x49, 0x0F, 0x45, 0xF4] (fun s => s.RIP = 0x10edbc) (atFlags (condHolds 5) (cmovR64R64Effect 0x10edbc 4 6 12))
      [.gpr 6, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 6, .rip] :=
    (cmovR64R64Effect_footprint 0x10edbc 4 6 12 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10edbc 5 0x49 (by decide) 0xf4 (by decide) c)) pre_rip
  have f10 : InstrSpec 0x10edc0 [0x31, 0xFF] (fun s => s.RIP = 0x10edc0) (xorR32R32Effect 0x10edc0 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10edc0 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x10edc0 0xff (by decide)) pre_rip
  have f11 : InstrSpec 0x10edc2 [0x45, 0x84, 0xC0] (fun s => s.RIP = 0x10edc2) (testR8R8Effect 0x10edc2 3 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10edc2 3 8 8).toInstrSpec (test_r8_r8_rex_effect_step 0x10edc2 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10edc5 [0x49, 0x0F, 0x45, 0xFD] (fun s => s.RIP = 0x10edc5) (atFlags (condHolds 5) (cmovR64R64Effect 0x10edc5 4 7 13))
      [.gpr 7, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (cmovR64R64Effect_footprint 0x10edc5 4 7 13 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10edc5 5 0x49 (by decide) 0xfd (by decide) c)) pre_rip
  have f13 : InstrSpec 0x10edc9 [0x45, 0x84, 0xC0] (fun s => s.RIP = 0x10edc9) (testR8R8Effect 0x10edc9 3 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10edc9 3 8 8).toInstrSpec (test_r8_r8_rex_effect_step 0x10edc9 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10edcc [0x48, 0x0F, 0x45, 0xCD] (fun s => s.RIP = 0x10edcc) (atFlags (condHolds 5) (cmovR64R64Effect 0x10edcc 4 1 5))
      [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (cmovR64R64Effect_footprint 0x10edcc 4 1 5 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10edcc 5 0x48 (by decide) 0xcd (by decide) c)) pre_rip
  have f15 : InstrSpec 0x10edd0 [0x49, 0x89, 0xC8] (fun s => s.RIP = 0x10edd0) (movR64R64Effect 0x10edd0 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10edd0 8 1).toInstrSpec (mov_r64_r64_effect_step 0x10edd0 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10edd3 [0x49, 0x0F, 0xA4, 0xF8, 0x24] (fun s => s.RIP = 0x10edd3) (shldR64R64Effect 0x10edd3 5 8 7 36)
      [.gpr 8, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10edd3 5 8 7 36).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10edd3 0x49 (by decide) 0xf8 (by decide) 0x24) pre_rip
  have f17 : InstrSpec 0x10edd8 [0x48, 0x0F, 0xA4, 0xF7, 0x18] (fun s => s.RIP = 0x10edd8) (shldR64R64Effect 0x10edd8 5 7 6 24)
      [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10edd8 5 7 6 24).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10edd8 0x48 (by decide) 0xf7 (by decide) 0x18) pre_rip
  have f18 : InstrSpec 0x10eddd [0x48, 0x0F, 0xA4, 0xD6, 0x0C] (fun s => s.RIP = 0x10eddd) (shldR64R64Effect 0x10eddd 5 6 2 12)
      [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x10eddd 5 6 2 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x10eddd 0x48 (by decide) 0xd6 (by decide) 0xc) pre_rip
  have f19 : InstrSpec 0x10ede2 [0x48, 0xC1, 0xE9, 0x10] (fun s => s.RIP = 0x10ede2) (shrR64Effect 0x10ede2 4 1 16)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10ede2 4 1 16).toInstrSpec (shr_r64_imm8_effect_step 0x10ede2 0x48 0xe9 0x10 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eda4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eda7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 56), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edac) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 56), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edae) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 58), (2, 60), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 56), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edb0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 58), (2, 60), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 56), (12, 12), (13, 13), (14, 14), (15, 15), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edb3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 58), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 56), (12, 12), (13, 13), (14, 14), (15, 15), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edb7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 58), (2, 64), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 56), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edb9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 58), (2, 64), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 56), (12, 12), (13, 13), (14, 14), (15, 15), (19, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edbc) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 58), (2, 64), (3, 3), (4, 4), (5, 5), (6, 70), (7, 7), (8, 56), (12, 12), (13, 13), (14, 14), (15, 15), (19, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edc0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 58), (2, 64), (3, 3), (4, 4), (5, 5), (6, 70), (7, 72), (8, 56), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edc2) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 58), (2, 64), (3, 3), (4, 4), (5, 5), (6, 70), (7, 72), (8, 56), (12, 12), (13, 13), (14, 14), (15, 15), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edc5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 58), (2, 64), (3, 3), (4, 4), (5, 5), (6, 70), (7, 76), (8, 56), (12, 12), (13, 13), (14, 14), (15, 15), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edc9) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 58), (2, 64), (3, 3), (4, 4), (5, 5), (6, 70), (7, 76), (8, 56), (12, 12), (13, 13), (14, 14), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edcc) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 80), (2, 64), (3, 3), (4, 4), (5, 5), (6, 70), (7, 76), (8, 56), (12, 12), (13, 13), (14, 14), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edd0) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 80), (2, 64), (3, 3), (4, 4), (5, 5), (6, 70), (7, 76), (8, 82), (12, 12), (13, 13), (14, 14), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edd3) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 80), (2, 64), (3, 3), (4, 4), (5, 5), (6, 70), (7, 76), (8, 84), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10edd8) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 80), (2, 64), (3, 3), (4, 4), (5, 5), (6, 70), (7, 86), (8, 84), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10eddd) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 80), (2, 64), (3, 3), (4, 4), (5, 5), (6, 88), (7, 86), (8, 84), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ede2) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 90), (2, 64), (3, 3), (4, 4), (5, 5), (6, 88), (7, 86), (8, 84), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ede6) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10eda1_1 code

theorem block_l10eda1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10eda1 :=
  Rest.liftedBlock (rest_l10eda1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10eda1 x hx)

theorem rest_l10ee37 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ee37 bytes_l10ee37) (entryMap (live .l10ee37))
      11 0x10ee37 bytes_l10ee37 b_l10ee37 := by
  have f0 : InstrSpec 0x10ee37 [0x44, 0x88, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x10ee37 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10ee37 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x10ee37 8 15 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10ee37 8 15 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10ee37 0x44 (by decide) 7 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10ee3f [0x48, 0x89, 0xE0] (fun s => s.RIP = 0x10ee3f) (movR64R64Effect 0x10ee3f 0 4)
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10ee3f 0 4).toInstrSpec (mov_r64_r64_effect_step 0x10ee3f 0x48 0xe0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10ee42 [0xB9, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ee42) (movR32Imm32Effect 0x10ee42 5 1 0xb)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10ee42 5 1 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x10ee42 0xb9 (by decide) 0xb) pre_rip
  have f3 : InstrSpec 0x10ee47 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x10ee47) (movR64R64Effect 0x10ee47 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10ee47 7 0).toInstrSpec (mov_r64_r64_effect_step 0x10ee47 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10ee4a [0x48, 0xC7, 0xC6, 0x70, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x10ee4a) (movR64Imm32Effect 0x10ee4a 6 0x202b70)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10ee4a 6 0x202b70).toInstrSpec (mov_r64_imm32_effect_step 0x10ee4a 0x48 0xc6 (by decide) (by decide) (by decide) 0x202b70) pre_rip
  have f5 : InstrSpec 0x10ee51 [0xF3, 0x48, 0xA5] (RepPre 0x10ee51 (RepMovsqPre 0x10ee51)) (repMovsqEffect 0x10ee51)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10ee51).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10ee51 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f6 : InstrSpec 0x10ee54 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10ee54) (movR64R64Effect 0x10ee54 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10ee54 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10ee54 0x48 0xdf (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10ee57 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x10ee57) (movR64R64Effect 0x10ee57 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10ee57 6 0).toInstrSpec (mov_r64_r64_effect_step 0x10ee57 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10ee5a [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x10ee5a) (movR64R64Effect 0x10ee5a 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10ee5a 2 12).toInstrSpec (mov_r64_r64_effect_step 0x10ee5a 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10ee5d [0x44, 0x89, 0xF9] (fun s => s.RIP = 0x10ee5d) (movR32R32Effect 0x10ee5d 3 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10ee5d 3 1 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x10ee5d 0x44 0xf9 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10ee60 [0xE8, 0x0B, 0x16, 0x01, 0x00] (PushPre 0x10ee60 5) (callEffect (fun _ => 0x120470) 0x10ee65)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10ee60 0x120470 0x10ee65).toInstrSpec (call_rel32_effect_step 0x10ee60 0x1160b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee3f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee42) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee47) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 54), (1, 56), (3, 3), (4, 4), (5, 5), (7, 58), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee4a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 54), (1, 56), (3, 3), (4, 4), (5, 5), (6, 60), (7, 58), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee51) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee54) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (7, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee57) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 54), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee5a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 54), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee5d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 54), (1, 69), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee60) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 54), (1, 69), (2, 67), (3, 3), (4, 71), (5, 5), (6, 65), (7, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120470) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l10ee37 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ee37 :=
  Rest.liftedBlock (rest_l10ee37 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ee37 x hx)

theorem rest_l10ee65 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ee65 bytes_l10ee65) (entryMap (live .l10ee65))
      9 0x10ee65 bytes_l10ee65 b_l10ee65 := by
  have f0 : InstrSpec 0x10ee65 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10ee65) (movR64R64Effect 0x10ee65 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10ee65 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10ee65 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10ee68 [0x48, 0x81, 0xC4, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ee68) (addR64Imm32Effect 0x10ee68 4 0xb8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x10ee68 4 0xb8).toInstrSpec (add_r64_imm32_effect_step 0x10ee68 0x48 0xc4 0xb8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10ee6f [0x5B] (PopPre 0x10ee6f) (popR64Effect 0x10ee6f 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10ee6f 1 3).toInstrSpec (pop_r64_effect_step 0x10ee6f 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10ee70 [0x41, 0x5C] (PopPre 0x10ee70) (popR64Effect 0x10ee70 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10ee70 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10ee70 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10ee72 [0x41, 0x5D] (PopPre 0x10ee72) (popR64Effect 0x10ee72 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10ee72 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10ee72 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10ee74 [0x41, 0x5E] (PopPre 0x10ee74) (popR64Effect 0x10ee74 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10ee74 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10ee74 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10ee76 [0x41, 0x5F] (PopPre 0x10ee76) (popR64Effect 0x10ee76 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10ee76 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10ee76 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x10ee78 [0x5D] (PopPre 0x10ee78) (popR64Effect 0x10ee78 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10ee78 1 5).toInstrSpec (pop_r64_effect_step 0x10ee78 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x10ee79 [0xC3] (RetPre 0x10ee79) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10ee79).toInstrSpec (ret_effect_step 0x10ee79) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee68) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee6f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee70) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee72) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee74) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee76) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee78) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ee79) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l10ee65 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ee65 :=
  Rest.liftedBlock (rest_l10ee65 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ee65 x hx)

section Steps

variable (code : CodeMap)
    (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64)
    (cf pf af zf sf of : Bool) (df : BitVec 1)
    (xmm0 xmm1 xmm2 xmm3 xmm4 xmm5 xmm6 xmm7 xmm8 xmm9 xmm10 xmm11 xmm12 xmm13 xmm14 xmm15 : BitVec 128)
    (mxcsr : BitVec 32) (st0 st1 st2 st3 st4 st5 st6 st7 : BitVec 80) (fsw : BitVec 16)
    (fcc : BitVec 4) (ftw fcw : BitVec 16) (fpuPtr : BitVec 171) (mem : Ram)

set_option hygiene false in
local notation "args" =>
  (#v[⟨64, rax⟩, ⟨64, rcx⟩, ⟨64, rdx⟩, ⟨64, rbx⟩, ⟨64, rsp⟩, ⟨64, rbp⟩, ⟨64, rsi⟩, ⟨64, rdi⟩, ⟨64, r8⟩, ⟨64, r9⟩, ⟨64, r10⟩, ⟨64, r11⟩, ⟨64, r12⟩, ⟨64, r13⟩, ⟨64, r14⟩, ⟨64, r15⟩] : Vector Value 16) ++
  (#v[.ofBool cf, .ofBool pf, .ofBool af, .ofBool zf, .ofBool sf, .ofBool of, ⟨1, df⟩] : Vector Value 7) ++
  (#v[⟨128, xmm0⟩, ⟨128, xmm1⟩, ⟨128, xmm2⟩, ⟨128, xmm3⟩, ⟨128, xmm4⟩, ⟨128, xmm5⟩, ⟨128, xmm6⟩, ⟨128, xmm7⟩, ⟨128, xmm8⟩, ⟨128, xmm9⟩, ⟨128, xmm10⟩, ⟨128, xmm11⟩, ⟨128, xmm12⟩, ⟨128, xmm13⟩, ⟨128, xmm14⟩, ⟨128, xmm15⟩, ⟨32, mxcsr⟩, ⟨80, st0⟩, ⟨80, st1⟩, ⟨80, st2⟩, ⟨80, st3⟩, ⟨80, st4⟩, ⟨80, st5⟩, ⟨80, st6⟩, ⟨80, st7⟩, ⟨16, fsw⟩, ⟨4, fcc⟩, ⟨16, ftw⟩, ⟨16, fcw⟩, ⟨171, fpuPtr⟩] : Vector Value 30)

theorem_by block_l10ece0_eval :
    program.runBlock (dialect code) ⟨.l10ece0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10ed05_eval :
    program.runBlock (dialect code) ⟨.l10ed05, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10ed84_eval :
    program.runBlock (dialect code) ⟨.l10ed84, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10eda1_eval :
    program.runBlock (dialect code) ⟨.l10eda1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10ee37_eval :
    program.runBlock (dialect code) ⟨.l10ee37, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10ee65_eval :
    program.runBlock (dialect code) ⟨.l10ee65, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
