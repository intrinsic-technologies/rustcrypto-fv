import K256.Proofs.Signing.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Signing.LIR.Generated.Values

namespace K256.Proofs.Signing.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR K256.Proofs.Verify.LIR

theorem rest_l115408 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x115408 bytes_l115408) (entryMap (live .l115408))
      14 0x115408 bytes_l115408 b_l115408 := by
  have f0 : InstrSpec 0x115408 [0x48, 0x83, 0xEC, 0x18] (fun s => s.RIP = 0x115408) (subR64Imm8Effect 0x115408 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x115408 4 0x18).toInstrSpec (sub_r64_imm8_effect_step 0x115408 0x48 0xec 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11540c [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x11540c) (movR64R64Effect 0x11540c 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11540c 0 9).toInstrSpec (mov_r64_r64_effect_step 0x11540c 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11540f [0x4D, 0x89, 0xC2] (fun s => s.RIP = 0x11540f) (movR64R64Effect 0x11540f 10 8)
      [.gpr 8] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x11540f 10 8).toInstrSpec (mov_r64_r64_effect_step 0x11540f 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x115412 [0x49, 0x89, 0xC9] (fun s => s.RIP = 0x115412) (movR64R64Effect 0x115412 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x115412 9 1).toInstrSpec (mov_r64_r64_effect_step 0x115412 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x115415 [0x4C, 0x8D, 0x44, 0x24, 0x08] (fun s => s.RIP = 0x115415) (leaR64Effect 0x115415 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x115415 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x115415 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11541a [0x49, 0x89, 0x30] (StorePre 0x11541a 3 (fun s => AddrMode.addr (.base 8 .none) s (0x11541a + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11541a 6 (.base 8 .none))
      [.gpr 6, .gpr 8] [] [.rip] :=
    (movM64R64Effect_footprint 0x11541a 6 (.base 8 .none)).toInstrSpec (mov_m64_r64_effect_step 0x11541a 0x49 (by decide) 6 (.base 8 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x11541d [0x48, 0x8D, 0x4C, 0x24, 0x10] (fun s => s.RIP = 0x11541d) (leaR64Effect 0x11541d 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x11541d 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x11541d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x115422 [0x48, 0x89, 0x11] (StorePre 0x115422 3 (fun s => AddrMode.addr (.base 1 .none) s (0x115422 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x115422 2 (.base 1 .none))
      [.gpr 2, .gpr 1] [] [.rip] :=
    (movM64R64Effect_footprint 0x115422 2 (.base 1 .none)).toInstrSpec (mov_m64_r64_effect_step 0x115422 0x48 (by decide) 2 (.base 1 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x115425 [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x115425) (movR64R64Effect 0x115425 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x115425 6 8).toInstrSpec (mov_r64_r64_effect_step 0x115425 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x115428 [0x48, 0xC7, 0xC2, 0x98, 0x2E, 0x20, 0x00] (fun s => s.RIP = 0x115428) (movR64Imm32Effect 0x115428 2 0x202e98)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x115428 2 0x202e98).toInstrSpec (mov_r64_imm32_effect_step 0x115428 0x48 0xc2 (by decide) (by decide) (by decide) 0x202e98) pre_rip
  have f10 : InstrSpec 0x11542f [0x49, 0xC7, 0xC0, 0x98, 0x2E, 0x20, 0x00] (fun s => s.RIP = 0x11542f) (movR64Imm32Effect 0x11542f 8 0x202e98)
      [] [] [.reg 8, .rip] :=
    (movR64Imm32Effect_footprint 0x11542f 8 0x202e98).toInstrSpec (mov_r64_imm32_effect_step 0x11542f 0x49 0xc0 (by decide) (by decide) (by decide) 0x202e98) pre_rip
  have f11 : InstrSpec 0x115436 [0x50] (PushPre 0x115436 1) (pushR64Effect 0x115436 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x115436 1 0).toInstrSpec (push_r64_effect_step 0x115436 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x115437 [0x41, 0x52] (PushPre 0x115437 2) (pushR64Effect 0x115437 2 10)
      [.gpr 4, .gpr 10] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x115437 2 10).toInstrSpec (push_r64_rex_effect_step 0x115437 0x41 0x52 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f13 : InstrSpec 0x115439 [0xE8, 0x1F, 0x42, 0x01, 0x00] (PushPre 0x115439 5) (callEffect (fun _ => 0x12965d) 0x11543e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x115439 0x12965d 0x11543e).toInstrSpec (call_rel32_effect_step 0x115439 0x1421f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x11540c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]) (p' := 0x11540f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 57)]) (p' := 0x115412) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 59), (10, 57)]) (p' := 0x115415) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 61), (9, 59), (10, 57)]) (p' := 0x11541a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 61), (9, 59), (10, 57)]) (p' := 0x11541d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 55), (1, 64), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 61), (9, 59), (10, 57)]) (p' := 0x115422) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 64), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 61), (9, 59), (10, 57)]) (p' := 0x115425) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 64), (2, 2), (4, 53), (5, 5), (6, 67), (7, 7), (8, 61), (9, 59), (10, 57)]) (p' := 0x115428) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 64), (2, 69), (4, 53), (5, 5), (6, 67), (7, 7), (8, 61), (9, 59), (10, 57)]) (p' := 0x11542f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 64), (2, 69), (4, 53), (5, 5), (6, 67), (7, 7), (8, 71), (9, 59), (10, 57)]) (p' := 0x115436) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 64), (2, 69), (4, 73), (5, 5), (6, 67), (7, 7), (8, 71), (9, 59), (10, 57)]) (p' := 0x115437) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 64), (2, 69), (4, 75), (5, 5), (6, 67), (7, 7), (8, 71), (9, 59), (10, 57)]) (p' := 0x115439) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 55), (1, 64), (2, 69), (4, 77), (5, 5), (6, 67), (7, 7), (8, 71), (9, 59), (10, 57)]) (p' := 0x12965d) f13 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 79) (by decide) (by decide) rfl rfl

theorem block_l115408 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l115408 :=
  Rest.liftedBlock (rest_l115408 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l115408 x hx)

theorem rest_l11543e_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x11543e bytes_l11543e) [(0, 125), (1, 121), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (19, 126), (22, 22), (39, 39), (50, 50), (51, 51)]
      7 0x1154d7 bytes_l11543e_2 b_l11543e_2 := by
  have f40 : InstrSpec 0x1154d7 [0x0F, 0x94, 0xC0] (fun s => s.RIP = 0x1154d7) (atFlags (condHolds 4) (setccR8Effect 0x1154d7 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x1154d7 3 0 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1154d7 4 0xc0 (by decide) (by decide) c)) pre_rip
  have f41 : InstrSpec 0x1154da [0x48, 0xB9, 0x2E, 0xFC, 0xFF, 0xFF, 0xFE, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x1154da) (movR64Imm64Effect 0x1154da 1 0xffffefffffc2e)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x1154da 1 0xffffefffffc2e).toInstrSpec (mov_r64_imm64_effect_step 0x1154da 0x48 0xb9 (by decide) (by decide) 0xffffefffffc2e) pre_rip
  have f42 : InstrSpec 0x1154e4 [0x49, 0x39, 0xCF] (fun s => s.RIP = 0x1154e4) (cmpR64R64Effect 0x1154e4 15 1)
      [.gpr 15, .gpr 1] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1154e4 15 1).toInstrSpec (cmp_r64_r64_effect_step 0x1154e4 0x49 0xcf (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x1154e7 [0x0F, 0x97, 0xC1] (fun s => s.RIP = 0x1154e7) (atFlags (condHolds 7) (setccR8Effect 0x1154e7 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x1154e7 3 1 7).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1154e7 7 0xc1 (by decide) (by decide) c)) pre_rip
  have f44 : InstrSpec 0x1154ea [0x20, 0xC1] (fun s => s.RIP = 0x1154ea) (andR8R8Effect 0x1154ea 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR8R8Effect_footprint 0x1154ea 2 1 0).toInstrSpec (and_r8_r8_effect_step 0x1154ea 0xc1 (by decide) (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x1154ec [0x0F, 0xB6, 0xF9] (fun s => s.RIP = 0x1154ec) (movzxR32R8Effect 0x1154ec 3 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x1154ec 3 7 1).toInstrSpec (movzx_r32_r8_effect_step 0x1154ec 0xf9 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x1154ef [0xE8, 0x5C, 0x28, 0x01, 0x00] (PushPre 0x1154ef 5) (callEffect (fun _ => 0x127d50) 0x1154f4)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1154ef 0x127d50 0x1154f4).toInstrSpec (call_rel32_effect_step 0x1154ef 0x1285c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 128), (1, 121), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (19, 126), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154da) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f41 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 128), (1, 130), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (19, 126), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154e4) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f42 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 133) f42 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 134) (ρ' := [(0, 128), (1, 130), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (16, 132), (19, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154e7) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f43 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 128), (1, 135), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (16, 132), (19, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154ea) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f44 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 128), (1, 137), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154ec) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f45 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 128), (1, 137), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 139), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154ef) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f46 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 128), (1, 137), (2, 2), (3, 99), (4, 141), (5, 103), (6, 6), (7, 139), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f46 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 143) (by decide) (by decide) rfl rfl

theorem rest_l11543e_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x11543e bytes_l11543e) [(0, 86), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 84), (14, 82), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      27 0x115482 bytes_l11543e_1 b_l11543e_1 := by
  have f20 : InstrSpec 0x115482 [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x115482 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x115482 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115482 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x115482 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x115482 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x115487 [0x4C, 0x8B, 0x66, 0x10] (LoadPre 0x115487 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x115487 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x115487 12 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x115487 12 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x115487 0x4c (by decide) 4 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x11548b [0x49, 0x0F, 0xCC] (fun s => s.RIP = 0x11548b) (bswapR64Effect 0x11548b 3 12)
      [.gpr 12] [] [.reg 12, .rip] :=
    (bswapR64Effect_footprint 0x11548b 3 12).toInstrSpec (bswap_r64_effect_step 0x11548b 0x49 (by decide) 0xcc (by decide)) pre_rip
  have f23 : InstrSpec 0x11548e [0x4C, 0x8B, 0x7E, 0x18] (LoadPre 0x11548e (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x11548e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11548e 15 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x11548e 15 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x11548e 0x4c (by decide) 7 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x115492 [0x49, 0x0F, 0xCF] (fun s => s.RIP = 0x115492) (bswapR64Effect 0x115492 3 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (bswapR64Effect_footprint 0x115492 3 15).toInstrSpec (bswap_r64_effect_step 0x115492 0x49 (by decide) 0xcf (by decide)) pre_rip
  have f25 : InstrSpec 0x115495 [0x4C, 0x89, 0xF3] (fun s => s.RIP = 0x115495) (movR64R64Effect 0x115495 3 14)
      [.gpr 14] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x115495 3 14).toInstrSpec (mov_r64_r64_effect_step 0x115495 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x115498 [0x4C, 0x0F, 0xA4, 0xEB, 0x24] (fun s => s.RIP = 0x115498) (shldR64R64Effect 0x115498 5 3 13 36)
      [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x115498 5 3 13 36).toInstrSpec (shld_r64_r64_imm8_effect_step 0x115498 0x4c (by decide) 0xeb (by decide) 0x24) pre_rip
  have f27 : InstrSpec 0x11549d [0x4D, 0x0F, 0xA4, 0xE5, 0x18] (fun s => s.RIP = 0x11549d) (shldR64R64Effect 0x11549d 5 13 12 24)
      [.gpr 13, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x11549d 5 13 12 24).toInstrSpec (shld_r64_r64_imm8_effect_step 0x11549d 0x4d (by decide) 0xe5 (by decide) 0x18) pre_rip
  have f28 : InstrSpec 0x1154a2 [0x48, 0xBD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x1154a2) (movR64Imm64Effect 0x1154a2 5 0xfffffffffffff)
      [] [] [.reg 5, .rip] :=
    (movR64Imm64Effect_footprint 0x1154a2 5 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x1154a2 0x48 0xbd (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f29 : InstrSpec 0x1154ac [0x4D, 0x0F, 0xA4, 0xFC, 0x0C] (fun s => s.RIP = 0x1154ac) (shldR64R64Effect 0x1154ac 5 12 15 12)
      [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1154ac 5 12 15 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1154ac 0x4d (by decide) 0xfc (by decide) 0xc) pre_rip
  have f30 : InstrSpec 0x1154b1 [0x49, 0x21, 0xEF] (fun s => s.RIP = 0x1154b1) (andR64R64Effect 0x1154b1 15 5)
      [.gpr 15, .gpr 5] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1154b1 15 5).toInstrSpec (and_r64_r64_effect_step 0x1154b1 0x49 0xef (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x1154b4 [0x49, 0x21, 0xEC] (fun s => s.RIP = 0x1154b4) (andR64R64Effect 0x1154b4 12 5)
      [.gpr 12, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1154b4 12 5).toInstrSpec (and_r64_r64_effect_step 0x1154b4 0x49 0xec (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x1154b7 [0x49, 0xC1, 0xEE, 0x10] (fun s => s.RIP = 0x1154b7) (shrR64Effect 0x1154b7 4 14 16)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64Effect_footprint 0x1154b7 4 14 16).toInstrSpec (shr_r64_imm8_effect_step 0x1154b7 0x49 0xee 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x1154bb [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x1154bb) (movR64R64Effect 0x1154bb 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1154bb 0 13).toInstrSpec (mov_r64_r64_effect_step 0x1154bb 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x1154be [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x1154be) (andR64R64Effect 0x1154be 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1154be 0 3).toInstrSpec (and_r64_r64_effect_step 0x1154be 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x1154c1 [0x4C, 0x21, 0xE0] (fun s => s.RIP = 0x1154c1) (andR64R64Effect 0x1154c1 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1154c1 0 12).toInstrSpec (and_r64_r64_effect_step 0x1154c1 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x1154c4 [0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x1154c4) (movR64Imm64Effect 0x1154c4 1 0xffffffffffff)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x1154c4 1 0xffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x1154c4 0x48 0xb9 (by decide) (by decide) 0xffffffffffff) pre_rip
  have f37 : InstrSpec 0x1154ce [0x4C, 0x31, 0xF1] (fun s => s.RIP = 0x1154ce) (xorR64R64Effect 0x1154ce 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1154ce 1 14).toInstrSpec (xor_r64_r64_effect_step 0x1154ce 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x1154d1 [0x48, 0x31, 0xE8] (fun s => s.RIP = 0x1154d1) (xorR64R64Effect 0x1154d1 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1154d1 0 5).toInstrSpec (xor_r64_r64_effect_step 0x1154d1 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x1154d4 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x1154d4) (orR64R64Effect 0x1154d4 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1154d4 0 1).toInstrSpec (or_r64_r64_effect_step 0x1154d4 0x48 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 86), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 84), (14, 82), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115487) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f21 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 86), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 84), (14, 82), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11548b) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f22 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 86), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 91), (13, 84), (14, 82), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11548e) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f23 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 86), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 91), (13, 84), (14, 82), (15, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115492) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f24 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 86), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 91), (13, 84), (14, 82), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115495) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f25 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 86), (2, 2), (3, 97), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 91), (13, 84), (14, 82), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115498) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f26 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 86), (2, 2), (3, 99), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 91), (13, 84), (14, 82), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11549d) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f27 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 86), (2, 2), (3, 99), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 91), (13, 101), (14, 82), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154a2) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f28 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 86), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 91), (13, 101), (14, 82), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154ac) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f29 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 86), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 105), (13, 101), (14, 82), (15, 95), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154b1) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f30 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 86), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 105), (13, 101), (14, 82), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154b4) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f31 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 86), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 82), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154b7) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f32 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 86), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154bb) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f33 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 113), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154be) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f34 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 115), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154c1) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f35 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 117), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154c4) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f36 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 117), (1, 119), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154ce) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f37 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 117), (1, 121), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154d1) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f38 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 123), (1, 121), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154d4) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f39 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 126) f39 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 127) (ρ' := [(0, 125), (1, 121), (2, 2), (3, 99), (4, 66), (5, 103), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (19, 126), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154d7) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11543e_2 code

theorem rest_l11543e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11543e bytes_l11543e) (entryMap (live .l11543e))
      47 0x11543e bytes_l11543e b_l11543e := by
  have f0 : InstrSpec 0x11543e [0x66, 0x90] (fun s => s.RIP = 0x11543e) (fun _ => nopEffect 0x11543e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x11543e 2).toInstrSpec (nop_66_effect_step 0x11543e) pre_rip
  have f1 : InstrSpec 0x115440 [0x55] (PushPre 0x115440 1) (pushR64Effect 0x115440 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x115440 1 5).toInstrSpec (push_r64_effect_step 0x115440 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x115441 [0x41, 0x57] (PushPre 0x115441 2) (pushR64Effect 0x115441 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x115441 2 15).toInstrSpec (push_r64_rex_effect_step 0x115441 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x115443 [0x41, 0x56] (PushPre 0x115443 2) (pushR64Effect 0x115443 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x115443 2 14).toInstrSpec (push_r64_rex_effect_step 0x115443 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x115445 [0x41, 0x55] (PushPre 0x115445 2) (pushR64Effect 0x115445 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x115445 2 13).toInstrSpec (push_r64_rex_effect_step 0x115445 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x115447 [0x41, 0x54] (PushPre 0x115447 2) (pushR64Effect 0x115447 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x115447 2 12).toInstrSpec (push_r64_rex_effect_step 0x115447 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x115449 [0x53] (PushPre 0x115449 1) (pushR64Effect 0x115449 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x115449 1 3).toInstrSpec (push_r64_effect_step 0x115449 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x11544a [0x48, 0x81, 0xEC, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11544a) (subR64Imm32Effect 0x11544a 4 0x98)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x11544a 4 0x98).toInstrSpec (sub_r64_imm32_effect_step 0x11544a 0x48 0xec 0x98 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x115451 [0x48, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x115451 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x115451 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115451 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x115451 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x115451 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x115456 [0x48, 0x8B, 0x46, 0x20] (LoadPre 0x115456 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x115456 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x115456 0 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x115456 0 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x115456 0x48 (by decide) 0 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x11545a [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x11545a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11545a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11545a 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11545a 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x11545a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x11545f [0x48, 0x8B, 0x46, 0x28] (LoadPre 0x11545f (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x11545f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11545f 0 (.base 6 (.d8 0x28)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11545f 0 (.base 6 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x11545f 0x48 (by decide) 0 (.base 6 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x115463 [0x48, 0x89, 0x44, 0x24, 0x70] (StorePre 0x115463 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x115463 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115463 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x115463 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x115463 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x115468 [0x48, 0x8B, 0x46, 0x30] (LoadPre 0x115468 (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x115468 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x115468 0 (.base 6 (.d8 0x30)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x115468 0 (.base 6 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x115468 0x48 (by decide) 0 (.base 6 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x11546c [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x11546c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11546c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11546c 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11546c 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x11546c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x115471 [0x4C, 0x8B, 0x36] (LoadPre 0x115471 (fun s => AddrMode.addr (.base 6 .none) s (0x115471 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x115471 14 (.base 6 .none))
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x115471 14 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x115471 0x4c (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x115474 [0x4C, 0x8B, 0x6E, 0x08] (LoadPre 0x115474 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x115474 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x115474 13 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x115474 13 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x115474 0x4c (by decide) 5 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x115478 [0x49, 0x0F, 0xCE] (fun s => s.RIP = 0x115478) (bswapR64Effect 0x115478 3 14)
      [.gpr 14] [] [.reg 14, .rip] :=
    (bswapR64Effect_footprint 0x115478 3 14).toInstrSpec (bswap_r64_effect_step 0x115478 0x49 (by decide) 0xce (by decide)) pre_rip
  have f18 : InstrSpec 0x11547b [0x49, 0x0F, 0xCD] (fun s => s.RIP = 0x11547b) (bswapR64Effect 0x11547b 3 13)
      [.gpr 13] [] [.reg 13, .rip] :=
    (bswapR64Effect_footprint 0x11547b 3 13).toInstrSpec (bswap_r64_effect_step 0x11547b 0x49 (by decide) 0xcd (by decide)) pre_rip
  have f19 : InstrSpec 0x11547e [0x48, 0x8B, 0x46, 0x38] (LoadPre 0x11547e (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x11547e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11547e 0 (.base 6 (.d8 0x38)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11547e 0 (.base 6 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x11547e 0x48 (by decide) 0 (.base 6 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115440) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115441) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115443) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115445) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115447) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 2), (3, 3), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115449) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 2), (3, 3), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11544a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115451) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115456) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11545a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11545f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115463) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115468) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11546c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115471) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 75), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 78), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115474) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 75), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 80), (14, 78), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115478) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f17 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 75), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 80), (14, 82), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11547b) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f18 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 75), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 84), (14, 82), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11547e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 86), (2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 84), (14, 82), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115482) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11543e_1 code

theorem block_l11543e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11543e :=
  Rest.liftedBlock (rest_l11543e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11543e x hx)

theorem rest_l1154f4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1154f4 bytes_l1154f4) (entryMap (live .l1154f4))
      4 0x1154f4 bytes_l1154f4 b_l1154f4 := by
  have f0 : InstrSpec 0x1154f4 [0xF6, 0xD0] (fun s => s.RIP = 0x1154f4) (notR8Effect 0x1154f4 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x1154f4 2 0).toInstrSpec (not_r8_effect_step 0x1154f4 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1154f6 [0x24, 0x01] (fun s => s.RIP = 0x1154f6) (andAlImm8Effect 0x1154f6 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x1154f6 0x1).toInstrSpec (and_al_imm8_effect_step 0x1154f6 0x1) pre_rip
  have f2 : InstrSpec 0x1154f8 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x1154f8) (movzxR32R8Effect 0x1154f8 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x1154f8 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x1154f8 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1154fb [0xE8, 0x50, 0x28, 0x01, 0x00] (PushPre 0x1154fb 5) (callEffect (fun _ => 0x127d50) 0x115500)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1154fb 0x127d50 0x115500).toInstrSpec (call_rel32_effect_step 0x1154fb 0x12850 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154f6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154f8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1154fb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1154f4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1154f4 :=
  Rest.liftedBlock (rest_l1154f4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1154f4 x hx)

theorem rest_l115500 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x115500 bytes_l115500) (entryMap (live .l115500))
      2 0x115500 bytes_l115500 b_l115500 := by
  have f0 : InstrSpec 0x115500 [0x3C, 0x01] (fun s => s.RIP = 0x115500) (cmpAlImm8Effect 0x115500 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x115500 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x115500 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115502) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x115502 5 0x222) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l115500 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l115500 :=
  Rest.liftedBlock (rest_l115500 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l115500 x hx)

theorem rest_l115508 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x115508 bytes_l115508) (entryMap (live .l115508))
      12 0x115508 bytes_l115508 b_l115508 := by
  have f0 : InstrSpec 0x115508 [0x88, 0x44, 0x24, 0x0F] (StorePre 0x115508 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x115508 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x115508 4 0 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x115508 4 0 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_effect_step 0x115508 0 (by decide) (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11550c [0x49, 0x21, 0xED] (fun s => s.RIP = 0x11550c) (andR64R64Effect 0x11550c 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11550c 13 5).toInstrSpec (and_r64_r64_effect_step 0x11550c 0x49 0xed (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11550f [0x48, 0x21, 0xEB] (fun s => s.RIP = 0x11550f) (andR64R64Effect 0x11550f 3 5)
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11550f 3 5).toInstrSpec (and_r64_r64_effect_step 0x11550f 0x48 0xeb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x115512 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x115512) (movR64R64Effect 0x115512 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x115512 0 3).toInstrSpec (mov_r64_r64_effect_step 0x115512 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x115515 [0x4C, 0x09, 0xF0] (fun s => s.RIP = 0x115515) (orR64R64Effect 0x115515 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x115515 0 14).toInstrSpec (or_r64_r64_effect_step 0x115515 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x115518 [0x4C, 0x89, 0xF9] (fun s => s.RIP = 0x115518) (movR64R64Effect 0x115518 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x115518 1 15).toInstrSpec (mov_r64_r64_effect_step 0x115518 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11551b [0x4C, 0x09, 0xE9] (fun s => s.RIP = 0x11551b) (orR64R64Effect 0x11551b 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11551b 1 13).toInstrSpec (or_r64_r64_effect_step 0x11551b 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11551e [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x11551e) (orR64R64Effect 0x11551e 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11551e 1 0).toInstrSpec (or_r64_r64_effect_step 0x11551e 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x115521 [0x31, 0xFF] (fun s => s.RIP = 0x115521) (xorR32R32Effect 0x115521 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x115521 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x115521 0xff (by decide)) pre_rip
  have f9 : InstrSpec 0x115523 [0x4C, 0x09, 0xE1] (fun s => s.RIP = 0x115523) (orR64R64Effect 0x115523 1 12)
      [.gpr 1, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x115523 1 12).toInstrSpec (or_r64_r64_effect_step 0x115523 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x115526 [0x40, 0x0F, 0x94, 0xC7] (fun s => s.RIP = 0x115526) (atFlags (condHolds 4) (setccR8Effect 0x115526 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x115526 4 7 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x115526 4 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f11 : InstrSpec 0x11552a [0xE8, 0x21, 0x28, 0x01, 0x00] (PushPre 0x11552a 5) (callEffect (fun _ => 0x127d50) 0x11552f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11552a 0x127d50 0x11552f).toInstrSpec (call_rel32_effect_step 0x11552a 0x12821 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11550c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11550f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (3, 56), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115512) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (2, 2), (3, 56), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115515) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (2, 2), (3, 56), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115518) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 62), (2, 2), (3, 56), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11551b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 60), (1, 64), (2, 2), (3, 56), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11551e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 60), (1, 66), (2, 2), (3, 56), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115521) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 60), (1, 66), (2, 2), (3, 56), (4, 4), (5, 5), (6, 6), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115523) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f9 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 60), (1, 70), (2, 2), (3, 56), (4, 4), (5, 5), (6, 6), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115526) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 60), (1, 70), (2, 2), (3, 56), (4, 4), (5, 5), (6, 6), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11552a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 60), (1, 70), (2, 2), (3, 56), (4, 75), (5, 5), (6, 6), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l115508 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l115508 :=
  Rest.liftedBlock (rest_l115508 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l115508 x hx)

theorem rest_l11552f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11552f bytes_l11552f) (entryMap (live .l11552f))
      2 0x11552f bytes_l11552f b_l11552f := by
  have f0 : InstrSpec 0x11552f [0x84, 0xC0] (fun s => s.RIP = 0x11552f) (testR8R8Effect 0x11552f 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11552f 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11552f 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115531) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x115531 5 0x1f3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11552f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11552f :=
  Rest.liftedBlock (rest_l11552f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11552f x hx)

theorem rest_l115537_2 [Bindings] (code : CodeMap) :
    Rest (n := 126) code lifted (codeRange 0x115537 bytes_l115537) [(1, 124), (2, 116), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      15 0x1155db bytes_l115537_2 b_l115537_2 := by
  have f40 : InstrSpec 0x1155db [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x1155db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1155db + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1155db 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1155db 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1155db 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f41 : InstrSpec 0x1155e0 [0x31, 0xC9] (fun s => s.RIP = 0x1155e0) (xorR32R32Effect 0x1155e0 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1155e0 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x1155e0 0xc9 (by decide)) pre_rip
  have f42 : InstrSpec 0x1155e2 [0x48, 0x2B, 0x4C, 0x24, 0x18] (LoadPre 0x1155e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1155e2 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1155e2 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x1155e2 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (sub_r64_m64_effect_step 0x1155e2 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x1155e7 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x1155e7) (sarR64Effect 0x1155e7 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x1155e7 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x1155e7 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x1155eb [0x4C, 0x01, 0xE9] (fun s => s.RIP = 0x1155eb) (addR64R64Effect 0x1155eb 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1155eb 1 13).toInstrSpec (add_r64_r64_effect_step 0x1155eb 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x1155ee [0x48, 0xFF, 0xC1] (fun s => s.RIP = 0x1155ee) (incR64Effect 0x1155ee 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (incR64Effect_footprint 0x1155ee 1).toInstrSpec (inc_r64_effect_step 0x1155ee 0x48 0xc1 (by decide) (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x1155f1 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x1155f1) (movR64R64Effect 0x1155f1 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1155f1 2 13).toInstrSpec (mov_r64_r64_effect_step 0x1155f1 0x4c 0xea (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x1155f4 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x1155f4) (notR64Effect 0x1155f4 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x1155f4 2).toInstrSpec (not_r64_effect_step 0x1155f4 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x1155f7 [0x48, 0x09, 0xCA] (fun s => s.RIP = 0x1155f7) (orR64R64Effect 0x1155f7 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1155f7 2 1).toInstrSpec (or_r64_r64_effect_step 0x1155f7 0x48 0xca (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x1155fa [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x1155fa) (shrR64Effect 0x1155fa 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x1155fa 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x1155fa 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x1155fe [0x48, 0x89, 0x54, 0x24, 0x18] (StorePre 0x1155fe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1155fe + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1155fe 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1155fe 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1155fe 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f51 : InstrSpec 0x115603 [0x0F, 0xB6, 0x44, 0x24, 0x18] (LoadPre 0x115603 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x115603 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x115603 5 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x115603 5 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (movzx_r32_m8_effect_step 0x115603 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f52 : InstrSpec 0x115608 [0x24, 0x01] (fun s => s.RIP = 0x115608) (andAlImm8Effect 0x115608 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x115608 0x1).toInstrSpec (and_al_imm8_effect_step 0x115608 0x1) pre_rip
  have f53 : InstrSpec 0x11560a [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x11560a) (movzxR32R8Effect 0x11560a 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x11560a 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x11560a 0xf8 (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x11560d [0xE8, 0x3E, 0x27, 0x01, 0x00] (PushPre 0x11560d 5) (callEffect (fun _ => 0x127d50) 0x115612)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11560d 0x127d50 0x115612).toInstrSpec (call_rel32_effect_step 0x11560d 0x1273e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 126) (RestInside.exec (n := 126) (ρ' := [(1, 124), (2, 116), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155e0) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f41 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(1, 127), (2, 116), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155e2) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f42 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(1, 129), (2, 116), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155e7) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f43 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(1, 131), (2, 116), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155eb) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f44 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(1, 133), (2, 116), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155ee) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f45 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(1, 135), (2, 116), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155f1) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f46 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(1, 135), (2, 137), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155f4) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f47 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(1, 135), (2, 139), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155f7) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f48 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(1, 135), (2, 141), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155fa) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f49 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(1, 135), (2, 143), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155fe) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.exec (n := 145) (ρ' := [(1, 135), (2, 143), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115603) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f51 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 146), (1, 135), (2, 143), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115608) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f52 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 148), (1, 135), (2, 143), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11560a) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f53 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 148), (1, 135), (2, 143), (3, 71), (4, 4), (5, 63), (6, 6), (7, 150), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11560d) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f54 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 148), (1, 135), (2, 143), (3, 71), (4, 152), (5, 63), (6, 6), (7, 150), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f54 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 154) (by decide) (by decide) rfl rfl

theorem rest_l115537_1 [Bindings] (code : CodeMap) :
    Rest (n := 87) code lifted (codeRange 0x115537 bytes_l115537) [(1, 83), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      35 0x11558f bytes_l115537_1 b_l115537_1 := by
  have f20 : InstrSpec 0x11558f [0x31, 0xC9] (fun s => s.RIP = 0x11558f) (xorR32R32Effect 0x11558f 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11558f 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x11558f 0xc9 (by decide)) pre_rip
  have f21 : InstrSpec 0x115591 [0x48, 0x2B, 0x4C, 0x24, 0x18] (LoadPre 0x115591 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x115591 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x115591 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x115591 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (sub_r64_m64_effect_step 0x115591 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x115596 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x115596) (sarR64Effect 0x115596 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x115596 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x115596 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x11559a [0x48, 0xBA, 0xC5, 0x5F, 0xB7, 0x50, 0x19, 0x23, 0x51, 0x45] (fun s => s.RIP = 0x11559a) (movR64Imm64Effect 0x11559a 2 0x4551231950b75fc5)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x11559a 2 0x4551231950b75fc5).toInstrSpec (mov_r64_imm64_effect_step 0x11559a 0x48 0xba (by decide) (by decide) 0x4551231950b75fc5) pre_rip
  have f24 : InstrSpec 0x1155a4 [0x4C, 0x01, 0xF2] (fun s => s.RIP = 0x1155a4) (addR64R64Effect 0x1155a4 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1155a4 2 14).toInstrSpec (add_r64_r64_effect_step 0x1155a4 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x1155a7 [0x48, 0x01, 0xCA] (fun s => s.RIP = 0x1155a7) (addR64R64Effect 0x1155a7 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1155a7 2 1).toInstrSpec (add_r64_r64_effect_step 0x1155a7 0x48 0xca (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x1155aa [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x1155aa) (movR64R64Effect 0x1155aa 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1155aa 1 14).toInstrSpec (mov_r64_r64_effect_step 0x1155aa 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x1155ad [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x1155ad) (notR64Effect 0x1155ad 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x1155ad 1).toInstrSpec (not_r64_effect_step 0x1155ad 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x1155b0 [0x48, 0x09, 0xD1] (fun s => s.RIP = 0x1155b0) (orR64R64Effect 0x1155b0 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1155b0 1 2).toInstrSpec (or_r64_r64_effect_step 0x1155b0 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x1155b3 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x1155b3) (shrR64Effect 0x1155b3 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1155b3 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x1155b3 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x1155b7 [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x1155b7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1155b7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1155b7 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1155b7 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1155b7 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x1155bc [0x31, 0xC9] (fun s => s.RIP = 0x1155bc) (xorR32R32Effect 0x1155bc 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1155bc 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x1155bc 0xc9 (by decide)) pre_rip
  have f32 : InstrSpec 0x1155be [0x48, 0x2B, 0x4C, 0x24, 0x18] (LoadPre 0x1155be (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1155be + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1155be 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x1155be 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (sub_r64_m64_effect_step 0x1155be 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x1155c3 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x1155c3) (sarR64Effect 0x1155c3 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x1155c3 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x1155c3 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x1155c7 [0x48, 0x89, 0xEA] (fun s => s.RIP = 0x1155c7) (movR64R64Effect 0x1155c7 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1155c7 2 5).toInstrSpec (mov_r64_r64_effect_step 0x1155c7 0x48 0xea (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x1155ca [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x1155ca) (notR64Effect 0x1155ca 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x1155ca 2).toInstrSpec (not_r64_effect_step 0x1155ca 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x1155cd [0x48, 0x01, 0xE9] (fun s => s.RIP = 0x1155cd) (addR64R64Effect 0x1155cd 1 5)
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1155cd 1 5).toInstrSpec (add_r64_r64_effect_step 0x1155cd 0x48 0xe9 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x1155d0 [0x48, 0x83, 0xC1, 0x02] (fun s => s.RIP = 0x1155d0) (addR64Imm8Effect 0x1155d0 1 0x2)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1155d0 1 0x2).toInstrSpec (add_r64_imm8_effect_step 0x1155d0 0x48 0xc1 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x1155d4 [0x48, 0x09, 0xD1] (fun s => s.RIP = 0x1155d4) (orR64R64Effect 0x1155d4 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1155d4 1 2).toInstrSpec (or_r64_r64_effect_step 0x1155d4 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x1155d7 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x1155d7) (shrR64Effect 0x1155d7 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1155d7 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x1155d7 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(1, 87), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115591) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(1, 89), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115596) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(1, 91), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11559a) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f23 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(1, 91), (2, 93), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155a4) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(1, 91), (2, 95), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155a7) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(1, 91), (2, 97), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155aa) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(1, 99), (2, 97), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155ad) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f27 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(1, 101), (2, 97), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155b0) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(1, 103), (2, 97), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155b3) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f29 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(1, 105), (2, 97), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155b7) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(1, 105), (2, 97), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155bc) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f31 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(1, 108), (2, 97), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155be) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(1, 110), (2, 97), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155c3) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f33 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(1, 112), (2, 97), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155c7) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f34 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(1, 112), (2, 114), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155ca) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f35 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(1, 112), (2, 116), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155cd) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f36 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(1, 118), (2, 116), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155d0) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f37 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(1, 120), (2, 116), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155d4) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f38 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(1, 122), (2, 116), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155d7) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f39 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(1, 124), (2, 116), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1155db) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l115537_2 code

theorem rest_l115537 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x115537 bytes_l115537) (entryMap (live .l115537))
      55 0x115537 bytes_l115537 b_l115537 := by
  have f0 : InstrSpec 0x115537 [0x4C, 0x89, 0x7C, 0x24, 0x40] (StorePre 0x115537 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x115537 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115537 15 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x115537 15 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x115537 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11553c [0x4C, 0x89, 0x6C, 0x24, 0x48] (StorePre 0x11553c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11553c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11553c 13 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11553c 13 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x11553c 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x115541 [0x48, 0x89, 0x5C, 0x24, 0x50] (StorePre 0x115541 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x115541 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115541 3 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x115541 3 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x115541 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x115546 [0x4C, 0x89, 0x74, 0x24, 0x58] (StorePre 0x115546 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x115546 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115546 14 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x115546 14 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x115546 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x11554b [0x4C, 0x8B, 0x6C, 0x24, 0x38] (LoadPre 0x11554b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11554b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11554b 13 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x11554b 13 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x11554b 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x115550 [0x49, 0x0F, 0xCD] (fun s => s.RIP = 0x115550) (bswapR64Effect 0x115550 3 13)
      [.gpr 13] [] [.reg 13, .rip] :=
    (bswapR64Effect_footprint 0x115550 3 13).toInstrSpec (bswap_r64_effect_step 0x115550 0x49 (by decide) 0xcd (by decide)) pre_rip
  have f6 : InstrSpec 0x115553 [0x48, 0x8B, 0x6C, 0x24, 0x70] (LoadPre 0x115553 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x115553 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x115553 5 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x115553 5 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x115553 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x115558 [0x48, 0x0F, 0xCD] (fun s => s.RIP = 0x115558) (bswapR64Effect 0x115558 3 5)
      [.gpr 5] [] [.reg 5, .rip] :=
    (bswapR64Effect_footprint 0x115558 3 5).toInstrSpec (bswap_r64_effect_step 0x115558 0x48 (by decide) 0xcd (by decide)) pre_rip
  have f8 : InstrSpec 0x11555b [0x4C, 0x8B, 0x74, 0x24, 0x68] (LoadPre 0x11555b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11555b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11555b 14 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x11555b 14 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x11555b 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x115560 [0x49, 0x0F, 0xCE] (fun s => s.RIP = 0x115560) (bswapR64Effect 0x115560 3 14)
      [.gpr 14] [] [.reg 14, .rip] :=
    (bswapR64Effect_footprint 0x115560 3 14).toInstrSpec (bswap_r64_effect_step 0x115560 0x49 (by decide) 0xce (by decide)) pre_rip
  have f10 : InstrSpec 0x115563 [0x48, 0x8B, 0x5C, 0x24, 0x60] (LoadPre 0x115563 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x115563 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x115563 3 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x115563 3 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x115563 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x115568 [0x48, 0x0F, 0xCB] (fun s => s.RIP = 0x115568) (bswapR64Effect 0x115568 3 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (bswapR64Effect_footprint 0x115568 3 3).toInstrSpec (bswap_r64_effect_step 0x115568 0x48 (by decide) 0xcb (by decide)) pre_rip
  have f12 : InstrSpec 0x11556b [0x48, 0xB8, 0xBF, 0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40] (fun s => s.RIP = 0x11556b) (movR64Imm64Effect 0x11556b 0 0x402da1732fc9bebf)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x11556b 0 0x402da1732fc9bebf).toInstrSpec (mov_r64_imm64_effect_step 0x11556b 0x48 0xb8 (by decide) (by decide) 0x402da1732fc9bebf) pre_rip
  have f13 : InstrSpec 0x115575 [0x48, 0x01, 0xD8] (fun s => s.RIP = 0x115575) (addR64R64Effect 0x115575 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x115575 0 3).toInstrSpec (add_r64_r64_effect_step 0x115575 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x115578 [0x48, 0x89, 0xD9] (fun s => s.RIP = 0x115578) (movR64R64Effect 0x115578 1 3)
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x115578 1 3).toInstrSpec (mov_r64_r64_effect_step 0x115578 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11557b [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x11557b) (notR64Effect 0x11557b 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x11557b 1).toInstrSpec (not_r64_effect_step 0x11557b 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11557e [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x11557e) (orR64R64Effect 0x11557e 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11557e 1 0).toInstrSpec (or_r64_r64_effect_step 0x11557e 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x115581 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x115581) (shrR64Effect 0x115581 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x115581 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x115581 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x115585 [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x115585 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x115585 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115585 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x115585 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x115585 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x11558a [0x48, 0x8D, 0x44, 0x24, 0x18] (fun s => s.RIP = 0x11558a) (leaR64Effect 0x11558a 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11558a 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (lea_r64_effect_step 0x11558a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11553c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115541) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115546) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11554b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115550) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115553) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 61), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115558) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11555b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115560) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(3, 3), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115563) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(3, 69), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115568) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11556b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115575) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115578) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 75), (1, 77), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11557b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 75), (1, 79), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11557e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 75), (1, 81), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115581) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 75), (1, 83), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115585) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 75), (1, 83), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11558a) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(1, 83), (3, 71), (4, 4), (5, 63), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11558f) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l115537_1 code

theorem block_l115537 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l115537 :=
  Rest.liftedBlock (rest_l115537 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l115537 x hx)

theorem rest_l115612_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x115612 bytes_l115612) [(0, 57), (1, 79), (2, 71), (3, 83), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]
      12 0x115656 bytes_l115612_1 b_l115612_1 := by
  have f20 : InstrSpec 0x115656 [0x48, 0x89, 0x4C, 0x24, 0x38] (StorePre 0x115656 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x115656 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115656 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x115656 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x115656 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x11565b [0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x11565b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11565b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11565b 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11565b 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x11565b 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x115663 [0x48, 0x89, 0x9C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x115663 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x115663 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115663 3 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x115663 3 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x115663 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x11566b [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x11566b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11566b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11566b (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11566b (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x11566b 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x115674 [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x115674 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x115674 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x115674 (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x115674 (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x115674 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x11567d [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x11567d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11567d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11567d (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11567d (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x11567d 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x115686 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x115686 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x115686 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x115686 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x115686 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x115686 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x11568f [0x48, 0x8D, 0x7C, 0x24, 0x78] (fun s => s.RIP = 0x11568f) (leaR64Effect 0x11568f 7 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11568f 7 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x11568f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x115694 [0x48, 0x8D, 0x54, 0x24, 0x18] (fun s => s.RIP = 0x115694) (leaR64Effect 0x115694 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x115694 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (lea_r64_effect_step 0x115694 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x115699 [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x115699) (movR32Imm32Effect 0x115699 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x115699 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x115699 0xbe (by decide) 0x4) pre_rip
  have f30 : InstrSpec 0x11569e [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11569e) (movR32Imm32Effect 0x11569e 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x11569e 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x11569e 0xb9 (by decide) 0x4) pre_rip
  have f31 : InstrSpec 0x1156a3 [0xE8, 0xA8, 0x28, 0x01, 0x00] (PushPre 0x1156a3 5) (callEffect (fun _ => 0x127f50) 0x1156a8)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1156a3 0x127f50 0x1156a8).toInstrSpec (call_rel32_effect_step 0x1156a3 0x128a8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 57), (1, 79), (2, 71), (3, 83), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11565b) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 57), (1, 79), (2, 71), (3, 83), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115663) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 57), (1, 79), (2, 71), (3, 83), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11566b) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 57), (1, 79), (2, 71), (3, 83), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115674) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 57), (1, 79), (2, 71), (3, 83), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11567d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 57), (1, 79), (2, 71), (3, 83), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115686) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 57), (1, 79), (2, 71), (3, 83), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11568f) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f27 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 57), (1, 79), (2, 71), (3, 83), (4, 4), (5, 5), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115694) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 57), (1, 79), (2, 98), (3, 83), (4, 4), (5, 5), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115699) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f29 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 57), (1, 79), (2, 98), (3, 83), (4, 4), (5, 5), (6, 100), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11569e) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 57), (1, 102), (2, 98), (3, 83), (4, 4), (5, 5), (6, 100), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156a3) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f31 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 57), (1, 102), (2, 98), (3, 83), (4, 104), (5, 5), (6, 100), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f50) f31 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 106) (by decide) (by decide) rfl rfl

theorem rest_l115612 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x115612 bytes_l115612) (entryMap (live .l115612))
      32 0x115612 bytes_l115612 b_l115612 := by
  have f0 : InstrSpec 0x115612 [0x41, 0x89, 0xC7] (fun s => s.RIP = 0x115612) (movR32R32Effect 0x115612 3 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x115612 3 15 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x115612 0x41 0xc7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x115615 [0x88, 0x44, 0x24, 0x18] (StorePre 0x115615 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x115615 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x115615 4 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x115615 4 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m8_r8_effect_step 0x115615 0 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x115619 [0x48, 0x8D, 0x44, 0x24, 0x18] (fun s => s.RIP = 0x115619) (leaR64Effect 0x115619 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x115619 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (lea_r64_effect_step 0x115619 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11561e [0x0F, 0xB6, 0x44, 0x24, 0x18] (LoadPre 0x11561e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11561e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11561e 5 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x11561e 5 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (movzx_r32_m8_effect_step 0x11561e 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x115623 [0x31, 0xC9] (fun s => s.RIP = 0x115623) (xorR32R32Effect 0x115623 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x115623 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x115623 0xc9 (by decide)) pre_rip
  have f5 : InstrSpec 0x115625 [0x84, 0xC0] (fun s => s.RIP = 0x115625) (testR8R8Effect 0x115625 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x115625 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x115625 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x115627 [0x48, 0x0F, 0x45, 0xCB] (fun s => s.RIP = 0x115627) (atFlags (condHolds 5) (cmovR64R64Effect 0x115627 4 1 3))
      [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (cmovR64R64Effect_footprint 0x115627 4 1 3 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x115627 5 0x48 (by decide) 0xcb (by decide) c)) pre_rip
  have f7 : InstrSpec 0x11562b [0x31, 0xDB] (fun s => s.RIP = 0x11562b) (xorR32R32Effect 0x11562b 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11562b 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x11562b 0xdb (by decide)) pre_rip
  have f8 : InstrSpec 0x11562d [0x31, 0xD2] (fun s => s.RIP = 0x11562d) (xorR32R32Effect 0x11562d 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11562d 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x11562d 0xd2 (by decide)) pre_rip
  have f9 : InstrSpec 0x11562f [0x84, 0xC0] (fun s => s.RIP = 0x11562f) (testR8R8Effect 0x11562f 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11562f 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11562f 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x115631 [0x49, 0x0F, 0x45, 0xD6] (fun s => s.RIP = 0x115631) (atFlags (condHolds 5) (cmovR64R64Effect 0x115631 4 2 14))
      [.gpr 2, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x115631 4 2 14 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x115631 5 0x49 (by decide) 0xd6 (by decide) c)) pre_rip
  have f11 : InstrSpec 0x115635 [0x49, 0x89, 0xCE] (fun s => s.RIP = 0x115635) (movR64R64Effect 0x115635 14 1)
      [.gpr 1] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x115635 14 1).toInstrSpec (mov_r64_r64_effect_step 0x115635 0x49 0xce (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x115638 [0x31, 0xC9] (fun s => s.RIP = 0x115638) (xorR32R32Effect 0x115638 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x115638 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x115638 0xc9 (by decide)) pre_rip
  have f13 : InstrSpec 0x11563a [0x84, 0xC0] (fun s => s.RIP = 0x11563a) (testR8R8Effect 0x11563a 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11563a 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11563a 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11563c [0x48, 0x0F, 0x45, 0xCD] (fun s => s.RIP = 0x11563c) (atFlags (condHolds 5) (cmovR64R64Effect 0x11563c 4 1 5))
      [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (cmovR64R64Effect_footprint 0x11563c 4 1 5 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11563c 5 0x48 (by decide) 0xcd (by decide) c)) pre_rip
  have f15 : InstrSpec 0x115640 [0x84, 0xC0] (fun s => s.RIP = 0x115640) (testR8R8Effect 0x115640 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x115640 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x115640 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x115642 [0x49, 0x0F, 0x45, 0xDD] (fun s => s.RIP = 0x115642) (atFlags (condHolds 5) (cmovR64R64Effect 0x115642 4 3 13))
      [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 3, .rip] :=
    (cmovR64R64Effect_footprint 0x115642 4 3 13 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x115642 5 0x49 (by decide) 0xdd (by decide) c)) pre_rip
  have f17 : InstrSpec 0x115646 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x115646) (movR64R64Effect 0x115646 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x115646 13 2).toInstrSpec (mov_r64_r64_effect_step 0x115646 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x115649 [0x4C, 0x89, 0x74, 0x24, 0x78] (StorePre 0x115649 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x115649 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115649 14 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x115649 14 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x115649 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x11564e [0x48, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x11564e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11564e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11564e 2 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11564e 2 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x11564e 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115615) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115619) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11561e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115623) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115625) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115627) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 63), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11562b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 63), (2, 2), (3, 65), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11562d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 63), (2, 67), (3, 65), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11562f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 63), (2, 67), (3, 65), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115631) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 63), (2, 71), (3, 65), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115635) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 57), (1, 63), (2, 71), (3, 65), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 53), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115638) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 57), (1, 75), (2, 71), (3, 65), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11563a) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 57), (1, 75), (2, 71), (3, 65), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 53), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11563c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 57), (1, 79), (2, 71), (3, 65), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 53), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115640) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 57), (1, 79), (2, 71), (3, 65), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115642) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 57), (1, 79), (2, 71), (3, 83), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115646) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 57), (1, 79), (2, 71), (3, 83), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115649) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 57), (1, 79), (2, 71), (3, 83), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11564e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 57), (1, 79), (2, 71), (3, 83), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115656) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l115612_1 code

theorem block_l115612 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l115612 :=
  Rest.liftedBlock (rest_l115612 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l115612 x hx)

theorem rest_l1156a8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1156a8 bytes_l1156a8) (entryMap (live .l1156a8))
      3 0x1156a8 bytes_l1156a8 b_l1156a8 := by
  have f0 : InstrSpec 0x1156a8 [0x24, 0x01] (fun s => s.RIP = 0x1156a8) (andAlImm8Effect 0x1156a8 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x1156a8 0x1).toInstrSpec (and_al_imm8_effect_step 0x1156a8 0x1) pre_rip
  have f1 : InstrSpec 0x1156aa [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x1156aa) (movzxR32R8Effect 0x1156aa 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x1156aa 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x1156aa 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1156ad [0xE8, 0x9E, 0x26, 0x01, 0x00] (PushPre 0x1156ad 5) (callEffect (fun _ => 0x127d50) 0x1156b2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1156ad 0x127d50 0x1156b2).toInstrSpec (call_rel32_effect_step 0x1156ad 0x1269e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156aa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156ad) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1156a8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1156a8 :=
  Rest.liftedBlock (rest_l1156a8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1156a8 x hx)

theorem rest_l1156b2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1156b2 bytes_l1156b2) (entryMap (live .l1156b2))
      4 0x1156b2 bytes_l1156b2 b_l1156b2 := by
  have f0 : InstrSpec 0x1156b2 [0xF6, 0xD0] (fun s => s.RIP = 0x1156b2) (notR8Effect 0x1156b2 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x1156b2 2 0).toInstrSpec (not_r8_effect_step 0x1156b2 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1156b4 [0x24, 0x01] (fun s => s.RIP = 0x1156b4) (andAlImm8Effect 0x1156b4 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x1156b4 0x1).toInstrSpec (and_al_imm8_effect_step 0x1156b4 0x1) pre_rip
  have f2 : InstrSpec 0x1156b6 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x1156b6) (movzxR32R8Effect 0x1156b6 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x1156b6 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x1156b6 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1156b9 [0xE8, 0x92, 0x26, 0x01, 0x00] (PushPre 0x1156b9 5) (callEffect (fun _ => 0x127d50) 0x1156be)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1156b9 0x127d50 0x1156be).toInstrSpec (call_rel32_effect_step 0x1156b9 0x12692 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156b4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156b6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156b9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1156b2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1156b2 :=
  Rest.liftedBlock (rest_l1156b2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1156b2 x hx)

theorem rest_l1156be [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1156be bytes_l1156be) (entryMap (live .l1156be))
      3 0x1156be bytes_l1156be b_l1156be := by
  have f0 : InstrSpec 0x1156be [0x44, 0x20, 0xF8] (fun s => s.RIP = 0x1156be) (andR8R8Effect 0x1156be 3 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (andR8R8Effect_footprint 0x1156be 3 0 15).toInstrSpec (and_r8_r8_rex_effect_step 0x1156be 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1156c1 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x1156c1) (movzxR32R8Effect 0x1156c1 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x1156c1 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x1156c1 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1156c4 [0xE8, 0x87, 0x26, 0x01, 0x00] (PushPre 0x1156c4 5) (callEffect (fun _ => 0x127d50) 0x1156c9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1156c4 0x127d50 0x1156c9).toInstrSpec (call_rel32_effect_step 0x1156c4 0x12687 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156c4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1156be [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1156be :=
  Rest.liftedBlock (rest_l1156be code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1156be x hx)

theorem rest_l1156c9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1156c9 bytes_l1156c9) (entryMap (live .l1156c9))
      2 0x1156c9 bytes_l1156c9 b_l1156c9 := by
  have f0 : InstrSpec 0x1156c9 [0x3C, 0x01] (fun s => s.RIP = 0x1156c9) (cmpAlImm8Effect 0x1156c9 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x1156c9 0x1).toInstrSpec (cmp_al_imm8_effect_step 0x1156c9 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156cb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1156cb 5 0x5d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1156c9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1156c9 :=
  Rest.liftedBlock (rest_l1156c9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1156c9 x hx)

theorem rest_l1156cd_1 [Bindings] (code : CodeMap) :
    Rest (n := 86) code lifted (codeRange 0x1156cd bytes_l1156cd) [(0, 77), (1, 73), (2, 69), (3, 3), (4, 4), (5, 75), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]
      4 0x11571e bytes_l1156cd_1 b_l1156cd_1 := by
  have f20 : InstrSpec 0x11571e [0x48, 0x89, 0x55, 0x40] (StorePre 0x11571e 4 (fun s => AddrMode.addr (.base 5 (.d8 0x40)) s (0x11571e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11571e 2 (.base 5 (.d8 0x40)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x11571e 2 (.base 5 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x11571e 0x48 (by decide) 2 (.base 5 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x115722 [0x48, 0x89, 0x4D, 0x48] (StorePre 0x115722 4 (fun s => AddrMode.addr (.base 5 (.d8 0x48)) s (0x115722 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x115722 1 (.base 5 (.d8 0x48)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x115722 1 (.base 5 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x115722 0x48 (by decide) 1 (.base 5 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x115726 [0x31, 0xC0] (fun s => s.RIP = 0x115726) (xorR32R32Effect 0x115726 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x115726 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x115726 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 77), (1, 73), (2, 69), (3, 3), (4, 4), (5, 75), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115722) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 77), (1, 73), (2, 69), (3, 3), (4, 4), (5, 75), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115726) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 88), (1, 73), (2, 69), (3, 3), (4, 4), (5, 75), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115728) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 90) (jmp_rel8_effect_step 0x115728 0x12 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l1156cd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1156cd bytes_l1156cd) (entryMap (live .l1156cd))
      24 0x1156cd bytes_l1156cd b_l1156cd := by
  have f0 : InstrSpec 0x1156cd [0x0F, 0xB6, 0x44, 0x24, 0x0F] (LoadPre 0x1156cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1156cd + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1156cd 5 0 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1156cd 5 0 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x1156cd 0 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1156d2 [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x1156d2) (negR64Effect 0x1156d2 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x1156d2 0).toInstrSpec (neg_r64_effect_step 0x1156d2 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1156d5 [0x48, 0x8B, 0x7C, 0x24, 0x40] (LoadPre 0x1156d5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1156d5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1156d5 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1156d5 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1156d5 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1156da [0x48, 0x21, 0xC7] (fun s => s.RIP = 0x1156da) (andR64R64Effect 0x1156da 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1156da 7 0).toInstrSpec (and_r64_r64_effect_step 0x1156da 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1156dd [0x49, 0x21, 0xC4] (fun s => s.RIP = 0x1156dd) (andR64R64Effect 0x1156dd 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1156dd 12 0).toInstrSpec (and_r64_r64_effect_step 0x1156dd 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1156e0 [0x48, 0x8B, 0x74, 0x24, 0x48] (LoadPre 0x1156e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1156e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1156e0 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1156e0 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x1156e0 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1156e5 [0x48, 0x21, 0xC6] (fun s => s.RIP = 0x1156e5) (andR64R64Effect 0x1156e5 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1156e5 6 0).toInstrSpec (and_r64_r64_effect_step 0x1156e5 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1156e8 [0x48, 0x8B, 0x54, 0x24, 0x50] (LoadPre 0x1156e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1156e8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1156e8 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1156e8 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x1156e8 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1156ed [0x48, 0x21, 0xC2] (fun s => s.RIP = 0x1156ed) (andR64R64Effect 0x1156ed 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1156ed 2 0).toInstrSpec (and_r64_r64_effect_step 0x1156ed 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1156f0 [0x48, 0x8B, 0x4C, 0x24, 0x58] (LoadPre 0x1156f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1156f0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1156f0 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1156f0 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x1156f0 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1156f5 [0x48, 0x21, 0xC1] (fun s => s.RIP = 0x1156f5) (andR64R64Effect 0x1156f5 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1156f5 1 0).toInstrSpec (and_r64_r64_effect_step 0x1156f5 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1156f8 [0x48, 0x8B, 0x6C, 0x24, 0x10] (LoadPre 0x1156f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1156f8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1156f8 5 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x1156f8 5 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1156f8 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1156fd [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x1156fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1156fd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1156fd 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1156fd 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1156fd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x115702 [0x48, 0x89, 0x45, 0x18] (StorePre 0x115702 4 (fun s => AddrMode.addr (.base 5 (.d8 0x18)) s (0x115702 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x115702 0 (.base 5 (.d8 0x18)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x115702 0 (.base 5 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x115702 0x48 (by decide) 0 (.base 5 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x115706 [0x48, 0x89, 0x5D, 0x20] (StorePre 0x115706 4 (fun s => AddrMode.addr (.base 5 (.d8 0x20)) s (0x115706 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x115706 3 (.base 5 (.d8 0x20)))
      [.gpr 3, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x115706 3 (.base 5 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x115706 0x48 (by decide) 3 (.base 5 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x11570a [0x4C, 0x89, 0x75, 0x08] (StorePre 0x11570a 4 (fun s => AddrMode.addr (.base 5 (.d8 0x8)) s (0x11570a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11570a 14 (.base 5 (.d8 0x8)))
      [.gpr 14, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x11570a 14 (.base 5 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11570a 0x4c (by decide) 6 (.base 5 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x11570e [0x4C, 0x89, 0x6D, 0x10] (StorePre 0x11570e 4 (fun s => AddrMode.addr (.base 5 (.d8 0x10)) s (0x11570e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11570e 13 (.base 5 (.d8 0x10)))
      [.gpr 13, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x11570e 13 (.base 5 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11570e 0x4c (by decide) 5 (.base 5 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x115712 [0x48, 0x89, 0x7D, 0x28] (StorePre 0x115712 4 (fun s => AddrMode.addr (.base 5 (.d8 0x28)) s (0x115712 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x115712 7 (.base 5 (.d8 0x28)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x115712 7 (.base 5 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x115712 0x48 (by decide) 7 (.base 5 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x115716 [0x4C, 0x89, 0x65, 0x30] (StorePre 0x115716 4 (fun s => AddrMode.addr (.base 5 (.d8 0x30)) s (0x115716 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x115716 12 (.base 5 (.d8 0x30)))
      [.gpr 12, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x115716 12 (.base 5 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x115716 0x4c (by decide) 4 (.base 5 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x11571a [0x48, 0x89, 0x75, 0x38] (StorePre 0x11571a 4 (fun s => AddrMode.addr (.base 5 (.d8 0x38)) s (0x11571a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11571a 6 (.base 5 (.d8 0x38)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x11571a 6 (.base 5 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x11571a 0x48 (by decide) 6 (.base 5 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156d2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156d5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156da) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (3, 3), (4, 4), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156dd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (3, 3), (4, 4), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156e0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (3, 3), (4, 4), (6, 63), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156e5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (3, 3), (4, 4), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156e8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (2, 67), (3, 3), (4, 4), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156ed) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (2, 69), (3, 3), (4, 4), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156f0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 71), (2, 69), (3, 3), (4, 4), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156f5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 73), (2, 69), (3, 3), (4, 4), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156f8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 73), (2, 69), (3, 3), (4, 4), (5, 75), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1156fd) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 73), (2, 69), (3, 3), (4, 4), (5, 75), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115702) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (1, 73), (2, 69), (3, 3), (4, 4), (5, 75), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115706) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 77), (1, 73), (2, 69), (3, 3), (4, 4), (5, 75), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11570a) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 77), (1, 73), (2, 69), (3, 3), (4, 4), (5, 75), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11570e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 77), (1, 73), (2, 69), (3, 3), (4, 4), (5, 75), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115712) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 77), (1, 73), (2, 69), (3, 3), (4, 4), (5, 75), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115716) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 77), (1, 73), (2, 69), (3, 3), (4, 4), (5, 75), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11571a) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 77), (1, 73), (2, 69), (3, 3), (4, 4), (5, 75), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11571e) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1156cd_1 code

theorem block_l1156cd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1156cd :=
  Rest.liftedBlock (rest_l1156cd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1156cd x hx)

theorem rest_l11572a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11572a bytes_l11572a) (entryMap (live .l11572a))
      3 0x11572a bytes_l11572a b_l11572a := by
  have f0 : InstrSpec 0x11572a [0x48, 0x8B, 0x6C, 0x24, 0x10] (LoadPre 0x11572a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11572a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11572a 5 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x11572a 5 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x11572a 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11572f [0x48, 0xC7, 0x45, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x11572f 8 (fun s => AddrMode.addr (.base 5 (.d8 0x8)) s (0x11572f + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x11572f (.base 5 (.d8 0x8)) 0x0)
      [.gpr 5] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11572f (.base 5 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x11572f 0x48 (by decide) (.base 5 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x115737 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x115737) (movR32Imm32Effect 0x115737 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x115737 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x115737 0xb8 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11572f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115737) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11573c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l11572a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11572a :=
  Rest.liftedBlock (rest_l11572a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11572a x hx)

theorem rest_l11573c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11573c bytes_l11573c) (entryMap (live .l11573c))
      10 0x11573c bytes_l11573c b_l11573c := by
  have f0 : InstrSpec 0x11573c [0x48, 0x89, 0x45, 0x00] (StorePre 0x11573c 4 (fun s => AddrMode.addr (.base 5 (.d8 0x0)) s (0x11573c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11573c 0 (.base 5 (.d8 0x0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x11573c 0 (.base 5 (.d8 0x0))).toInstrSpec (mov_m64_r64_effect_step 0x11573c 0x48 (by decide) 0 (.base 5 (.d8 0x0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x115740 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x115740) (movR64R64Effect 0x115740 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x115740 0 5).toInstrSpec (mov_r64_r64_effect_step 0x115740 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x115743 [0x48, 0x81, 0xC4, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x115743) (addR64Imm32Effect 0x115743 4 0x98)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x115743 4 0x98).toInstrSpec (add_r64_imm32_effect_step 0x115743 0x48 0xc4 0x98 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11574a [0x5B] (PopPre 0x11574a) (popR64Effect 0x11574a 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11574a 1 3).toInstrSpec (pop_r64_effect_step 0x11574a 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x11574b [0x41, 0x5C] (PopPre 0x11574b) (popR64Effect 0x11574b 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11574b 2 12).toInstrSpec (pop_r64_rex_effect_step 0x11574b 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x11574d [0x41, 0x5D] (PopPre 0x11574d) (popR64Effect 0x11574d 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11574d 2 13).toInstrSpec (pop_r64_rex_effect_step 0x11574d 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x11574f [0x41, 0x5E] (PopPre 0x11574f) (popR64Effect 0x11574f 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11574f 2 14).toInstrSpec (pop_r64_rex_effect_step 0x11574f 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x115751 [0x41, 0x5F] (PopPre 0x115751) (popR64Effect 0x115751 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x115751 2 15).toInstrSpec (pop_r64_rex_effect_step 0x115751 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x115753 [0x5D] (PopPre 0x115753) (popR64Effect 0x115753 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x115753 1 5).toInstrSpec (pop_r64_effect_step 0x115753 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x115754 [0xC3] (RetPre 0x115754) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x115754).toInstrSpec (ret_effect_step 0x115754) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115740) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115743) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11574a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11574b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11574d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11574f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115751) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 71), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115753) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 74), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115754) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f9 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 78) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 77), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) f9 (by decide) rfl rfl rfl (by decide)

theorem block_l11573c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11573c :=
  Rest.liftedBlock (rest_l11573c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11573c x hx)

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

theorem_by block_l115408_eval :
    program.runBlock (dialect code) ⟨.l115408, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11543e_eval :
    program.runBlock (dialect code) ⟨.l11543e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1154f4_eval :
    program.runBlock (dialect code) ⟨.l1154f4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l115500_eval :
    program.runBlock (dialect code) ⟨.l115500, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l115508_eval :
    program.runBlock (dialect code) ⟨.l115508, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11552f_eval :
    program.runBlock (dialect code) ⟨.l11552f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l115537_eval :
    program.runBlock (dialect code) ⟨.l115537, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l115612_eval :
    program.runBlock (dialect code) ⟨.l115612, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1156a8_eval :
    program.runBlock (dialect code) ⟨.l1156a8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1156b2_eval :
    program.runBlock (dialect code) ⟨.l1156b2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1156be_eval :
    program.runBlock (dialect code) ⟨.l1156be, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1156c9_eval :
    program.runBlock (dialect code) ⟨.l1156c9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1156cd_eval :
    program.runBlock (dialect code) ⟨.l1156cd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11572a_eval :
    program.runBlock (dialect code) ⟨.l11572a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11573c_eval :
    program.runBlock (dialect code) ⟨.l11573c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
