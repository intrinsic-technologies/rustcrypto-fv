import K256.Proofs.Ecdh.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Ecdh.LIR.Generated.Values

namespace K256.Proofs.Ecdh.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR

theorem rest_l1205b0_2 [Bindings] (code : CodeMap) :
    Rest (n := 133) code lifted (codeRange 0x1205b0 bytes_l1205b0) [(0, 124), (1, 131), (2, 101), (3, 89), (4, 65), (5, 85), (6, 111), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 115), (16, 128), (19, 129), (22, 22), (39, 39), (50, 50), (51, 51)]
      3 0x120649 bytes_l1205b0_2 b_l1205b0_2 := by
  have f40 : InstrSpec 0x120649 [0x20, 0xC1] (fun s => s.RIP = 0x120649) (andR8R8Effect 0x120649 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR8R8Effect_footprint 0x120649 2 1 0).toInstrSpec (and_r8_r8_effect_step 0x120649 0xc1 (by decide) (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x12064b [0x0F, 0xB6, 0xF9] (fun s => s.RIP = 0x12064b) (movzxR32R8Effect 0x12064b 3 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x12064b 3 7 1).toInstrSpec (movzx_r32_r8_effect_step 0x12064b 0xf9 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x12064e [0xE8, 0xFD, 0x76, 0x00, 0x00] (PushPre 0x12064e 5) (callEffect (fun _ => 0x127d50) 0x120653)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12064e 0x127d50 0x120653).toInstrSpec (call_rel32_effect_step 0x12064e 0x76fd (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f40 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 124), (1, 133), (2, 101), (3, 89), (4, 65), (5, 85), (6, 111), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 115), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12064b) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f41 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 124), (1, 133), (2, 101), (3, 89), (4, 65), (5, 85), (6, 111), (7, 135), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 115), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12064e) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f42 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 124), (1, 133), (2, 101), (3, 89), (4, 137), (5, 85), (6, 111), (7, 135), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 115), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f42 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 139) (by decide) (by decide) rfl rfl

theorem rest_l1205b0_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x1205b0 bytes_l1205b0) [(0, 79), (2, 73), (3, 89), (4, 65), (5, 85), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 83), (13, 13), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      23 0x1205fa bytes_l1205b0_1 b_l1205b0_1 := by
  have f20 : InstrSpec 0x1205fa [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x1205fa) (movR64R64Effect 0x1205fa 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1205fa 1 0).toInstrSpec (mov_r64_r64_effect_step 0x1205fa 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1205fd [0x49, 0x0F, 0xA4, 0xC6, 0x18] (fun s => s.RIP = 0x1205fd) (shldR64R64Effect 0x1205fd 5 14 0 24)
      [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1205fd 5 14 0 24).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1205fd 0x49 (by decide) 0xc6 (by decide) 0x18) pre_rip
  have f22 : InstrSpec 0x120602 [0x4C, 0x0F, 0xA4, 0xE1, 0x0C] (fun s => s.RIP = 0x120602) (shldR64R64Effect 0x120602 5 1 12 12)
      [.gpr 1, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x120602 5 1 12 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x120602 0x4c (by decide) 0xe1 (by decide) 0xc) pre_rip
  have f23 : InstrSpec 0x120607 [0x49, 0x21, 0xEC] (fun s => s.RIP = 0x120607) (andR64R64Effect 0x120607 12 5)
      [.gpr 12, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120607 12 5).toInstrSpec (and_r64_r64_effect_step 0x120607 0x49 0xec (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x12060a [0x48, 0x21, 0xE9] (fun s => s.RIP = 0x12060a) (andR64R64Effect 0x12060a 1 5)
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x12060a 1 5).toInstrSpec (and_r64_r64_effect_step 0x12060a 0x48 0xe9 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x12060d [0x48, 0xC1, 0xEA, 0x10] (fun s => s.RIP = 0x12060d) (shrR64Effect 0x12060d 4 2 16)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x12060d 4 2 16).toInstrSpec (shr_r64_imm8_effect_step 0x12060d 0x48 0xea 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x120611 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x120611) (movR64R64Effect 0x120611 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120611 0 14).toInstrSpec (mov_r64_r64_effect_step 0x120611 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x120614 [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x120614) (andR64R64Effect 0x120614 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120614 0 3).toInstrSpec (and_r64_r64_effect_step 0x120614 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x120617 [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x120617) (andR64R64Effect 0x120617 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120617 0 1).toInstrSpec (and_r64_r64_effect_step 0x120617 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x12061a [0x49, 0x89, 0xCD] (fun s => s.RIP = 0x12061a) (movR64R64Effect 0x12061a 13 1)
      [.gpr 1] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x12061a 13 1).toInstrSpec (mov_r64_r64_effect_step 0x12061a 0x49 0xcd (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x12061d [0x48, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x12061d) (movR64Imm64Effect 0x12061d 6 0xffffffffffff)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x12061d 6 0xffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x12061d 0x48 0xbe (by decide) (by decide) 0xffffffffffff) pre_rip
  have f31 : InstrSpec 0x120627 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x120627) (movR64R64Effect 0x120627 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x120627 1 2).toInstrSpec (mov_r64_r64_effect_step 0x120627 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x12062a [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x12062a) (movR64R64Effect 0x12062a 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x12062a 15 2).toInstrSpec (mov_r64_r64_effect_step 0x12062a 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x12062d [0x48, 0x31, 0xF1] (fun s => s.RIP = 0x12062d) (xorR64R64Effect 0x12062d 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x12062d 1 6).toInstrSpec (xor_r64_r64_effect_step 0x12062d 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x120630 [0x48, 0x31, 0xE8] (fun s => s.RIP = 0x120630) (xorR64R64Effect 0x120630 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120630 0 5).toInstrSpec (xor_r64_r64_effect_step 0x120630 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x120633 [0x48, 0x09, 0xC8] (fun s => s.RIP = 0x120633) (orR64R64Effect 0x120633 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x120633 0 1).toInstrSpec (or_r64_r64_effect_step 0x120633 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x120636 [0x0F, 0x94, 0xC0] (fun s => s.RIP = 0x120636) (atFlags (condHolds 4) (setccR8Effect 0x120636 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x120636 3 0 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x120636 4 0xc0 (by decide) (by decide) c)) pre_rip
  have f37 : InstrSpec 0x120639 [0x48, 0xB9, 0x2E, 0xFC, 0xFF, 0xFF, 0xFE, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x120639) (movR64Imm64Effect 0x120639 1 0xffffefffffc2e)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x120639 1 0xffffefffffc2e).toInstrSpec (mov_r64_imm64_effect_step 0x120639 0x48 0xb9 (by decide) (by decide) 0xffffefffffc2e) pre_rip
  have f38 : InstrSpec 0x120643 [0x49, 0x39, 0xCC] (fun s => s.RIP = 0x120643) (cmpR64R64Effect 0x120643 12 1)
      [.gpr 12, .gpr 1] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x120643 12 1).toInstrSpec (cmp_r64_r64_effect_step 0x120643 0x49 0xcc (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x120646 [0x0F, 0x97, 0xC1] (fun s => s.RIP = 0x120646) (atFlags (condHolds 7) (setccR8Effect 0x120646 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x120646 3 1 7).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x120646 7 0xc1 (by decide) (by decide) c)) pre_rip
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 79), (1, 91), (2, 73), (3, 89), (4, 65), (5, 85), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 83), (13, 13), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205fd) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 79), (1, 91), (2, 73), (3, 89), (4, 65), (5, 85), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 83), (13, 13), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120602) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 79), (1, 95), (2, 73), (3, 89), (4, 65), (5, 85), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 83), (13, 13), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120607) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 79), (1, 95), (2, 73), (3, 89), (4, 65), (5, 85), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 13), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12060a) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 79), (1, 99), (2, 73), (3, 89), (4, 65), (5, 85), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 13), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12060d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 79), (1, 99), (2, 101), (3, 89), (4, 65), (5, 85), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 13), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120611) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 103), (1, 99), (2, 101), (3, 89), (4, 65), (5, 85), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 13), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120614) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 105), (1, 99), (2, 101), (3, 89), (4, 65), (5, 85), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 13), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120617) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f28 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 107), (1, 99), (2, 101), (3, 89), (4, 65), (5, 85), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 13), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12061a) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f29 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 107), (1, 99), (2, 101), (3, 89), (4, 65), (5, 85), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12061d) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f30 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 107), (1, 99), (2, 101), (3, 89), (4, 65), (5, 85), (6, 111), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120627) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f31 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 107), (1, 113), (2, 101), (3, 89), (4, 65), (5, 85), (6, 111), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12062a) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f32 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 107), (1, 113), (2, 101), (3, 89), (4, 65), (5, 85), (6, 111), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 115), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12062d) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f33 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 107), (1, 117), (2, 101), (3, 89), (4, 65), (5, 85), (6, 111), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 115), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120630) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f34 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 119), (1, 117), (2, 101), (3, 89), (4, 65), (5, 85), (6, 111), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 115), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120633) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f35 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 122) f35 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 123) (ρ' := [(0, 121), (1, 117), (2, 101), (3, 89), (4, 65), (5, 85), (6, 111), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 115), (19, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120636) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f36 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 124), (1, 117), (2, 101), (3, 89), (4, 65), (5, 85), (6, 111), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 115), (19, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120639) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f37 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 124), (1, 126), (2, 101), (3, 89), (4, 65), (5, 85), (6, 111), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 115), (19, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120643) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f38 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 129) f38 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 130) (ρ' := [(0, 124), (1, 126), (2, 101), (3, 89), (4, 65), (5, 85), (6, 111), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 115), (16, 128), (19, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120646) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f39 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 124), (1, 131), (2, 101), (3, 89), (4, 65), (5, 85), (6, 111), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 109), (14, 93), (15, 115), (16, 128), (19, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120649) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1205b0_2 code

theorem rest_l1205b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1205b0 bytes_l1205b0) (entryMap (live .l1205b0))
      43 0x1205b0 bytes_l1205b0 b_l1205b0 := by
  have f0 : InstrSpec 0x1205b0 [0x55] (PushPre 0x1205b0 1) (pushR64Effect 0x1205b0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1205b0 1 5).toInstrSpec (push_r64_effect_step 0x1205b0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1205b1 [0x41, 0x57] (PushPre 0x1205b1 2) (pushR64Effect 0x1205b1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1205b1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1205b1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1205b3 [0x41, 0x56] (PushPre 0x1205b3 2) (pushR64Effect 0x1205b3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1205b3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1205b3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1205b5 [0x41, 0x55] (PushPre 0x1205b5 2) (pushR64Effect 0x1205b5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1205b5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1205b5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1205b7 [0x41, 0x54] (PushPre 0x1205b7 2) (pushR64Effect 0x1205b7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1205b7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1205b7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1205b9 [0x53] (PushPre 0x1205b9 1) (pushR64Effect 0x1205b9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1205b9 1 3).toInstrSpec (push_r64_effect_step 0x1205b9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1205ba [0x48, 0x81, 0xEC, 0xB8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1205ba) (subR64Imm32Effect 0x1205ba 4 0x1b8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1205ba 4 0x1b8).toInstrSpec (sub_r64_imm32_effect_step 0x1205ba 0x48 0xec 0x1b8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1205c1 [0x89, 0x54, 0x24, 0x6C] (StorePre 0x1205c1 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x1205c1 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1205c1 2 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1205c1 2 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (mov_m32_r32_low_effect_step 0x1205c1 2 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1205c5 [0x48, 0x89, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1205c5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1205c5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1205c5 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1205c5 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x1205c5 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1205cd [0x48, 0x8B, 0x16] (LoadPre 0x1205cd (fun s => AddrMode.addr (.base 6 .none) s (0x1205cd + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1205cd 2 (.base 6 .none))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1205cd 2 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1205cd 0x48 (by decide) 2 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1205d0 [0x4C, 0x8B, 0x76, 0x08] (LoadPre 0x1205d0 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1205d0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1205d0 14 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1205d0 14 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1205d0 0x4c (by decide) 6 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1205d4 [0x48, 0x0F, 0xCA] (fun s => s.RIP = 0x1205d4) (bswapR64Effect 0x1205d4 3 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR64Effect_footprint 0x1205d4 3 2).toInstrSpec (bswap_r64_effect_step 0x1205d4 0x48 (by decide) 0xca (by decide)) pre_rip
  have f12 : InstrSpec 0x1205d7 [0x49, 0x0F, 0xCE] (fun s => s.RIP = 0x1205d7) (bswapR64Effect 0x1205d7 3 14)
      [.gpr 14] [] [.reg 14, .rip] :=
    (bswapR64Effect_footprint 0x1205d7 3 14).toInstrSpec (bswap_r64_effect_step 0x1205d7 0x49 (by decide) 0xce (by decide)) pre_rip
  have f13 : InstrSpec 0x1205da [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x1205da (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1205da + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1205da 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1205da 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1205da 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1205de [0x48, 0x0F, 0xC8] (fun s => s.RIP = 0x1205de) (bswapR64Effect 0x1205de 3 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR64Effect_footprint 0x1205de 3 0).toInstrSpec (bswap_r64_effect_step 0x1205de 0x48 (by decide) 0xc8 (by decide)) pre_rip
  have f15 : InstrSpec 0x1205e1 [0x4C, 0x8B, 0x66, 0x18] (LoadPre 0x1205e1 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1205e1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1205e1 12 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x1205e1 12 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1205e1 0x4c (by decide) 4 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1205e5 [0x49, 0x0F, 0xCC] (fun s => s.RIP = 0x1205e5) (bswapR64Effect 0x1205e5 3 12)
      [.gpr 12] [] [.reg 12, .rip] :=
    (bswapR64Effect_footprint 0x1205e5 3 12).toInstrSpec (bswap_r64_effect_step 0x1205e5 0x49 (by decide) 0xcc (by decide)) pre_rip
  have f17 : InstrSpec 0x1205e8 [0x48, 0xBD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x1205e8) (movR64Imm64Effect 0x1205e8 5 0xfffffffffffff)
      [] [] [.reg 5, .rip] :=
    (movR64Imm64Effect_footprint 0x1205e8 5 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x1205e8 0x48 0xbd (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f18 : InstrSpec 0x1205f2 [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x1205f2) (movR64R64Effect 0x1205f2 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1205f2 3 2).toInstrSpec (mov_r64_r64_effect_step 0x1205f2 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1205f5 [0x4C, 0x0F, 0xA4, 0xF3, 0x24] (fun s => s.RIP = 0x1205f5) (shldR64R64Effect 0x1205f5 5 3 14 36)
      [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1205f5 5 3 14 36).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1205f5 0x4c (by decide) 0xf3 (by decide) 0x24) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205b1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205b3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205b5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205b7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205b9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205ba) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205c1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205c5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205cd) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 69), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205d0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 69), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205d4) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(2, 73), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205d7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(2, 73), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205da) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (2, 73), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205de) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (2, 73), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205e1) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 79), (2, 73), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 13), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205e5) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 79), (2, 73), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 83), (13, 13), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205e8) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 79), (2, 73), (3, 3), (4, 65), (5, 85), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 83), (13, 13), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205f2) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 79), (2, 73), (3, 87), (4, 65), (5, 85), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 83), (13, 13), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205f5) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 79), (2, 73), (3, 89), (4, 65), (5, 85), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 83), (13, 13), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1205fa) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1205b0_1 code

theorem block_l1205b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1205b0 :=
  Rest.liftedBlock (rest_l1205b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1205b0 x hx)

theorem rest_l120653 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120653 bytes_l120653) (entryMap (live .l120653))
      4 0x120653 bytes_l120653 b_l120653 := by
  have f0 : InstrSpec 0x120653 [0xF6, 0xD0] (fun s => s.RIP = 0x120653) (notR8Effect 0x120653 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x120653 2 0).toInstrSpec (not_r8_effect_step 0x120653 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x120655 [0x24, 0x01] (fun s => s.RIP = 0x120655) (andAlImm8Effect 0x120655 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x120655 0x1).toInstrSpec (and_al_imm8_effect_step 0x120655 0x1) pre_rip
  have f2 : InstrSpec 0x120657 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x120657) (movzxR32R8Effect 0x120657 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x120657 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x120657 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12065a [0xE8, 0xF1, 0x76, 0x00, 0x00] (PushPre 0x12065a 5) (callEffect (fun _ => 0x127d50) 0x12065f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12065a 0x127d50 0x12065f).toInstrSpec (call_rel32_effect_step 0x12065a 0x76f1 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120655) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120657) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12065a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l120653 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120653 :=
  Rest.liftedBlock (rest_l120653 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120653 x hx)

theorem rest_l12065f_21 [Bindings] (code : CodeMap) :
    Rest (n := 967) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 952), (1, 948), (2, 962), (3, 907), (4, 4), (5, 872), (6, 946), (7, 942), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (16, 965), (22, 22), (39, 39), (50, 50), (51, 51)]
      16 0x120ca2 bytes_l12065f_21 b_l12065f_21 := by
  have f420 : InstrSpec 0x120ca2 [0x4C, 0x11, 0xCA] (fun s => s.RIP = 0x120ca2) (atFlags StatusFlags.CF (adcR64R64Effect 0x120ca2 2 9))
      [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120ca2 2 9).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120ca2 0x4c 0xca c (by decide) (by decide))) pre_rip
  have f421 : InstrSpec 0x120ca5 [0x4C, 0x21, 0xC3] (fun s => s.RIP = 0x120ca5) (andR64R64Effect 0x120ca5 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120ca5 3 8).toInstrSpec (and_r64_r64_effect_step 0x120ca5 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f422 : InstrSpec 0x120ca8 [0x4C, 0x0F, 0xA4, 0xC2, 0x0C] (fun s => s.RIP = 0x120ca8) (shldR64R64Effect 0x120ca8 5 2 8 12)
      [.gpr 2, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x120ca8 5 2 8 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x120ca8 0x4c (by decide) 0xc2 (by decide) 0xc) pre_rip
  have f423 : InstrSpec 0x120cad [0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x120cad) (movR64Imm64Effect 0x120cad 0 0xffffffffffff)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x120cad 0 0xffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x120cad 0x48 0xb8 (by decide) (by decide) 0xffffffffffff) pre_rip
  have f424 : InstrSpec 0x120cb7 [0x49, 0x21, 0xC6] (fun s => s.RIP = 0x120cb7) (andR64R64Effect 0x120cb7 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120cb7 14 0).toInstrSpec (and_r64_r64_effect_step 0x120cb7 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f425 : InstrSpec 0x120cba [0x49, 0x01, 0xD6] (fun s => s.RIP = 0x120cba) (addR64R64Effect 0x120cba 14 2)
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120cba 14 2).toInstrSpec (add_r64_r64_effect_step 0x120cba 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f426 : InstrSpec 0x120cbd [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x120cbd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x120cbd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120cbd 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120cbd 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x120cbd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f427 : InstrSpec 0x120cc2 [0x48, 0x83, 0xC0, 0x07] (fun s => s.RIP = 0x120cc2) (addR64Imm8Effect 0x120cc2 0 0x7)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x120cc2 0 0x7).toInstrSpec (add_r64_imm8_effect_step 0x120cc2 0x48 0xc0 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f428 : InstrSpec 0x120cc6 [0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x120cc6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x120cc6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120cc6 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120cc6 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x120cc6 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f429 : InstrSpec 0x120cce [0x4C, 0x89, 0x9C, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x120cce 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x120cce + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120cce 11 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120cce 11 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x120cce 0x4c (by decide) 3 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f430 : InstrSpec 0x120cd6 [0x48, 0x89, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x120cd6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x120cd6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120cd6 6 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120cd6 6 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x120cd6 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f431 : InstrSpec 0x120cde [0x48, 0x89, 0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x120cde 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x120cde + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120cde 3 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120cde 3 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x120cde 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f432 : InstrSpec 0x120ce6 [0x4C, 0x89, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x120ce6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x120ce6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120ce6 14 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120ce6 14 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x120ce6 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f433 : InstrSpec 0x120cee [0x48, 0x8D, 0xBC, 0x24, 0x30, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x120cee) (leaR64Effect 0x120cee 7 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x120cee 7 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (lea_r64_effect_step 0x120cee 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) pre_rip
  have f434 : InstrSpec 0x120cf6 [0x48, 0x8D, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x120cf6) (leaR64Effect 0x120cf6 6 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x120cf6 6 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (lea_r64_effect_step 0x120cf6 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) pre_rip
  have f435 : InstrSpec 0x120cfe [0xE8, 0x4D, 0x4C, 0xFF, 0xFF] (PushPre 0x120cfe 5) (callEffect (fun _ => 0x115950) 0x120d03)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x120cfe 0x115950 0x120d03).toInstrSpec (call_rel32_effect_step 0x120cfe 0xffff4c4d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 967) (RestInside.out (n := 967) f420 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 968) (ρ' := [(0, 952), (1, 948), (2, 967), (3, 907), (4, 4), (5, 872), (6, 946), (7, 942), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ca5) f420 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 969) (RestInside.out (n := 969) f421 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 970) (ρ' := [(0, 952), (1, 948), (2, 967), (3, 969), (4, 4), (5, 872), (6, 946), (7, 942), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ca8) f421 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 971) (RestInside.out (n := 971) f422 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 972) (ρ' := [(0, 952), (1, 948), (2, 971), (3, 969), (4, 4), (5, 872), (6, 946), (7, 942), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120cad) f422 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 973) (RestInside.out (n := 973) f423 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 974) (ρ' := [(0, 973), (1, 948), (2, 971), (3, 969), (4, 4), (5, 872), (6, 946), (7, 942), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120cb7) f423 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 975) (RestInside.out (n := 975) f424 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 976) (ρ' := [(0, 973), (1, 948), (2, 971), (3, 969), (4, 4), (5, 872), (6, 946), (7, 942), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 975), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120cba) f424 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 977) (RestInside.out (n := 977) f425 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 978) (ρ' := [(0, 973), (1, 948), (2, 971), (3, 969), (4, 4), (5, 872), (6, 946), (7, 942), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 977), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120cbd) f425 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 979) (RestInside.out (n := 979) f426 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 980) (ρ' := [(0, 979), (1, 948), (2, 971), (3, 969), (4, 4), (5, 872), (6, 946), (7, 942), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 977), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120cc2) f426 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 981) (RestInside.out (n := 981) f427 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 982) (ρ' := [(0, 981), (1, 948), (2, 971), (3, 969), (4, 4), (5, 872), (6, 946), (7, 942), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 977), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120cc6) f427 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 983) (RestInside.exec (n := 983) (ρ' := [(0, 981), (1, 948), (2, 971), (3, 969), (4, 4), (5, 872), (6, 946), (7, 942), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 977), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120cce) f428 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 984) (RestInside.exec (n := 984) (ρ' := [(0, 981), (1, 948), (2, 971), (3, 969), (4, 4), (5, 872), (6, 946), (7, 942), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 977), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120cd6) f429 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 985) (RestInside.exec (n := 985) (ρ' := [(0, 981), (1, 948), (2, 971), (3, 969), (4, 4), (5, 872), (6, 946), (7, 942), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 977), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120cde) f430 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 986) (RestInside.exec (n := 986) (ρ' := [(0, 981), (1, 948), (2, 971), (3, 969), (4, 4), (5, 872), (6, 946), (7, 942), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 977), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ce6) f431 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 987) (RestInside.exec (n := 987) (ρ' := [(0, 981), (1, 948), (2, 971), (3, 969), (4, 4), (5, 872), (6, 946), (7, 942), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 977), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120cee) f432 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 988) (RestInside.out (n := 988) f433 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 989) (ρ' := [(0, 981), (1, 948), (2, 971), (3, 969), (4, 4), (5, 872), (6, 946), (7, 988), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 977), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120cf6) f433 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 990) (RestInside.out (n := 990) f434 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 991) (ρ' := [(0, 981), (1, 948), (2, 971), (3, 969), (4, 4), (5, 872), (6, 990), (7, 988), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 977), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120cfe) f434 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 992) (RestInside.out (n := 992) f435 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 993) (ρ' := [(0, 981), (1, 948), (2, 971), (3, 969), (4, 992), (5, 872), (6, 990), (7, 988), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 977), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x115950) f435 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 994) (by decide) (by decide) rfl rfl

theorem rest_l12065f_20 [Bindings] (code : CodeMap) :
    Rest (n := 921) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 913), (1, 903), (2, 914), (3, 907), (4, 4), (5, 872), (6, 916), (7, 919), (8, 900), (9, 843), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]
      36 0x120c5b bytes_l12065f_20 b_l12065f_20 := by
  have f400 : InstrSpec 0x120c5b [0x48, 0x01, 0xEE] (fun s => s.RIP = 0x120c5b) (addR64R64Effect 0x120c5b 6 5)
      [.gpr 6, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120c5b 6 5).toInstrSpec (add_r64_r64_effect_step 0x120c5b 0x48 0xee (by decide) (by decide)) pre_rip
  have f401 : InstrSpec 0x120c5e [0x48, 0x13, 0x7C, 0x24, 0x08] (LoadPre 0x120c5e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120c5e + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x120c5e 7 (.sib 4 none 0 (.d8 0x8))))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 7, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x120c5e 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x120c5e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f402 : InstrSpec 0x120c63 [0x48, 0x01, 0xC6] (fun s => s.RIP = 0x120c63) (addR64R64Effect 0x120c63 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120c63 6 0).toInstrSpec (add_r64_r64_effect_step 0x120c63 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f403 : InstrSpec 0x120c66 [0x48, 0x11, 0xD7] (fun s => s.RIP = 0x120c66) (atFlags StatusFlags.CF (adcR64R64Effect 0x120c66 7 2))
      [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 7, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120c66 7 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120c66 0x48 0xd7 c (by decide) (by decide))) pre_rip
  have f404 : InstrSpec 0x120c69 [0x4C, 0x01, 0xEE] (fun s => s.RIP = 0x120c69) (addR64R64Effect 0x120c69 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120c69 6 13).toInstrSpec (add_r64_r64_effect_step 0x120c69 0x4c 0xee (by decide) (by decide)) pre_rip
  have f405 : InstrSpec 0x120c6c [0x4C, 0x11, 0xFF] (fun s => s.RIP = 0x120c6c) (atFlags StatusFlags.CF (adcR64R64Effect 0x120c6c 7 15))
      [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 7, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120c6c 7 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120c6c 0x4c 0xff c (by decide) (by decide))) pre_rip
  have f406 : InstrSpec 0x120c6f [0x49, 0x0F, 0xAC, 0xC8, 0x34] (fun s => s.RIP = 0x120c6f) (shrdR64R64Effect 0x120c6f 5 8 1 52)
      [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrdR64R64Effect_footprint 0x120c6f 5 8 1 52).toInstrSpec (shrd_r64_r64_imm8_effect_step 0x120c6f 0x49 (by decide) 0xc8 (by decide) 0x34) pre_rip
  have f407 : InstrSpec 0x120c74 [0x48, 0xC1, 0xE9, 0x34] (fun s => s.RIP = 0x120c74) (shrR64Effect 0x120c74 4 1 52)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x120c74 4 1 52).toInstrSpec (shr_r64_imm8_effect_step 0x120c74 0x48 0xe9 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f408 : InstrSpec 0x120c78 [0x49, 0x89, 0xF9] (fun s => s.RIP = 0x120c78) (movR64R64Effect 0x120c78 9 7)
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x120c78 9 7).toInstrSpec (mov_r64_r64_effect_step 0x120c78 0x49 0xf9 (by decide) (by decide)) pre_rip
  have f409 : InstrSpec 0x120c7b [0x48, 0x0F, 0xA4, 0xF7, 0x0C] (fun s => s.RIP = 0x120c7b) (shldR64R64Effect 0x120c7b 5 7 6 12)
      [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x120c7b 5 7 6 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x120c7b 0x48 (by decide) 0xf7 (by decide) 0xc) pre_rip
  have f410 : InstrSpec 0x120c80 [0x49, 0xC1, 0xE9, 0x34] (fun s => s.RIP = 0x120c80) (shrR64Effect 0x120c80 4 9 52)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x120c80 4 9 52).toInstrSpec (shr_r64_imm8_effect_step 0x120c80 0x49 0xe9 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f411 : InstrSpec 0x120c84 [0x48, 0x21, 0xDE] (fun s => s.RIP = 0x120c84) (andR64R64Effect 0x120c84 6 3)
      [.gpr 6, .gpr 3] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120c84 6 3).toInstrSpec (and_r64_r64_effect_step 0x120c84 0x48 0xde (by decide) (by decide)) pre_rip
  have f412 : InstrSpec 0x120c87 [0x49, 0x0F, 0xAF, 0xCA] (fun s => s.RIP = 0x120c87) (imulR64R64Effect 0x120c87 4 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x120c87 4 1 10).toInstrSpec (imul_r64_r64_effect_step 0x120c87 0x49 (by decide) 0xca (by decide)) pre_rip
  have f413 : InstrSpec 0x120c8b [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x120c8b) (movR64R64Effect 0x120c8b 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120c8b 0 8).toInstrSpec (mov_r64_r64_effect_step 0x120c8b 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f414 : InstrSpec 0x120c8e [0x49, 0xF7, 0xE2] (fun s => s.RIP = 0x120c8e) (mulR64Effect 0x120c8e 10)
      [.gpr 10, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120c8e 10).toInstrSpec (mul_r64_effect_step 0x120c8e 0x49 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f415 : InstrSpec 0x120c91 [0x4C, 0x8B, 0x44, 0x24, 0x60] (LoadPre 0x120c91 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x120c91 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120c91 8 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x120c91 8 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x120c91 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f416 : InstrSpec 0x120c96 [0x49, 0x21, 0xD8] (fun s => s.RIP = 0x120c96) (andR64R64Effect 0x120c96 8 3)
      [.gpr 8, .gpr 3] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120c96 8 3).toInstrSpec (and_r64_r64_effect_step 0x120c96 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f417 : InstrSpec 0x120c99 [0x49, 0x01, 0xC0] (fun s => s.RIP = 0x120c99) (addR64R64Effect 0x120c99 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120c99 8 0).toInstrSpec (add_r64_r64_effect_step 0x120c99 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f418 : InstrSpec 0x120c9c [0x48, 0x11, 0xCA] (fun s => s.RIP = 0x120c9c) (atFlags StatusFlags.CF (adcR64R64Effect 0x120c9c 2 1))
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120c9c 2 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120c9c 0x48 0xca c (by decide) (by decide))) pre_rip
  have f419 : InstrSpec 0x120c9f [0x49, 0x01, 0xF8] (fun s => s.RIP = 0x120c9f) (addR64R64Effect 0x120c9f 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120c9f 8 7).toInstrSpec (add_r64_r64_effect_step 0x120c9f 0x49 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 921) (RestInside.out (n := 921) f400 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 922) f400 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 923) (ρ' := [(0, 913), (1, 903), (2, 914), (3, 907), (4, 4), (5, 872), (6, 921), (7, 919), (8, 900), (9, 843), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (16, 922), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c5e) f400 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 924) (RestInside.out (n := 924) f401 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 925) (ρ' := [(0, 913), (1, 903), (2, 914), (3, 907), (4, 4), (5, 872), (6, 921), (7, 924), (8, 900), (9, 843), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c63) f401 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 926) (RestInside.out (n := 926) f402 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 927) f402 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 928) (ρ' := [(0, 913), (1, 903), (2, 914), (3, 907), (4, 4), (5, 872), (6, 926), (7, 924), (8, 900), (9, 843), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (16, 927), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c66) f402 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 929) (RestInside.out (n := 929) f403 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 930) (ρ' := [(0, 913), (1, 903), (2, 914), (3, 907), (4, 4), (5, 872), (6, 926), (7, 929), (8, 900), (9, 843), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c69) f403 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 931) (RestInside.out (n := 931) f404 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 932) f404 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 933) (ρ' := [(0, 913), (1, 903), (2, 914), (3, 907), (4, 4), (5, 872), (6, 931), (7, 929), (8, 900), (9, 843), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (16, 932), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c6c) f404 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 934) (RestInside.out (n := 934) f405 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 935) (ρ' := [(0, 913), (1, 903), (2, 914), (3, 907), (4, 4), (5, 872), (6, 931), (7, 934), (8, 900), (9, 843), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c6f) f405 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 936) (RestInside.out (n := 936) f406 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 937) (ρ' := [(0, 913), (1, 903), (2, 914), (3, 907), (4, 4), (5, 872), (6, 931), (7, 934), (8, 936), (9, 843), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c74) f406 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 938) (RestInside.out (n := 938) f407 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 939) (ρ' := [(0, 913), (1, 938), (2, 914), (3, 907), (4, 4), (5, 872), (6, 931), (7, 934), (8, 936), (9, 843), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c78) f407 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 940) (RestInside.out (n := 940) f408 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 941) (ρ' := [(0, 913), (1, 938), (2, 914), (3, 907), (4, 4), (5, 872), (6, 931), (7, 934), (8, 936), (9, 940), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c7b) f408 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 942) (RestInside.out (n := 942) f409 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 943) (ρ' := [(0, 913), (1, 938), (2, 914), (3, 907), (4, 4), (5, 872), (6, 931), (7, 942), (8, 936), (9, 940), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c80) f409 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 944) (RestInside.out (n := 944) f410 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 945) (ρ' := [(0, 913), (1, 938), (2, 914), (3, 907), (4, 4), (5, 872), (6, 931), (7, 942), (8, 936), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c84) f410 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 946) (RestInside.out (n := 946) f411 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 947) (ρ' := [(0, 913), (1, 938), (2, 914), (3, 907), (4, 4), (5, 872), (6, 946), (7, 942), (8, 936), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c87) f411 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 948) (RestInside.out (n := 948) f412 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 949) (ρ' := [(0, 913), (1, 948), (2, 914), (3, 907), (4, 4), (5, 872), (6, 946), (7, 942), (8, 936), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c8b) f412 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 950) (RestInside.out (n := 950) f413 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 951) (ρ' := [(0, 950), (1, 948), (2, 914), (3, 907), (4, 4), (5, 872), (6, 946), (7, 942), (8, 936), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c8e) f413 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 952) (RestInside.out (n := 952) f414 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 953) f414 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 954) (ρ' := [(0, 952), (1, 948), (2, 953), (3, 907), (4, 4), (5, 872), (6, 946), (7, 942), (8, 936), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c91) f414 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 955) (RestInside.out (n := 955) f415 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 956) (ρ' := [(0, 952), (1, 948), (2, 953), (3, 907), (4, 4), (5, 872), (6, 946), (7, 942), (8, 955), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c96) f415 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 957) (RestInside.out (n := 957) f416 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 958) (ρ' := [(0, 952), (1, 948), (2, 953), (3, 907), (4, 4), (5, 872), (6, 946), (7, 942), (8, 957), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c99) f416 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 959) (RestInside.out (n := 959) f417 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 960) f417 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 961) (ρ' := [(0, 952), (1, 948), (2, 953), (3, 907), (4, 4), (5, 872), (6, 946), (7, 942), (8, 959), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (16, 960), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c9c) f417 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 962) (RestInside.out (n := 962) f418 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 963) (ρ' := [(0, 952), (1, 948), (2, 962), (3, 907), (4, 4), (5, 872), (6, 946), (7, 942), (8, 959), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c9f) f418 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 964) (RestInside.out (n := 964) f419 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 965) f419 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 966) (ρ' := [(0, 952), (1, 948), (2, 962), (3, 907), (4, 4), (5, 872), (6, 946), (7, 942), (8, 964), (9, 944), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (16, 965), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ca2) f419 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_21 code

theorem rest_l12065f_19 [Bindings] (code : CodeMap) :
    Rest (n := 875) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 869), (1, 815), (2, 870), (3, 739), (4, 4), (5, 872), (6, 865), (7, 863), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]
      56 0x120c05 bytes_l12065f_19 b_l12065f_19 := by
  have f380 : InstrSpec 0x120c05 [0x49, 0x21, 0xCB] (fun s => s.RIP = 0x120c05) (andR64R64Effect 0x120c05 11 1)
      [.gpr 11, .gpr 1] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120c05 11 1).toInstrSpec (and_r64_r64_effect_step 0x120c05 0x49 0xcb (by decide) (by decide)) pre_rip
  have f381 : InstrSpec 0x120c08 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x120c08 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x120c08 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120c08 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120c08 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x120c08 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f382 : InstrSpec 0x120c0d [0x48, 0xF7, 0x64, 0x24, 0x48] (LoadPre 0x120c0d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x120c0d + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120c0d 5 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x120c0d 5 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mul_m64_effect_step 0x120c0d 0x48 (by decide) (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f383 : InstrSpec 0x120c12 [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x120c12) (movR64R64Effect 0x120c12 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x120c12 3 2).toInstrSpec (mov_r64_r64_effect_step 0x120c12 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f384 : InstrSpec 0x120c15 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x120c15) (movR64R64Effect 0x120c15 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x120c15 10 0).toInstrSpec (mov_r64_r64_effect_step 0x120c15 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f385 : InstrSpec 0x120c18 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x120c18 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x120c18 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120c18 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120c18 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x120c18 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f386 : InstrSpec 0x120c1d [0x48, 0xF7, 0x64, 0x24, 0x30] (LoadPre 0x120c1d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x120c1d + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120c1d 5 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x120c1d 5 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mul_m64_effect_step 0x120c1d 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f387 : InstrSpec 0x120c22 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x120c22) (movR64R64Effect 0x120c22 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x120c22 1 2).toInstrSpec (mov_r64_r64_effect_step 0x120c22 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f388 : InstrSpec 0x120c25 [0x49, 0x89, 0xC0] (fun s => s.RIP = 0x120c25) (movR64R64Effect 0x120c25 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x120c25 8 0).toInstrSpec (mov_r64_r64_effect_step 0x120c25 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f389 : InstrSpec 0x120c28 [0x4D, 0x01, 0xD0] (fun s => s.RIP = 0x120c28) (addR64R64Effect 0x120c28 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120c28 8 10).toInstrSpec (add_r64_r64_effect_step 0x120c28 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f390 : InstrSpec 0x120c2b [0x48, 0x11, 0xD9] (fun s => s.RIP = 0x120c2b) (atFlags StatusFlags.CF (adcR64R64Effect 0x120c2b 1 3))
      [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120c2b 1 3).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120c2b 0x48 0xd9 c (by decide) (by decide))) pre_rip
  have f391 : InstrSpec 0x120c2e [0x4D, 0x01, 0xE0] (fun s => s.RIP = 0x120c2e) (addR64R64Effect 0x120c2e 8 12)
      [.gpr 8, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120c2e 8 12).toInstrSpec (add_r64_r64_effect_step 0x120c2e 0x4d 0xe0 (by decide) (by decide)) pre_rip
  have f392 : InstrSpec 0x120c31 [0x4C, 0x11, 0xC9] (fun s => s.RIP = 0x120c31) (atFlags StatusFlags.CF (adcR64R64Effect 0x120c31 1 9))
      [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120c31 1 9).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120c31 0x4c 0xc9 c (by decide) (by decide))) pre_rip
  have f393 : InstrSpec 0x120c34 [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x120c34) (movR64R64Effect 0x120c34 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120c34 0 8).toInstrSpec (mov_r64_r64_effect_step 0x120c34 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f394 : InstrSpec 0x120c37 [0x48, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x120c37) (movR64Imm64Effect 0x120c37 3 0xfffffffffffff)
      [] [] [.reg 3, .rip] :=
    (movR64Imm64Effect_footprint 0x120c37 3 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x120c37 0x48 0xbb (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f395 : InstrSpec 0x120c41 [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x120c41) (andR64R64Effect 0x120c41 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120c41 0 3).toInstrSpec (and_r64_r64_effect_step 0x120c41 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f396 : InstrSpec 0x120c44 [0x49, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x120c44) (movR64Imm64Effect 0x120c44 10 0x1000003d10)
      [] [] [.reg 10, .rip] :=
    (movR64Imm64Effect_footprint 0x120c44 10 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x120c44 0x49 0xba (by decide) (by decide) 0x1000003d10) pre_rip
  have f397 : InstrSpec 0x120c4e [0x49, 0xF7, 0xE2] (fun s => s.RIP = 0x120c4e) (mulR64Effect 0x120c4e 10)
      [.gpr 10, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120c4e 10).toInstrSpec (mul_r64_effect_step 0x120c4e 0x49 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f398 : InstrSpec 0x120c51 [0x48, 0x03, 0x74, 0x24, 0x18] (LoadPre 0x120c51 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120c51 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x120c51 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (addR64M64Effect_footprint 0x120c51 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (add_r64_m64_effect_step 0x120c51 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f399 : InstrSpec 0x120c56 [0x48, 0x13, 0x7C, 0x24, 0x10] (LoadPre 0x120c56 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120c56 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x120c56 7 (.sib 4 none 0 (.d8 0x10))))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 7, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x120c56 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x120c56 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 875) (RestInside.out (n := 875) f380 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 876) (ρ' := [(0, 869), (1, 815), (2, 870), (3, 739), (4, 4), (5, 872), (6, 865), (7, 863), (8, 776), (9, 843), (10, 669), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c08) f380 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 877) (RestInside.out (n := 877) f381 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 878) (ρ' := [(0, 877), (1, 815), (2, 870), (3, 739), (4, 4), (5, 872), (6, 865), (7, 863), (8, 776), (9, 843), (10, 669), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c0d) f381 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 879) (RestInside.out (n := 879) f382 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 880) f382 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 881) (ρ' := [(0, 879), (1, 815), (2, 880), (3, 739), (4, 4), (5, 872), (6, 865), (7, 863), (8, 776), (9, 843), (10, 669), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c12) f382 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 882) (RestInside.out (n := 882) f383 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 883) (ρ' := [(0, 879), (1, 815), (2, 880), (3, 882), (4, 4), (5, 872), (6, 865), (7, 863), (8, 776), (9, 843), (10, 669), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c15) f383 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 884) (RestInside.out (n := 884) f384 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 885) (ρ' := [(0, 879), (1, 815), (2, 880), (3, 882), (4, 4), (5, 872), (6, 865), (7, 863), (8, 776), (9, 843), (10, 884), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c18) f384 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 886) (RestInside.out (n := 886) f385 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 887) (ρ' := [(0, 886), (1, 815), (2, 880), (3, 882), (4, 4), (5, 872), (6, 865), (7, 863), (8, 776), (9, 843), (10, 884), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c1d) f385 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 888) (RestInside.out (n := 888) f386 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 889) f386 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 890) (ρ' := [(0, 888), (1, 815), (2, 889), (3, 882), (4, 4), (5, 872), (6, 865), (7, 863), (8, 776), (9, 843), (10, 884), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c22) f386 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 891) (RestInside.out (n := 891) f387 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 892) (ρ' := [(0, 888), (1, 891), (2, 889), (3, 882), (4, 4), (5, 872), (6, 865), (7, 863), (8, 776), (9, 843), (10, 884), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c25) f387 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 893) (RestInside.out (n := 893) f388 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 894) (ρ' := [(0, 888), (1, 891), (2, 889), (3, 882), (4, 4), (5, 872), (6, 865), (7, 863), (8, 893), (9, 843), (10, 884), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c28) f388 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 895) (RestInside.out (n := 895) f389 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 896) f389 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 897) (ρ' := [(0, 888), (1, 891), (2, 889), (3, 882), (4, 4), (5, 872), (6, 865), (7, 863), (8, 895), (9, 843), (10, 884), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (16, 896), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c2b) f389 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 898) (RestInside.out (n := 898) f390 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 899) (ρ' := [(0, 888), (1, 898), (2, 889), (3, 882), (4, 4), (5, 872), (6, 865), (7, 863), (8, 895), (9, 843), (10, 884), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c2e) f390 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 900) (RestInside.out (n := 900) f391 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 901) f391 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 902) (ρ' := [(0, 888), (1, 898), (2, 889), (3, 882), (4, 4), (5, 872), (6, 865), (7, 863), (8, 900), (9, 843), (10, 884), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (16, 901), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c31) f391 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 903) (RestInside.out (n := 903) f392 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 904) (ρ' := [(0, 888), (1, 903), (2, 889), (3, 882), (4, 4), (5, 872), (6, 865), (7, 863), (8, 900), (9, 843), (10, 884), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c34) f392 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 905) (RestInside.out (n := 905) f393 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 906) (ρ' := [(0, 905), (1, 903), (2, 889), (3, 882), (4, 4), (5, 872), (6, 865), (7, 863), (8, 900), (9, 843), (10, 884), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c37) f393 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 907) (RestInside.out (n := 907) f394 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 908) (ρ' := [(0, 905), (1, 903), (2, 889), (3, 907), (4, 4), (5, 872), (6, 865), (7, 863), (8, 900), (9, 843), (10, 884), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c41) f394 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 909) (RestInside.out (n := 909) f395 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 910) (ρ' := [(0, 909), (1, 903), (2, 889), (3, 907), (4, 4), (5, 872), (6, 865), (7, 863), (8, 900), (9, 843), (10, 884), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c44) f395 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 911) (RestInside.out (n := 911) f396 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 912) (ρ' := [(0, 909), (1, 903), (2, 889), (3, 907), (4, 4), (5, 872), (6, 865), (7, 863), (8, 900), (9, 843), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c4e) f396 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 913) (RestInside.out (n := 913) f397 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 914) f397 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 915) (ρ' := [(0, 913), (1, 903), (2, 914), (3, 907), (4, 4), (5, 872), (6, 865), (7, 863), (8, 900), (9, 843), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c51) f397 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 916) (RestInside.out (n := 916) f398 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 917) f398 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 918) (ρ' := [(0, 913), (1, 903), (2, 914), (3, 907), (4, 4), (5, 872), (6, 916), (7, 863), (8, 900), (9, 843), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (16, 917), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c56) f398 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 919) (RestInside.out (n := 919) f399 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 920) (ρ' := [(0, 913), (1, 903), (2, 914), (3, 907), (4, 4), (5, 872), (6, 916), (7, 919), (8, 900), (9, 843), (10, 911), (11, 875), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c5b) f399 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_20 code

theorem rest_l12065f_18 [Bindings] (code : CodeMap) :
    Rest (n := 834) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 821), (1, 815), (2, 822), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 829), (12, 811), (13, 832), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]
      76 0x120bb4 bytes_l12065f_18 b_l12065f_18 := by
  have f360 : InstrSpec 0x120bb4 [0x49, 0x01, 0xF3] (fun s => s.RIP = 0x120bb4) (addR64R64Effect 0x120bb4 11 6)
      [.gpr 11, .gpr 6] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120bb4 11 6).toInstrSpec (add_r64_r64_effect_step 0x120bb4 0x49 0xf3 (by decide) (by decide)) pre_rip
  have f361 : InstrSpec 0x120bb7 [0x49, 0x83, 0xD5, 0x00] (fun s => s.RIP = 0x120bb7) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x120bb7 13 0x0))
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 13, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x120bb7 13 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x120bb7 0x49 0xd5 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f362 : InstrSpec 0x120bbb [0x4D, 0x89, 0xE1] (fun s => s.RIP = 0x120bbb) (movR64R64Effect 0x120bbb 9 12)
      [.gpr 12] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x120bbb 9 12).toInstrSpec (mov_r64_r64_effect_step 0x120bbb 0x4d 0xe1 (by decide) (by decide)) pre_rip
  have f363 : InstrSpec 0x120bbe [0x49, 0x0F, 0xA4, 0xEC, 0x0C] (fun s => s.RIP = 0x120bbe) (shldR64R64Effect 0x120bbe 5 12 5 12)
      [.gpr 12, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x120bbe 5 12 5 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x120bbe 0x49 (by decide) 0xec (by decide) 0xc) pre_rip
  have f364 : InstrSpec 0x120bc3 [0x49, 0xC1, 0xE9, 0x34] (fun s => s.RIP = 0x120bc3) (shrR64Effect 0x120bc3 4 9 52)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x120bc3 4 9 52).toInstrSpec (shr_r64_imm8_effect_step 0x120bc3 0x49 0xe9 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f365 : InstrSpec 0x120bc7 [0x4D, 0x89, 0xEF] (fun s => s.RIP = 0x120bc7) (movR64R64Effect 0x120bc7 15 13)
      [.gpr 13] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x120bc7 15 13).toInstrSpec (mov_r64_r64_effect_step 0x120bc7 0x4d 0xef (by decide) (by decide)) pre_rip
  have f366 : InstrSpec 0x120bca [0x49, 0xC1, 0xEF, 0x34] (fun s => s.RIP = 0x120bca) (shrR64Effect 0x120bca 4 15 52)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x120bca 4 15 52).toInstrSpec (shr_r64_imm8_effect_step 0x120bca 0x49 0xef 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f367 : InstrSpec 0x120bce [0x4D, 0x0F, 0xA4, 0xDD, 0x0C] (fun s => s.RIP = 0x120bce) (shldR64R64Effect 0x120bce 5 13 11 12)
      [.gpr 13, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x120bce 5 13 11 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x120bce 0x4d (by decide) 0xdd (by decide) 0xc) pre_rip
  have f368 : InstrSpec 0x120bd3 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x120bd3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120bd3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120bd3 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120bd3 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x120bd3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f369 : InstrSpec 0x120bd8 [0x48, 0xF7, 0xE7] (fun s => s.RIP = 0x120bd8) (mulR64Effect 0x120bd8 7)
      [.gpr 7, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120bd8 7).toInstrSpec (mul_r64_effect_step 0x120bd8 0x48 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f370 : InstrSpec 0x120bdb [0x48, 0x89, 0x54, 0x24, 0x10] (StorePre 0x120bdb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120bdb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120bdb 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120bdb 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x120bdb 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f371 : InstrSpec 0x120be0 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x120be0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120be0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120be0 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120be0 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x120be0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f372 : InstrSpec 0x120be5 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x120be5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120be5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120be5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120be5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x120be5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f373 : InstrSpec 0x120bea [0x48, 0xF7, 0x64, 0x24, 0x58] (LoadPre 0x120bea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x120bea + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120bea 5 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x120bea 5 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mul_m64_effect_step 0x120bea 0x48 (by decide) (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f374 : InstrSpec 0x120bef [0x48, 0x89, 0xD7] (fun s => s.RIP = 0x120bef) (movR64R64Effect 0x120bef 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x120bef 7 2).toInstrSpec (mov_r64_r64_effect_step 0x120bef 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f375 : InstrSpec 0x120bf2 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x120bf2) (movR64R64Effect 0x120bf2 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x120bf2 6 0).toInstrSpec (mov_r64_r64_effect_step 0x120bf2 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f376 : InstrSpec 0x120bf5 [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x120bf5) (movR64R64Effect 0x120bf5 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120bf5 0 10).toInstrSpec (mov_r64_r64_effect_step 0x120bf5 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f377 : InstrSpec 0x120bf8 [0x48, 0xF7, 0x64, 0x24, 0x50] (LoadPre 0x120bf8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x120bf8 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120bf8 5 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x120bf8 5 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mul_m64_effect_step 0x120bf8 0x48 (by decide) (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f378 : InstrSpec 0x120bfd [0x48, 0x89, 0xC5] (fun s => s.RIP = 0x120bfd) (movR64R64Effect 0x120bfd 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x120bfd 5 0).toInstrSpec (mov_r64_r64_effect_step 0x120bfd 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f379 : InstrSpec 0x120c00 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x120c00 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120c00 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120c00 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120c00 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x120c00 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 834) (RestInside.out (n := 834) f360 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 835) f360 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 836) (ρ' := [(0, 821), (1, 815), (2, 822), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 834), (12, 811), (13, 832), (14, 638), (15, 722), (16, 835), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bb7) f360 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 837) (RestInside.out (n := 837) f361 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 838) (ρ' := [(0, 821), (1, 815), (2, 822), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 834), (12, 811), (13, 837), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bbb) f361 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 839) (RestInside.out (n := 839) f362 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 840) (ρ' := [(0, 821), (1, 815), (2, 822), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 839), (10, 669), (11, 834), (12, 811), (13, 837), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bbe) f362 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 841) (RestInside.out (n := 841) f363 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 842) (ρ' := [(0, 821), (1, 815), (2, 822), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 839), (10, 669), (11, 834), (12, 841), (13, 837), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bc3) f363 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 843) (RestInside.out (n := 843) f364 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 844) (ρ' := [(0, 821), (1, 815), (2, 822), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 837), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bc7) f364 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 845) (RestInside.out (n := 845) f365 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 846) (ρ' := [(0, 821), (1, 815), (2, 822), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 837), (14, 638), (15, 845), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bca) f365 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 847) (RestInside.out (n := 847) f366 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 848) (ρ' := [(0, 821), (1, 815), (2, 822), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 837), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bce) f366 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 849) (RestInside.out (n := 849) f367 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 850) (ρ' := [(0, 821), (1, 815), (2, 822), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bd3) f367 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 851) (RestInside.out (n := 851) f368 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 852) (ρ' := [(0, 851), (1, 815), (2, 822), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bd8) f368 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 853) (RestInside.out (n := 853) f369 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 854) f369 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 855) (ρ' := [(0, 853), (1, 815), (2, 854), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bdb) f369 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 856) (RestInside.exec (n := 856) (ρ' := [(0, 853), (1, 815), (2, 854), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120be0) f370 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 857) (RestInside.exec (n := 857) (ρ' := [(0, 853), (1, 815), (2, 854), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120be5) f371 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 858) (RestInside.out (n := 858) f372 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 859) (ρ' := [(0, 858), (1, 815), (2, 854), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bea) f372 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 860) (RestInside.out (n := 860) f373 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 861) f373 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 862) (ρ' := [(0, 860), (1, 815), (2, 861), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bef) f373 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 863) (RestInside.out (n := 863) f374 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 864) (ρ' := [(0, 860), (1, 815), (2, 861), (3, 739), (4, 4), (5, 808), (6, 746), (7, 863), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bf2) f374 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 865) (RestInside.out (n := 865) f375 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 866) (ρ' := [(0, 860), (1, 815), (2, 861), (3, 739), (4, 4), (5, 808), (6, 865), (7, 863), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bf5) f375 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 867) (RestInside.out (n := 867) f376 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 868) (ρ' := [(0, 867), (1, 815), (2, 861), (3, 739), (4, 4), (5, 808), (6, 865), (7, 863), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bf8) f376 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 869) (RestInside.out (n := 869) f377 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 870) f377 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 871) (ρ' := [(0, 869), (1, 815), (2, 870), (3, 739), (4, 4), (5, 808), (6, 865), (7, 863), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bfd) f377 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 872) (RestInside.out (n := 872) f378 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 873) (ρ' := [(0, 869), (1, 815), (2, 870), (3, 739), (4, 4), (5, 872), (6, 865), (7, 863), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c00) f378 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 874) (RestInside.exec (n := 874) (ρ' := [(0, 869), (1, 815), (2, 870), (3, 739), (4, 4), (5, 872), (6, 865), (7, 863), (8, 776), (9, 843), (10, 669), (11, 834), (12, 841), (13, 849), (14, 638), (15, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120c05) f379 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l12065f_19 code

theorem rest_l12065f_17 [Bindings] (code : CodeMap) :
    Rest (n := 787) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 782), (1, 768), (2, 783), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 776), (9, 778), (10, 669), (11, 762), (12, 785), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]
      96 0x120b62 bytes_l12065f_17 b_l12065f_17 := by
  have f340 : InstrSpec 0x120b62 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x120b62) (movR64R64Effect 0x120b62 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x120b62 1 0).toInstrSpec (mov_r64_r64_effect_step 0x120b62 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f341 : InstrSpec 0x120b65 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x120b65 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x120b65 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120b65 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120b65 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x120b65 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f342 : InstrSpec 0x120b6a [0x48, 0x8B, 0x7C, 0x24, 0x40] (LoadPre 0x120b6a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x120b6a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120b6a 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x120b6a 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x120b6a 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f343 : InstrSpec 0x120b6f [0x48, 0xF7, 0xE7] (fun s => s.RIP = 0x120b6f) (mulR64Effect 0x120b6f 7)
      [.gpr 7, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120b6f 7).toInstrSpec (mul_r64_effect_step 0x120b6f 0x48 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f344 : InstrSpec 0x120b72 [0x48, 0x89, 0xC5] (fun s => s.RIP = 0x120b72) (movR64R64Effect 0x120b72 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x120b72 5 0).toInstrSpec (mov_r64_r64_effect_step 0x120b72 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f345 : InstrSpec 0x120b75 [0x4C, 0x01, 0xC9] (fun s => s.RIP = 0x120b75) (addR64R64Effect 0x120b75 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120b75 1 9).toInstrSpec (add_r64_r64_effect_step 0x120b75 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f346 : InstrSpec 0x120b78 [0x4D, 0x11, 0xC4] (fun s => s.RIP = 0x120b78) (atFlags StatusFlags.CF (adcR64R64Effect 0x120b78 12 8))
      [.gpr 12, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120b78 12 8).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120b78 0x4d 0xc4 c (by decide) (by decide))) pre_rip
  have f347 : InstrSpec 0x120b7b [0x48, 0x01, 0xCD] (fun s => s.RIP = 0x120b7b) (addR64R64Effect 0x120b7b 5 1)
      [.gpr 5, .gpr 1] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120b7b 5 1).toInstrSpec (add_r64_r64_effect_step 0x120b7b 0x48 0xcd (by decide) (by decide)) pre_rip
  have f348 : InstrSpec 0x120b7e [0x49, 0x11, 0xD4] (fun s => s.RIP = 0x120b7e) (atFlags StatusFlags.CF (adcR64R64Effect 0x120b7e 12 2))
      [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120b7e 12 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120b7e 0x49 0xd4 c (by decide) (by decide))) pre_rip
  have f349 : InstrSpec 0x120b81 [0x4C, 0x01, 0xFD] (fun s => s.RIP = 0x120b81) (addR64R64Effect 0x120b81 5 15)
      [.gpr 5, .gpr 15] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120b81 5 15).toInstrSpec (add_r64_r64_effect_step 0x120b81 0x4c 0xfd (by decide) (by decide)) pre_rip
  have f350 : InstrSpec 0x120b84 [0x49, 0x11, 0xDC] (fun s => s.RIP = 0x120b84) (atFlags StatusFlags.CF (adcR64R64Effect 0x120b84 12 3))
      [.gpr 12, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 12, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120b84 12 3).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120b84 0x49 0xdc c (by decide) (by decide))) pre_rip
  have f351 : InstrSpec 0x120b87 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x120b87) (movR64R64Effect 0x120b87 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120b87 0 5).toInstrSpec (mov_r64_r64_effect_step 0x120b87 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f352 : InstrSpec 0x120b8a [0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x120b8a) (movR64Imm64Effect 0x120b8a 1 0xfffffffffffff)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x120b8a 1 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x120b8a 0x48 0xb9 (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f353 : InstrSpec 0x120b94 [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x120b94) (andR64R64Effect 0x120b94 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120b94 0 1).toInstrSpec (and_r64_r64_effect_step 0x120b94 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f354 : InstrSpec 0x120b97 [0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x120b97) (movR64Imm64Effect 0x120b97 2 0x1000003d10)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x120b97 2 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x120b97 0x48 0xba (by decide) (by decide) 0x1000003d10) pre_rip
  have f355 : InstrSpec 0x120ba1 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x120ba1) (mulR64Effect 0x120ba1 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120ba1 2).toInstrSpec (mul_r64_effect_step 0x120ba1 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f356 : InstrSpec 0x120ba4 [0x4C, 0x03, 0x5C, 0x24, 0x70] (LoadPre 0x120ba4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x120ba4 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x120ba4 11 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 11, .gpr 4] [] [.reg 11, .flags, .rip] :=
    (addR64M64Effect_footprint 0x120ba4 11 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (add_r64_m64_effect_step 0x120ba4 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f357 : InstrSpec 0x120ba9 [0x4C, 0x13, 0x6C, 0x24, 0x18] (LoadPre 0x120ba9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120ba9 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x120ba9 13 (.sib 4 none 0 (.d8 0x18))))
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 13, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x120ba9 13 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x120ba9 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f358 : InstrSpec 0x120bae [0x49, 0x01, 0xC3] (fun s => s.RIP = 0x120bae) (addR64R64Effect 0x120bae 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120bae 11 0).toInstrSpec (add_r64_r64_effect_step 0x120bae 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f359 : InstrSpec 0x120bb1 [0x49, 0x11, 0xD5] (fun s => s.RIP = 0x120bb1) (atFlags StatusFlags.CF (adcR64R64Effect 0x120bb1 13 2))
      [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 13, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120bb1 13 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120bb1 0x49 0xd5 c (by decide) (by decide))) pre_rip
  refine Rest.ofInside (n := 787) (RestInside.out (n := 787) f340 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 788) (ρ' := [(0, 782), (1, 787), (2, 783), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 776), (9, 778), (10, 669), (11, 762), (12, 785), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b65) f340 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 789) (RestInside.out (n := 789) f341 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 790) (ρ' := [(0, 789), (1, 787), (2, 783), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 776), (9, 778), (10, 669), (11, 762), (12, 785), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b6a) f341 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 791) (RestInside.out (n := 791) f342 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 792) (ρ' := [(0, 789), (1, 787), (2, 783), (3, 739), (4, 4), (5, 689), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 762), (12, 785), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b6f) f342 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 793) (RestInside.out (n := 793) f343 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 794) f343 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 795) (ρ' := [(0, 793), (1, 787), (2, 794), (3, 739), (4, 4), (5, 689), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 762), (12, 785), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b72) f343 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 796) (RestInside.out (n := 796) f344 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 797) (ρ' := [(0, 793), (1, 787), (2, 794), (3, 739), (4, 4), (5, 796), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 762), (12, 785), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b75) f344 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 798) (RestInside.out (n := 798) f345 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 799) f345 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 800) (ρ' := [(0, 793), (1, 798), (2, 794), (3, 739), (4, 4), (5, 796), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 762), (12, 785), (13, 764), (14, 638), (15, 722), (16, 799), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b78) f345 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 801) (RestInside.out (n := 801) f346 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 802) (ρ' := [(0, 793), (1, 798), (2, 794), (3, 739), (4, 4), (5, 796), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 762), (12, 801), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b7b) f346 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 803) (RestInside.out (n := 803) f347 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 804) f347 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 805) (ρ' := [(0, 793), (1, 798), (2, 794), (3, 739), (4, 4), (5, 803), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 762), (12, 801), (13, 764), (14, 638), (15, 722), (16, 804), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b7e) f347 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 806) (RestInside.out (n := 806) f348 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 807) (ρ' := [(0, 793), (1, 798), (2, 794), (3, 739), (4, 4), (5, 803), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 762), (12, 806), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b81) f348 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 808) (RestInside.out (n := 808) f349 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 809) f349 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 810) (ρ' := [(0, 793), (1, 798), (2, 794), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 762), (12, 806), (13, 764), (14, 638), (15, 722), (16, 809), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b84) f349 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 811) (RestInside.out (n := 811) f350 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 812) (ρ' := [(0, 793), (1, 798), (2, 794), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 762), (12, 811), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b87) f350 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 813) (RestInside.out (n := 813) f351 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 814) (ρ' := [(0, 813), (1, 798), (2, 794), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 762), (12, 811), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b8a) f351 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 815) (RestInside.out (n := 815) f352 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 816) (ρ' := [(0, 813), (1, 815), (2, 794), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 762), (12, 811), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b94) f352 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 817) (RestInside.out (n := 817) f353 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 818) (ρ' := [(0, 817), (1, 815), (2, 794), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 762), (12, 811), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b97) f353 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 819) (RestInside.out (n := 819) f354 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 820) (ρ' := [(0, 817), (1, 815), (2, 819), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 762), (12, 811), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ba1) f354 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 821) (RestInside.out (n := 821) f355 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 822) f355 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 823) (ρ' := [(0, 821), (1, 815), (2, 822), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 762), (12, 811), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ba4) f355 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 824) (RestInside.out (n := 824) f356 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 825) f356 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 826) (ρ' := [(0, 821), (1, 815), (2, 822), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 824), (12, 811), (13, 764), (14, 638), (15, 722), (16, 825), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ba9) f356 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 827) (RestInside.out (n := 827) f357 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 828) (ρ' := [(0, 821), (1, 815), (2, 822), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 824), (12, 811), (13, 827), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bae) f357 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 829) (RestInside.out (n := 829) f358 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 830) f358 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 831) (ρ' := [(0, 821), (1, 815), (2, 822), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 829), (12, 811), (13, 827), (14, 638), (15, 722), (16, 830), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bb1) f358 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 832) (RestInside.out (n := 832) f359 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 833) (ρ' := [(0, 821), (1, 815), (2, 822), (3, 739), (4, 4), (5, 808), (6, 746), (7, 791), (8, 776), (9, 778), (10, 669), (11, 829), (12, 811), (13, 832), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120bb4) f359 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_18 code

theorem rest_l12065f_16 [Bindings] (code : CodeMap) :
    Rest (n := 746) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 741), (1, 732), (2, 735), (3, 739), (4, 4), (5, 689), (6, 744), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]
      116 0x120b0d bytes_l12065f_16 b_l12065f_16 := by
  have f320 : InstrSpec 0x120b0d [0x48, 0x0F, 0xA4, 0xC6, 0x0C] (fun s => s.RIP = 0x120b0d) (shldR64R64Effect 0x120b0d 5 6 0 12)
      [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x120b0d 5 6 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x120b0d 0x48 (by decide) 0xc6 (by decide) 0xc) pre_rip
  have f321 : InstrSpec 0x120b12 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x120b12) (movR64R64Effect 0x120b12 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x120b12 1 0).toInstrSpec (mov_r64_r64_effect_step 0x120b12 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f322 : InstrSpec 0x120b15 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x120b15 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120b15 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120b15 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120b15 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x120b15 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f323 : InstrSpec 0x120b1a [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x120b1a) (mulR64Effect 0x120b1a 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120b1a 8).toInstrSpec (mul_r64_effect_step 0x120b1a 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f324 : InstrSpec 0x120b1d [0x48, 0x89, 0x54, 0x24, 0x18] (StorePre 0x120b1d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120b1d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120b1d 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120b1d 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x120b1d 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f325 : InstrSpec 0x120b22 [0x48, 0x89, 0x44, 0x24, 0x70] (StorePre 0x120b22 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x120b22 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120b22 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120b22 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x120b22 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f326 : InstrSpec 0x120b27 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x120b27 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120b27 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120b27 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120b27 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x120b27 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f327 : InstrSpec 0x120b2c [0x48, 0xF7, 0x64, 0x24, 0x50] (LoadPre 0x120b2c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x120b2c + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120b2c 5 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x120b2c 5 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mul_m64_effect_step 0x120b2c 0x48 (by decide) (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f328 : InstrSpec 0x120b31 [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x120b31) (movR64R64Effect 0x120b31 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x120b31 11 0).toInstrSpec (mov_r64_r64_effect_step 0x120b31 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f329 : InstrSpec 0x120b34 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x120b34) (movR64R64Effect 0x120b34 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x120b34 13 2).toInstrSpec (mov_r64_r64_effect_step 0x120b34 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f330 : InstrSpec 0x120b37 [0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x120b37) (movR64Imm64Effect 0x120b37 0 0xfffffffffffff)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x120b37 0 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x120b37 0x48 0xb8 (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f331 : InstrSpec 0x120b41 [0x48, 0x21, 0xC1] (fun s => s.RIP = 0x120b41) (andR64R64Effect 0x120b41 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120b41 1 0).toInstrSpec (and_r64_r64_effect_step 0x120b41 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f332 : InstrSpec 0x120b44 [0x48, 0x89, 0x4C, 0x24, 0x38] (StorePre 0x120b44 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x120b44 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120b44 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120b44 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x120b44 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f333 : InstrSpec 0x120b49 [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x120b49) (movR64R64Effect 0x120b49 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120b49 0 10).toInstrSpec (mov_r64_r64_effect_step 0x120b49 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f334 : InstrSpec 0x120b4c [0x48, 0xF7, 0x64, 0x24, 0x48] (LoadPre 0x120b4c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x120b4c + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120b4c 5 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x120b4c 5 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mul_m64_effect_step 0x120b4c 0x48 (by decide) (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f335 : InstrSpec 0x120b51 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x120b51) (movR64R64Effect 0x120b51 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x120b51 8 2).toInstrSpec (mov_r64_r64_effect_step 0x120b51 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f336 : InstrSpec 0x120b54 [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x120b54) (movR64R64Effect 0x120b54 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x120b54 9 0).toInstrSpec (mov_r64_r64_effect_step 0x120b54 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f337 : InstrSpec 0x120b57 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x120b57) (movR64R64Effect 0x120b57 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120b57 0 7).toInstrSpec (mov_r64_r64_effect_step 0x120b57 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f338 : InstrSpec 0x120b5a [0x48, 0xF7, 0x64, 0x24, 0x30] (LoadPre 0x120b5a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x120b5a + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120b5a 5 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x120b5a 5 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mul_m64_effect_step 0x120b5a 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f339 : InstrSpec 0x120b5f [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x120b5f) (movR64R64Effect 0x120b5f 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x120b5f 12 2).toInstrSpec (mov_r64_r64_effect_step 0x120b5f 0x49 0xd4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 746) (RestInside.out (n := 746) f320 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 747) (ρ' := [(0, 741), (1, 732), (2, 735), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b12) f320 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 748) (RestInside.out (n := 748) f321 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 749) (ρ' := [(0, 741), (1, 748), (2, 735), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b15) f321 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 750) (RestInside.out (n := 750) f322 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 751) (ρ' := [(0, 750), (1, 748), (2, 735), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b1a) f322 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 752) (RestInside.out (n := 752) f323 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 753) f323 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 754) (ρ' := [(0, 752), (1, 748), (2, 753), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b1d) f323 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 755) (RestInside.exec (n := 755) (ρ' := [(0, 752), (1, 748), (2, 753), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b22) f324 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 756) (RestInside.exec (n := 756) (ρ' := [(0, 752), (1, 748), (2, 753), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b27) f325 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 757) (RestInside.out (n := 757) f326 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 758) (ρ' := [(0, 757), (1, 748), (2, 753), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b2c) f326 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 759) (RestInside.out (n := 759) f327 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 760) f327 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 761) (ρ' := [(0, 759), (1, 748), (2, 760), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b31) f327 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 762) (RestInside.out (n := 762) f328 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 763) (ρ' := [(0, 759), (1, 748), (2, 760), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 693), (9, 705), (10, 669), (11, 762), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b34) f328 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 764) (RestInside.out (n := 764) f329 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 765) (ρ' := [(0, 759), (1, 748), (2, 760), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 693), (9, 705), (10, 669), (11, 762), (12, 663), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b37) f329 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 766) (RestInside.out (n := 766) f330 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 767) (ρ' := [(0, 766), (1, 748), (2, 760), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 693), (9, 705), (10, 669), (11, 762), (12, 663), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b41) f330 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 768) (RestInside.out (n := 768) f331 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 769) (ρ' := [(0, 766), (1, 768), (2, 760), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 693), (9, 705), (10, 669), (11, 762), (12, 663), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b44) f331 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 770) (RestInside.exec (n := 770) (ρ' := [(0, 766), (1, 768), (2, 760), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 693), (9, 705), (10, 669), (11, 762), (12, 663), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b49) f332 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 771) (RestInside.out (n := 771) f333 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 772) (ρ' := [(0, 771), (1, 768), (2, 760), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 693), (9, 705), (10, 669), (11, 762), (12, 663), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b4c) f333 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 773) (RestInside.out (n := 773) f334 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 774) f334 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 775) (ρ' := [(0, 773), (1, 768), (2, 774), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 693), (9, 705), (10, 669), (11, 762), (12, 663), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b51) f334 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 776) (RestInside.out (n := 776) f335 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 777) (ρ' := [(0, 773), (1, 768), (2, 774), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 776), (9, 705), (10, 669), (11, 762), (12, 663), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b54) f335 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 778) (RestInside.out (n := 778) f336 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 779) (ρ' := [(0, 773), (1, 768), (2, 774), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 776), (9, 778), (10, 669), (11, 762), (12, 663), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b57) f336 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 780) (RestInside.out (n := 780) f337 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 781) (ρ' := [(0, 780), (1, 768), (2, 774), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 776), (9, 778), (10, 669), (11, 762), (12, 663), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b5a) f337 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 782) (RestInside.out (n := 782) f338 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 783) f338 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 784) (ρ' := [(0, 782), (1, 768), (2, 783), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 776), (9, 778), (10, 669), (11, 762), (12, 663), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b5f) f338 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 785) (RestInside.out (n := 785) f339 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 786) (ρ' := [(0, 782), (1, 768), (2, 783), (3, 739), (4, 4), (5, 689), (6, 746), (7, 680), (8, 776), (9, 778), (10, 669), (11, 762), (12, 785), (13, 764), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b62) f339 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_17 code

theorem rest_l12065f_15 [Bindings] (code : CodeMap) :
    Rest (n := 700) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 695), (1, 645), (2, 696), (3, 647), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 678), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 676), (22, 22), (39, 39), (50, 50), (51, 51)]
      136 0x120abb bytes_l12065f_15 b_l12065f_15 := by
  have f300 : InstrSpec 0x120abb [0x49, 0x01, 0xF1] (fun s => s.RIP = 0x120abb) (addR64R64Effect 0x120abb 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120abb 9 6).toInstrSpec (add_r64_r64_effect_step 0x120abb 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f301 : InstrSpec 0x120abe [0x4D, 0x11, 0xE7] (fun s => s.RIP = 0x120abe) (atFlags StatusFlags.CF (adcR64R64Effect 0x120abe 15 12))
      [.gpr 15, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120abe 15 12).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120abe 0x4d 0xe7 c (by decide) (by decide))) pre_rip
  have f302 : InstrSpec 0x120ac1 [0x49, 0x01, 0xE9] (fun s => s.RIP = 0x120ac1) (addR64R64Effect 0x120ac1 9 5)
      [.gpr 9, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120ac1 9 5).toInstrSpec (add_r64_r64_effect_step 0x120ac1 0x49 0xe9 (by decide) (by decide)) pre_rip
  have f303 : InstrSpec 0x120ac4 [0x4D, 0x11, 0xEF] (fun s => s.RIP = 0x120ac4) (atFlags StatusFlags.CF (adcR64R64Effect 0x120ac4 15 13))
      [.gpr 15, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120ac4 15 13).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120ac4 0x4d 0xef c (by decide) (by decide))) pre_rip
  have f304 : InstrSpec 0x120ac7 [0x4C, 0x01, 0xC8] (fun s => s.RIP = 0x120ac7) (addR64R64Effect 0x120ac7 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120ac7 0 9).toInstrSpec (add_r64_r64_effect_step 0x120ac7 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f305 : InstrSpec 0x120aca [0x49, 0x11, 0xD7] (fun s => s.RIP = 0x120aca) (atFlags StatusFlags.CF (adcR64R64Effect 0x120aca 15 2))
      [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120aca 15 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120aca 0x49 0xd7 c (by decide) (by decide))) pre_rip
  have f306 : InstrSpec 0x120acd [0x48, 0x01, 0xD8] (fun s => s.RIP = 0x120acd) (addR64R64Effect 0x120acd 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120acd 0 3).toInstrSpec (add_r64_r64_effect_step 0x120acd 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f307 : InstrSpec 0x120ad0 [0x49, 0x11, 0xCF] (fun s => s.RIP = 0x120ad0) (atFlags StatusFlags.CF (adcR64R64Effect 0x120ad0 15 1))
      [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120ad0 15 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120ad0 0x49 0xcf c (by decide) (by decide))) pre_rip
  have f308 : InstrSpec 0x120ad3 [0x4C, 0x89, 0xFB] (fun s => s.RIP = 0x120ad3) (movR64R64Effect 0x120ad3 3 15)
      [.gpr 15] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x120ad3 3 15).toInstrSpec (mov_r64_r64_effect_step 0x120ad3 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f309 : InstrSpec 0x120ad6 [0x49, 0x0F, 0xA4, 0xC7, 0x0C] (fun s => s.RIP = 0x120ad6) (shldR64R64Effect 0x120ad6 5 15 0 12)
      [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x120ad6 5 15 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x120ad6 0x49 (by decide) 0xc7 (by decide) 0xc) pre_rip
  have f310 : InstrSpec 0x120adb [0x48, 0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x120adb) (shlR64Effect 0x120adb 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x120adb 4 0 4).toInstrSpec (shl_r64_imm8_effect_step 0x120adb 0x48 0xe0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f311 : InstrSpec 0x120adf [0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00] (fun s => s.RIP = 0x120adf) (movR64Imm64Effect 0x120adf 1 0xfffffffffffff0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x120adf 1 0xfffffffffffff0).toInstrSpec (mov_r64_imm64_effect_step 0x120adf 0x48 0xb9 (by decide) (by decide) 0xfffffffffffff0) pre_rip
  have f312 : InstrSpec 0x120ae9 [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x120ae9) (andR64R64Effect 0x120ae9 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120ae9 0 1).toInstrSpec (and_r64_r64_effect_step 0x120ae9 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f313 : InstrSpec 0x120aec [0x4C, 0x09, 0xD8] (fun s => s.RIP = 0x120aec) (orR64R64Effect 0x120aec 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x120aec 0 11).toInstrSpec (or_r64_r64_effect_step 0x120aec 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f314 : InstrSpec 0x120aef [0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x120aef) (movR64Imm64Effect 0x120aef 1 0x1000003d1)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x120aef 1 0x1000003d1).toInstrSpec (mov_r64_imm64_effect_step 0x120aef 0x48 0xb9 (by decide) (by decide) 0x1000003d1) pre_rip
  have f315 : InstrSpec 0x120af9 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x120af9) (mulR64Effect 0x120af9 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120af9 1).toInstrSpec (mul_r64_effect_step 0x120af9 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f316 : InstrSpec 0x120afc [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x120afc) (movR64R64Effect 0x120afc 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x120afc 6 2).toInstrSpec (mov_r64_r64_effect_step 0x120afc 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f317 : InstrSpec 0x120aff [0x48, 0xC1, 0xEB, 0x34] (fun s => s.RIP = 0x120aff) (shrR64Effect 0x120aff 4 3 52)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x120aff 4 3 52).toInstrSpec (shr_r64_imm8_effect_step 0x120aff 0x48 0xeb 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f318 : InstrSpec 0x120b03 [0x48, 0x03, 0x44, 0x24, 0x18] (LoadPre 0x120b03 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120b03 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x120b03 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (addR64M64Effect_footprint 0x120b03 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (add_r64_m64_effect_step 0x120b03 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f319 : InstrSpec 0x120b08 [0x48, 0x13, 0x74, 0x24, 0x38] (LoadPre 0x120b08 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x120b08 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x120b08 6 (.sib 4 none 0 (.d8 0x38))))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x120b08 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x120b08 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 700) (RestInside.out (n := 700) f300 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 701) f300 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 702) (ρ' := [(0, 695), (1, 645), (2, 696), (3, 647), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 700), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 676), (16, 701), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120abe) f300 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 703) (RestInside.out (n := 703) f301 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 704) (ρ' := [(0, 695), (1, 645), (2, 696), (3, 647), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 700), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 703), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ac1) f301 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 705) (RestInside.out (n := 705) f302 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 706) f302 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 707) (ρ' := [(0, 695), (1, 645), (2, 696), (3, 647), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 703), (16, 706), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ac4) f302 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 708) (RestInside.out (n := 708) f303 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 709) (ρ' := [(0, 695), (1, 645), (2, 696), (3, 647), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 708), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ac7) f303 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 710) (RestInside.out (n := 710) f304 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 711) f304 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 712) (ρ' := [(0, 710), (1, 645), (2, 696), (3, 647), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 708), (16, 711), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120aca) f304 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 713) (RestInside.out (n := 713) f305 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 714) (ρ' := [(0, 710), (1, 645), (2, 696), (3, 647), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 713), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120acd) f305 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 715) (RestInside.out (n := 715) f306 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 716) f306 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 717) (ρ' := [(0, 715), (1, 645), (2, 696), (3, 647), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 713), (16, 716), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ad0) f306 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 718) (RestInside.out (n := 718) f307 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 719) (ρ' := [(0, 715), (1, 645), (2, 696), (3, 647), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 718), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ad3) f307 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 720) (RestInside.out (n := 720) f308 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 721) (ρ' := [(0, 715), (1, 645), (2, 696), (3, 720), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 718), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ad6) f308 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 722) (RestInside.out (n := 722) f309 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 723) (ρ' := [(0, 715), (1, 645), (2, 696), (3, 720), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120adb) f309 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 724) (RestInside.out (n := 724) f310 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 725) (ρ' := [(0, 724), (1, 645), (2, 696), (3, 720), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120adf) f310 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 726) (RestInside.out (n := 726) f311 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 727) (ρ' := [(0, 724), (1, 726), (2, 696), (3, 720), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ae9) f311 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 728) (RestInside.out (n := 728) f312 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 729) (ρ' := [(0, 728), (1, 726), (2, 696), (3, 720), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120aec) f312 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 730) (RestInside.out (n := 730) f313 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 731) (ρ' := [(0, 730), (1, 726), (2, 696), (3, 720), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120aef) f313 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 732) (RestInside.out (n := 732) f314 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 733) (ρ' := [(0, 730), (1, 732), (2, 696), (3, 720), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120af9) f314 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 734) (RestInside.out (n := 734) f315 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 735) f315 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 736) (ρ' := [(0, 734), (1, 732), (2, 735), (3, 720), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120afc) f315 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 737) (RestInside.out (n := 737) f316 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 738) (ρ' := [(0, 734), (1, 732), (2, 735), (3, 720), (4, 4), (5, 689), (6, 737), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120aff) f316 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 739) (RestInside.out (n := 739) f317 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 740) (ρ' := [(0, 734), (1, 732), (2, 735), (3, 739), (4, 4), (5, 689), (6, 737), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b03) f317 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 741) (RestInside.out (n := 741) f318 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 742) f318 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 743) (ρ' := [(0, 741), (1, 732), (2, 735), (3, 739), (4, 4), (5, 689), (6, 737), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (16, 742), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b08) f318 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 744) (RestInside.out (n := 744) f319 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 745) (ρ' := [(0, 741), (1, 732), (2, 735), (3, 739), (4, 4), (5, 689), (6, 744), (7, 680), (8, 693), (9, 705), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 722), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120b0d) f319 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_16 code

theorem rest_l12065f_14 [Bindings] (code : CodeMap) :
    Rest (n := 656) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 651), (1, 645), (2, 652), (3, 647), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]
      156 0x120a6f bytes_l12065f_14 b_l12065f_14 := by
  have f280 : InstrSpec 0x120a6f [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x120a6f) (movR64R64Effect 0x120a6f 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120a6f 0 7).toInstrSpec (mov_r64_r64_effect_step 0x120a6f 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f281 : InstrSpec 0x120a72 [0x48, 0xF7, 0x64, 0x24, 0x48] (LoadPre 0x120a72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x120a72 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120a72 5 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x120a72 5 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mul_m64_effect_step 0x120a72 0x48 (by decide) (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f282 : InstrSpec 0x120a77 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x120a77) (movR64R64Effect 0x120a77 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x120a77 6 0).toInstrSpec (mov_r64_r64_effect_step 0x120a77 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f283 : InstrSpec 0x120a7a [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x120a7a) (movR64R64Effect 0x120a7a 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x120a7a 12 2).toInstrSpec (mov_r64_r64_effect_step 0x120a7a 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f284 : InstrSpec 0x120a7d [0x4D, 0x89, 0xF3] (fun s => s.RIP = 0x120a7d) (movR64R64Effect 0x120a7d 11 14)
      [.gpr 14] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x120a7d 11 14).toInstrSpec (mov_r64_r64_effect_step 0x120a7d 0x4d 0xf3 (by decide) (by decide)) pre_rip
  have f285 : InstrSpec 0x120a80 [0x49, 0xC1, 0xEB, 0x30] (fun s => s.RIP = 0x120a80) (shrR64Effect 0x120a80 4 11 48)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR64Effect_footprint 0x120a80 4 11 48).toInstrSpec (shr_r64_imm8_effect_step 0x120a80 0x49 0xeb 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f286 : InstrSpec 0x120a84 [0x4C, 0x8B, 0x54, 0x24, 0x78] (LoadPre 0x120a84 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x120a84 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120a84 10 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x120a84 10 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x120a84 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f287 : InstrSpec 0x120a89 [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x120a89) (movR64R64Effect 0x120a89 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120a89 0 10).toInstrSpec (mov_r64_r64_effect_step 0x120a89 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f288 : InstrSpec 0x120a8c [0x48, 0xF7, 0x64, 0x24, 0x30] (LoadPre 0x120a8c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x120a8c + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120a8c 5 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x120a8c 5 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mul_m64_effect_step 0x120a8c 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f289 : InstrSpec 0x120a91 [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x120a91) (movR64R64Effect 0x120a91 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x120a91 15 2).toInstrSpec (mov_r64_r64_effect_step 0x120a91 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f290 : InstrSpec 0x120a94 [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x120a94) (movR64R64Effect 0x120a94 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x120a94 9 0).toInstrSpec (mov_r64_r64_effect_step 0x120a94 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f291 : InstrSpec 0x120a97 [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x120a97 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x120a97 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120a97 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x120a97 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x120a97 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f292 : InstrSpec 0x120a9c [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x120a9c) (movR64R64Effect 0x120a9c 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120a9c 0 7).toInstrSpec (mov_r64_r64_effect_step 0x120a9c 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f293 : InstrSpec 0x120a9f [0x48, 0xF7, 0x64, 0x24, 0x40] (LoadPre 0x120a9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x120a9f + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x120a9f 5 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x120a9f 5 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mul_m64_effect_step 0x120a9f 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f294 : InstrSpec 0x120aa4 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x120aa4) (movR64R64Effect 0x120aa4 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x120aa4 13 2).toInstrSpec (mov_r64_r64_effect_step 0x120aa4 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f295 : InstrSpec 0x120aa7 [0x48, 0x89, 0xC5] (fun s => s.RIP = 0x120aa7) (movR64R64Effect 0x120aa7 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x120aa7 5 0).toInstrSpec (mov_r64_r64_effect_step 0x120aa7 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f296 : InstrSpec 0x120aaa [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x120aaa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x120aaa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120aaa 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120aaa 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x120aaa 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f297 : InstrSpec 0x120aaf [0x4C, 0x8B, 0x44, 0x24, 0x58] (LoadPre 0x120aaf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x120aaf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120aaf 8 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x120aaf 8 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x120aaf 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f298 : InstrSpec 0x120ab4 [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x120ab4) (mulR64Effect 0x120ab4 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120ab4 8).toInstrSpec (mul_r64_effect_step 0x120ab4 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f299 : InstrSpec 0x120ab7 [0x41, 0x83, 0xE3, 0x0F] (fun s => s.RIP = 0x120ab7) (andR32Imm8Effect 0x120ab7 4 11 0xf)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x120ab7 4 11 0xf).toInstrSpec (and_r32_imm8_rex_effect_step 0x120ab7 0x41 0xe3 0xf (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 656) (RestInside.out (n := 656) f280 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 657) (ρ' := [(0, 656), (1, 645), (2, 652), (3, 647), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a72) f280 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 658) (RestInside.out (n := 658) f281 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 659) f281 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 660) (ρ' := [(0, 658), (1, 645), (2, 659), (3, 647), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a77) f281 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 661) (RestInside.out (n := 661) f282 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 662) (ρ' := [(0, 658), (1, 645), (2, 659), (3, 647), (4, 4), (5, 582), (6, 661), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a7a) f282 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 663) (RestInside.out (n := 663) f283 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 664) (ρ' := [(0, 658), (1, 645), (2, 659), (3, 647), (4, 4), (5, 582), (6, 661), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 663), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a7d) f283 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 665) (RestInside.out (n := 665) f284 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 666) (ρ' := [(0, 658), (1, 645), (2, 659), (3, 647), (4, 4), (5, 582), (6, 661), (7, 564), (8, 591), (9, 600), (10, 598), (11, 665), (12, 663), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a80) f284 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 667) (RestInside.out (n := 667) f285 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 668) (ρ' := [(0, 658), (1, 645), (2, 659), (3, 647), (4, 4), (5, 582), (6, 661), (7, 564), (8, 591), (9, 600), (10, 598), (11, 667), (12, 663), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a84) f285 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 669) (RestInside.out (n := 669) f286 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 670) (ρ' := [(0, 658), (1, 645), (2, 659), (3, 647), (4, 4), (5, 582), (6, 661), (7, 564), (8, 591), (9, 600), (10, 669), (11, 667), (12, 663), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a89) f286 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 671) (RestInside.out (n := 671) f287 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 672) (ρ' := [(0, 671), (1, 645), (2, 659), (3, 647), (4, 4), (5, 582), (6, 661), (7, 564), (8, 591), (9, 600), (10, 669), (11, 667), (12, 663), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a8c) f287 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 673) (RestInside.out (n := 673) f288 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 674) f288 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 675) (ρ' := [(0, 673), (1, 645), (2, 674), (3, 647), (4, 4), (5, 582), (6, 661), (7, 564), (8, 591), (9, 600), (10, 669), (11, 667), (12, 663), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a91) f288 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 676) (RestInside.out (n := 676) f289 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 677) (ρ' := [(0, 673), (1, 645), (2, 674), (3, 647), (4, 4), (5, 582), (6, 661), (7, 564), (8, 591), (9, 600), (10, 669), (11, 667), (12, 663), (13, 536), (14, 638), (15, 676), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a94) f289 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 678) (RestInside.out (n := 678) f290 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 679) (ρ' := [(0, 673), (1, 645), (2, 674), (3, 647), (4, 4), (5, 582), (6, 661), (7, 564), (8, 591), (9, 678), (10, 669), (11, 667), (12, 663), (13, 536), (14, 638), (15, 676), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a97) f290 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 680) (RestInside.out (n := 680) f291 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 681) (ρ' := [(0, 673), (1, 645), (2, 674), (3, 647), (4, 4), (5, 582), (6, 661), (7, 680), (8, 591), (9, 678), (10, 669), (11, 667), (12, 663), (13, 536), (14, 638), (15, 676), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a9c) f291 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 682) (RestInside.out (n := 682) f292 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 683) (ρ' := [(0, 682), (1, 645), (2, 674), (3, 647), (4, 4), (5, 582), (6, 661), (7, 680), (8, 591), (9, 678), (10, 669), (11, 667), (12, 663), (13, 536), (14, 638), (15, 676), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a9f) f292 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 684) (RestInside.out (n := 684) f293 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 685) f293 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 686) (ρ' := [(0, 684), (1, 645), (2, 685), (3, 647), (4, 4), (5, 582), (6, 661), (7, 680), (8, 591), (9, 678), (10, 669), (11, 667), (12, 663), (13, 536), (14, 638), (15, 676), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120aa4) f293 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 687) (RestInside.out (n := 687) f294 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 688) (ρ' := [(0, 684), (1, 645), (2, 685), (3, 647), (4, 4), (5, 582), (6, 661), (7, 680), (8, 591), (9, 678), (10, 669), (11, 667), (12, 663), (13, 687), (14, 638), (15, 676), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120aa7) f294 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 689) (RestInside.out (n := 689) f295 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 690) (ρ' := [(0, 684), (1, 645), (2, 685), (3, 647), (4, 4), (5, 689), (6, 661), (7, 680), (8, 591), (9, 678), (10, 669), (11, 667), (12, 663), (13, 687), (14, 638), (15, 676), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120aaa) f295 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 691) (RestInside.out (n := 691) f296 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 692) (ρ' := [(0, 691), (1, 645), (2, 685), (3, 647), (4, 4), (5, 689), (6, 661), (7, 680), (8, 591), (9, 678), (10, 669), (11, 667), (12, 663), (13, 687), (14, 638), (15, 676), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120aaf) f296 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 693) (RestInside.out (n := 693) f297 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 694) (ρ' := [(0, 691), (1, 645), (2, 685), (3, 647), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 678), (10, 669), (11, 667), (12, 663), (13, 687), (14, 638), (15, 676), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ab4) f297 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 695) (RestInside.out (n := 695) f298 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 696) f298 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 697) (ρ' := [(0, 695), (1, 645), (2, 696), (3, 647), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 678), (10, 669), (11, 667), (12, 663), (13, 687), (14, 638), (15, 676), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ab7) f298 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 698) (RestInside.out (n := 698) f299 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 699) (ρ' := [(0, 695), (1, 645), (2, 696), (3, 647), (4, 4), (5, 689), (6, 661), (7, 680), (8, 693), (9, 678), (10, 669), (11, 698), (12, 663), (13, 687), (14, 638), (15, 676), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120abb) f299 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_15 code

theorem rest_l12065f_13 [Bindings] (code : CodeMap) :
    Rest (n := 611) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 608), (1, 553), (2, 609), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 573), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]
      176 0x120a25 bytes_l12065f_13 b_l12065f_13 := by
  have f260 : InstrSpec 0x120a25 [0x48, 0xC1, 0xE9, 0x34] (fun s => s.RIP = 0x120a25) (shrR64Effect 0x120a25 4 1 52)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x120a25 4 1 52).toInstrSpec (shr_r64_imm8_effect_step 0x120a25 0x48 0xe9 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f261 : InstrSpec 0x120a29 [0x4C, 0x03, 0x74, 0x24, 0x18] (LoadPre 0x120a29 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120a29 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x120a29 14 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 14, .gpr 4] [] [.reg 14, .flags, .rip] :=
    (addR64M64Effect_footprint 0x120a29 14 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (add_r64_m64_effect_step 0x120a29 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f262 : InstrSpec 0x120a2e [0x48, 0x13, 0x5C, 0x24, 0x38] (LoadPre 0x120a2e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x120a2e + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x120a2e 3 (.sib 4 none 0 (.d8 0x38))))
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x120a2e 3 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x120a2e 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f263 : InstrSpec 0x120a33 [0x49, 0x01, 0xEE] (fun s => s.RIP = 0x120a33) (addR64R64Effect 0x120a33 14 5)
      [.gpr 14, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120a33 14 5).toInstrSpec (add_r64_r64_effect_step 0x120a33 0x49 0xee (by decide) (by decide)) pre_rip
  have f264 : InstrSpec 0x120a36 [0x4C, 0x11, 0xDB] (fun s => s.RIP = 0x120a36) (atFlags StatusFlags.CF (adcR64R64Effect 0x120a36 3 11))
      [.gpr 3, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120a36 3 11).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120a36 0x4c 0xdb c (by decide) (by decide))) pre_rip
  have f265 : InstrSpec 0x120a39 [0x4D, 0x01, 0xC6] (fun s => s.RIP = 0x120a39) (addR64R64Effect 0x120a39 14 8)
      [.gpr 14, .gpr 8] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120a39 14 8).toInstrSpec (add_r64_r64_effect_step 0x120a39 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f266 : InstrSpec 0x120a3c [0x4C, 0x11, 0xFB] (fun s => s.RIP = 0x120a3c) (atFlags StatusFlags.CF (adcR64R64Effect 0x120a3c 3 15))
      [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120a3c 3 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120a3c 0x4c 0xfb c (by decide) (by decide))) pre_rip
  have f267 : InstrSpec 0x120a3f [0x4D, 0x01, 0xE6] (fun s => s.RIP = 0x120a3f) (addR64R64Effect 0x120a3f 14 12)
      [.gpr 14, .gpr 12] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120a3f 14 12).toInstrSpec (add_r64_r64_effect_step 0x120a3f 0x4d 0xe6 (by decide) (by decide)) pre_rip
  have f268 : InstrSpec 0x120a42 [0x4C, 0x11, 0xCB] (fun s => s.RIP = 0x120a42) (atFlags StatusFlags.CF (adcR64R64Effect 0x120a42 3 9))
      [.gpr 3, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120a42 3 9).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120a42 0x4c 0xcb c (by decide) (by decide))) pre_rip
  have f269 : InstrSpec 0x120a45 [0x49, 0x01, 0xC6] (fun s => s.RIP = 0x120a45) (addR64R64Effect 0x120a45 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120a45 14 0).toInstrSpec (add_r64_r64_effect_step 0x120a45 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f270 : InstrSpec 0x120a48 [0x48, 0x11, 0xD3] (fun s => s.RIP = 0x120a48) (atFlags StatusFlags.CF (adcR64R64Effect 0x120a48 3 2))
      [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120a48 3 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120a48 0x48 0xd3 c (by decide) (by decide))) pre_rip
  have f271 : InstrSpec 0x120a4b [0x49, 0x01, 0xF6] (fun s => s.RIP = 0x120a4b) (addR64R64Effect 0x120a4b 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120a4b 14 6).toInstrSpec (add_r64_r64_effect_step 0x120a4b 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f272 : InstrSpec 0x120a4e [0x48, 0x11, 0xCB] (fun s => s.RIP = 0x120a4e) (atFlags StatusFlags.CF (adcR64R64Effect 0x120a4e 3 1))
      [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120a4e 3 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120a4e 0x48 0xcb c (by decide) (by decide))) pre_rip
  have f273 : InstrSpec 0x120a51 [0x48, 0x89, 0xD9] (fun s => s.RIP = 0x120a51) (movR64R64Effect 0x120a51 1 3)
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x120a51 1 3).toInstrSpec (mov_r64_r64_effect_step 0x120a51 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f274 : InstrSpec 0x120a54 [0x48, 0xC1, 0xE9, 0x34] (fun s => s.RIP = 0x120a54) (shrR64Effect 0x120a54 4 1 52)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x120a54 4 1 52).toInstrSpec (shr_r64_imm8_effect_step 0x120a54 0x48 0xe9 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f275 : InstrSpec 0x120a58 [0x4C, 0x0F, 0xA4, 0xF3, 0x0C] (fun s => s.RIP = 0x120a58) (shldR64R64Effect 0x120a58 5 3 14 12)
      [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x120a58 5 3 14 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x120a58 0x4c (by decide) 0xf3 (by decide) 0xc) pre_rip
  have f276 : InstrSpec 0x120a5d [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x120a5d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120a5d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120a5d 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120a5d 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x120a5d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f277 : InstrSpec 0x120a62 [0x49, 0xF7, 0xE2] (fun s => s.RIP = 0x120a62) (mulR64Effect 0x120a62 10)
      [.gpr 10, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120a62 10).toInstrSpec (mul_r64_effect_step 0x120a62 0x49 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f278 : InstrSpec 0x120a65 [0x48, 0x89, 0x54, 0x24, 0x38] (StorePre 0x120a65 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x120a65 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120a65 2 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120a65 2 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x120a65 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f279 : InstrSpec 0x120a6a [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x120a6a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120a6a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120a6a 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120a6a 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x120a6a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 611) (RestInside.out (n := 611) f260 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 612) (ρ' := [(0, 608), (1, 611), (2, 609), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 573), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a29) f260 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 613) (RestInside.out (n := 613) f261 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 614) f261 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 615) (ρ' := [(0, 608), (1, 611), (2, 609), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 613), (15, 589), (16, 614), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a2e) f261 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 616) (RestInside.out (n := 616) f262 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 617) (ρ' := [(0, 608), (1, 611), (2, 609), (3, 616), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 613), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a33) f262 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 618) (RestInside.out (n := 618) f263 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 619) f263 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 620) (ρ' := [(0, 608), (1, 611), (2, 609), (3, 616), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 618), (15, 589), (16, 619), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a36) f263 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 621) (RestInside.out (n := 621) f264 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 622) (ρ' := [(0, 608), (1, 611), (2, 609), (3, 621), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 618), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a39) f264 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 623) (RestInside.out (n := 623) f265 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 624) f265 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 625) (ρ' := [(0, 608), (1, 611), (2, 609), (3, 621), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 623), (15, 589), (16, 624), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a3c) f265 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 626) (RestInside.out (n := 626) f266 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 627) (ρ' := [(0, 608), (1, 611), (2, 609), (3, 626), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 623), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a3f) f266 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 628) (RestInside.out (n := 628) f267 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 629) f267 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 630) (ρ' := [(0, 608), (1, 611), (2, 609), (3, 626), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 628), (15, 589), (16, 629), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a42) f267 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 631) (RestInside.out (n := 631) f268 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 632) (ρ' := [(0, 608), (1, 611), (2, 609), (3, 631), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 628), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a45) f268 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 633) (RestInside.out (n := 633) f269 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 634) f269 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 635) (ρ' := [(0, 608), (1, 611), (2, 609), (3, 631), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 633), (15, 589), (16, 634), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a48) f269 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 636) (RestInside.out (n := 636) f270 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 637) (ρ' := [(0, 608), (1, 611), (2, 609), (3, 636), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 633), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a4b) f270 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 638) (RestInside.out (n := 638) f271 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 639) f271 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 640) (ρ' := [(0, 608), (1, 611), (2, 609), (3, 636), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 638), (15, 589), (16, 639), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a4e) f271 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 641) (RestInside.out (n := 641) f272 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 642) (ρ' := [(0, 608), (1, 611), (2, 609), (3, 641), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a51) f272 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 643) (RestInside.out (n := 643) f273 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 644) (ρ' := [(0, 608), (1, 643), (2, 609), (3, 641), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a54) f273 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 645) (RestInside.out (n := 645) f274 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 646) (ρ' := [(0, 608), (1, 645), (2, 609), (3, 641), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a58) f274 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 647) (RestInside.out (n := 647) f275 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 648) (ρ' := [(0, 608), (1, 645), (2, 609), (3, 647), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a5d) f275 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 649) (RestInside.out (n := 649) f276 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 650) (ρ' := [(0, 649), (1, 645), (2, 609), (3, 647), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a62) f276 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 651) (RestInside.out (n := 651) f277 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 652) f277 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 653) (ρ' := [(0, 651), (1, 645), (2, 652), (3, 647), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a65) f277 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 654) (RestInside.exec (n := 654) (ρ' := [(0, 651), (1, 645), (2, 652), (3, 647), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a6a) f278 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 655) (RestInside.exec (n := 655) (ρ' := [(0, 651), (1, 645), (2, 652), (3, 647), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 638), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a6f) f279 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l12065f_14 code

theorem rest_l12065f_12 [Bindings] (code : CodeMap) :
    Rest (n := 566) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 559), (1, 553), (2, 560), (3, 519), (4, 4), (5, 465), (6, 555), (7, 564), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]
      196 0x1209e0 bytes_l12065f_12 b_l12065f_12 := by
  have f240 : InstrSpec 0x1209e0 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x1209e0) (movR64R64Effect 0x1209e0 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1209e0 0 7).toInstrSpec (mov_r64_r64_effect_step 0x1209e0 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f241 : InstrSpec 0x1209e3 [0x48, 0xF7, 0xE5] (fun s => s.RIP = 0x1209e3) (mulR64Effect 0x1209e3 5)
      [.gpr 5, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1209e3 5).toInstrSpec (mul_r64_effect_step 0x1209e3 0x48 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f242 : InstrSpec 0x1209e6 [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x1209e6) (movR64R64Effect 0x1209e6 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1209e6 3 2).toInstrSpec (mov_r64_r64_effect_step 0x1209e6 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f243 : InstrSpec 0x1209e9 [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x1209e9) (movR64R64Effect 0x1209e9 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1209e9 14 0).toInstrSpec (mov_r64_r64_effect_step 0x1209e9 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f244 : InstrSpec 0x1209ec [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x1209ec) (movR64R64Effect 0x1209ec 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1209ec 0 8).toInstrSpec (mov_r64_r64_effect_step 0x1209ec 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f245 : InstrSpec 0x1209ef [0x48, 0xF7, 0x64, 0x24, 0x40] (LoadPre 0x1209ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1209ef + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1209ef 5 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulM64Effect_footprint 0x1209ef 5 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mul_m64_effect_step 0x1209ef 0x48 (by decide) (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f246 : InstrSpec 0x1209f4 [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x1209f4) (movR64R64Effect 0x1209f4 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1209f4 11 2).toInstrSpec (mov_r64_r64_effect_step 0x1209f4 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f247 : InstrSpec 0x1209f7 [0x48, 0x89, 0xC5] (fun s => s.RIP = 0x1209f7) (movR64R64Effect 0x1209f7 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1209f7 5 0).toInstrSpec (mov_r64_r64_effect_step 0x1209f7 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f248 : InstrSpec 0x1209fa [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x1209fa) (movR64R64Effect 0x1209fa 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1209fa 0 10).toInstrSpec (mov_r64_r64_effect_step 0x1209fa 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f249 : InstrSpec 0x1209fd [0x49, 0xF7, 0xE7] (fun s => s.RIP = 0x1209fd) (mulR64Effect 0x1209fd 15)
      [.gpr 15, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1209fd 15).toInstrSpec (mul_r64_effect_step 0x1209fd 0x49 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f250 : InstrSpec 0x120a00 [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x120a00) (movR64R64Effect 0x120a00 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x120a00 15 2).toInstrSpec (mov_r64_r64_effect_step 0x120a00 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f251 : InstrSpec 0x120a03 [0x49, 0x89, 0xC0] (fun s => s.RIP = 0x120a03) (movR64R64Effect 0x120a03 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x120a03 8 0).toInstrSpec (mov_r64_r64_effect_step 0x120a03 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f252 : InstrSpec 0x120a06 [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x120a06) (movR64R64Effect 0x120a06 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120a06 0 9).toInstrSpec (mov_r64_r64_effect_step 0x120a06 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f253 : InstrSpec 0x120a09 [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x120a09) (mulR64Effect 0x120a09 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120a09 12).toInstrSpec (mul_r64_effect_step 0x120a09 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f254 : InstrSpec 0x120a0c [0x4D, 0x89, 0xE2] (fun s => s.RIP = 0x120a0c) (movR64R64Effect 0x120a0c 10 12)
      [.gpr 12] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x120a0c 10 12).toInstrSpec (mov_r64_r64_effect_step 0x120a0c 0x4d 0xe2 (by decide) (by decide)) pre_rip
  have f255 : InstrSpec 0x120a0f [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x120a0f) (movR64R64Effect 0x120a0f 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x120a0f 9 2).toInstrSpec (mov_r64_r64_effect_step 0x120a0f 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f256 : InstrSpec 0x120a12 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x120a12) (movR64R64Effect 0x120a12 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x120a12 12 0).toInstrSpec (mov_r64_r64_effect_step 0x120a12 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f257 : InstrSpec 0x120a15 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x120a15) (movR64R64Effect 0x120a15 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120a15 0 13).toInstrSpec (mov_r64_r64_effect_step 0x120a15 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f258 : InstrSpec 0x120a18 [0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x120a18) (movR64Imm64Effect 0x120a18 2 0x1000003d10)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x120a18 2 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x120a18 0x48 0xba (by decide) (by decide) 0x1000003d10) pre_rip
  have f259 : InstrSpec 0x120a22 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x120a22) (mulR64Effect 0x120a22 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120a22 2).toInstrSpec (mul_r64_effect_step 0x120a22 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 566) (RestInside.out (n := 566) f240 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 567) (ρ' := [(0, 566), (1, 553), (2, 560), (3, 519), (4, 4), (5, 465), (6, 555), (7, 564), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209e3) f240 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 568) (RestInside.out (n := 568) f241 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 569) f241 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 570) (ρ' := [(0, 568), (1, 553), (2, 569), (3, 519), (4, 4), (5, 465), (6, 555), (7, 564), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209e6) f241 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 571) (RestInside.out (n := 571) f242 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 572) (ρ' := [(0, 568), (1, 553), (2, 569), (3, 571), (4, 4), (5, 465), (6, 555), (7, 564), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209e9) f242 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 573) (RestInside.out (n := 573) f243 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 574) (ρ' := [(0, 568), (1, 553), (2, 569), (3, 571), (4, 4), (5, 465), (6, 555), (7, 564), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 573), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209ec) f243 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 575) (RestInside.out (n := 575) f244 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 576) (ρ' := [(0, 575), (1, 553), (2, 569), (3, 571), (4, 4), (5, 465), (6, 555), (7, 564), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 573), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209ef) f244 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 577) (RestInside.out (n := 577) f245 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 578) f245 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 579) (ρ' := [(0, 577), (1, 553), (2, 578), (3, 571), (4, 4), (5, 465), (6, 555), (7, 564), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 573), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209f4) f245 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 580) (RestInside.out (n := 580) f246 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 581) (ρ' := [(0, 577), (1, 553), (2, 578), (3, 571), (4, 4), (5, 465), (6, 555), (7, 564), (8, 490), (9, 524), (10, 460), (11, 580), (12, 510), (13, 536), (14, 573), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209f7) f246 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 582) (RestInside.out (n := 582) f247 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 583) (ρ' := [(0, 577), (1, 553), (2, 578), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 490), (9, 524), (10, 460), (11, 580), (12, 510), (13, 536), (14, 573), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209fa) f247 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 584) (RestInside.out (n := 584) f248 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 585) (ρ' := [(0, 584), (1, 553), (2, 578), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 490), (9, 524), (10, 460), (11, 580), (12, 510), (13, 536), (14, 573), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209fd) f248 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 586) (RestInside.out (n := 586) f249 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 587) f249 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 588) (ρ' := [(0, 586), (1, 553), (2, 587), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 490), (9, 524), (10, 460), (11, 580), (12, 510), (13, 536), (14, 573), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a00) f249 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 589) (RestInside.out (n := 589) f250 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 590) (ρ' := [(0, 586), (1, 553), (2, 587), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 490), (9, 524), (10, 460), (11, 580), (12, 510), (13, 536), (14, 573), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a03) f250 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 591) (RestInside.out (n := 591) f251 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 592) (ρ' := [(0, 586), (1, 553), (2, 587), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 524), (10, 460), (11, 580), (12, 510), (13, 536), (14, 573), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a06) f251 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 593) (RestInside.out (n := 593) f252 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 594) (ρ' := [(0, 593), (1, 553), (2, 587), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 524), (10, 460), (11, 580), (12, 510), (13, 536), (14, 573), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a09) f252 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 595) (RestInside.out (n := 595) f253 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 596) f253 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 597) (ρ' := [(0, 595), (1, 553), (2, 596), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 524), (10, 460), (11, 580), (12, 510), (13, 536), (14, 573), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a0c) f253 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 598) (RestInside.out (n := 598) f254 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 599) (ρ' := [(0, 595), (1, 553), (2, 596), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 524), (10, 598), (11, 580), (12, 510), (13, 536), (14, 573), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a0f) f254 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 600) (RestInside.out (n := 600) f255 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 601) (ρ' := [(0, 595), (1, 553), (2, 596), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 510), (13, 536), (14, 573), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a12) f255 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 602) (RestInside.out (n := 602) f256 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 603) (ρ' := [(0, 595), (1, 553), (2, 596), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 573), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a15) f256 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 604) (RestInside.out (n := 604) f257 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 605) (ρ' := [(0, 604), (1, 553), (2, 596), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 573), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a18) f257 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 606) (RestInside.out (n := 606) f258 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 607) (ρ' := [(0, 604), (1, 553), (2, 606), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 573), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a22) f258 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 608) (RestInside.out (n := 608) f259 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 609) f259 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 610) (ρ' := [(0, 608), (1, 553), (2, 609), (3, 571), (4, 4), (5, 582), (6, 555), (7, 564), (8, 591), (9, 600), (10, 598), (11, 580), (12, 602), (13, 536), (14, 573), (15, 589), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120a25) f259 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_13 code

theorem rest_l12065f_11 [Bindings] (code : CodeMap) :
    Rest (n := 526) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 512), (1, 447), (2, 513), (3, 519), (4, 4), (5, 465), (6, 505), (7, 458), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]
      216 0x12098d bytes_l12065f_11 b_l12065f_11 := by
  have f220 : InstrSpec 0x12098d [0x4C, 0x89, 0x6C, 0x24, 0x20] (StorePre 0x12098d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x12098d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12098d 13 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12098d 13 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x12098d 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f221 : InstrSpec 0x120992 [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x120992) (movR64R64Effect 0x120992 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120992 0 13).toInstrSpec (mov_r64_r64_effect_step 0x120992 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f222 : InstrSpec 0x120995 [0x48, 0x8B, 0x7C, 0x24, 0x48] (LoadPre 0x120995 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x120995 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120995 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x120995 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x120995 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f223 : InstrSpec 0x12099a [0x48, 0xF7, 0xE7] (fun s => s.RIP = 0x12099a) (mulR64Effect 0x12099a 7)
      [.gpr 7, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x12099a 7).toInstrSpec (mul_r64_effect_step 0x12099a 0x48 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f224 : InstrSpec 0x12099d [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x12099d) (movR64R64Effect 0x12099d 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x12099d 13 2).toInstrSpec (mov_r64_r64_effect_step 0x12099d 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f225 : InstrSpec 0x1209a0 [0x49, 0x0F, 0xA4, 0xC5, 0x0C] (fun s => s.RIP = 0x1209a0) (shldR64R64Effect 0x1209a0 5 13 0 12)
      [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1209a0 5 13 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1209a0 0x49 (by decide) 0xc5 (by decide) 0xc) pre_rip
  have f226 : InstrSpec 0x1209a5 [0x48, 0x21, 0xC8] (fun s => s.RIP = 0x1209a5) (andR64R64Effect 0x1209a5 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1209a5 0 1).toInstrSpec (and_r64_r64_effect_step 0x1209a5 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f227 : InstrSpec 0x1209a8 [0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1209a8) (movR64Imm64Effect 0x1209a8 1 0x1000003d10)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x1209a8 1 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x1209a8 0x48 0xb9 (by decide) (by decide) 0x1000003d10) pre_rip
  have f228 : InstrSpec 0x1209b2 [0x48, 0xF7, 0xE1] (fun s => s.RIP = 0x1209b2) (mulR64Effect 0x1209b2 1)
      [.gpr 1, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1209b2 1).toInstrSpec (mul_r64_effect_step 0x1209b2 0x48 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f229 : InstrSpec 0x1209b5 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x1209b5) (movR64R64Effect 0x1209b5 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1209b5 6 2).toInstrSpec (mov_r64_r64_effect_step 0x1209b5 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f230 : InstrSpec 0x1209b8 [0x48, 0x01, 0xD8] (fun s => s.RIP = 0x1209b8) (addR64R64Effect 0x1209b8 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1209b8 0 3).toInstrSpec (add_r64_r64_effect_step 0x1209b8 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f231 : InstrSpec 0x1209bb [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x1209bb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1209bb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1209bb 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1209bb 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x1209bb 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f232 : InstrSpec 0x1209c0 [0x4C, 0x11, 0xDE] (fun s => s.RIP = 0x1209c0) (atFlags StatusFlags.CF (adcR64R64Effect 0x1209c0 6 11))
      [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1209c0 6 11).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1209c0 0x4c 0xde c (by decide) (by decide))) pre_rip
  have f233 : InstrSpec 0x1209c3 [0x48, 0x89, 0xF1] (fun s => s.RIP = 0x1209c3) (movR64R64Effect 0x1209c3 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1209c3 1 6).toInstrSpec (mov_r64_r64_effect_step 0x1209c3 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f234 : InstrSpec 0x1209c6 [0x48, 0x0F, 0xA4, 0xC6, 0x0C] (fun s => s.RIP = 0x1209c6) (shldR64R64Effect 0x1209c6 5 6 0 12)
      [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1209c6 5 6 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1209c6 0x48 (by decide) 0xc6 (by decide) 0xc) pre_rip
  have f235 : InstrSpec 0x1209cb [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x1209cb) (movR64R64Effect 0x1209cb 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1209cb 0 14).toInstrSpec (mov_r64_r64_effect_step 0x1209cb 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f236 : InstrSpec 0x1209ce [0x48, 0xF7, 0xE7] (fun s => s.RIP = 0x1209ce) (mulR64Effect 0x1209ce 7)
      [.gpr 7, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1209ce 7).toInstrSpec (mul_r64_effect_step 0x1209ce 0x48 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f237 : InstrSpec 0x1209d1 [0x48, 0x89, 0x54, 0x24, 0x38] (StorePre 0x1209d1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1209d1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1209d1 2 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1209d1 2 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x1209d1 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f238 : InstrSpec 0x1209d6 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x1209d6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1209d6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1209d6 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1209d6 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1209d6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f239 : InstrSpec 0x1209db [0x48, 0x8B, 0x7C, 0x24, 0x08] (LoadPre 0x1209db (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1209db + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1209db 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1209db 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1209db 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 526) (RestInside.exec (n := 526) (ρ' := [(0, 512), (1, 447), (2, 513), (3, 519), (4, 4), (5, 465), (6, 505), (7, 458), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120992) f220 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 527) (RestInside.out (n := 527) f221 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 528) (ρ' := [(0, 527), (1, 447), (2, 513), (3, 519), (4, 4), (5, 465), (6, 505), (7, 458), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120995) f221 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 529) (RestInside.out (n := 529) f222 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 530) (ρ' := [(0, 527), (1, 447), (2, 513), (3, 519), (4, 4), (5, 465), (6, 505), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12099a) f222 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 531) (RestInside.out (n := 531) f223 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 532) f223 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 533) (ρ' := [(0, 531), (1, 447), (2, 532), (3, 519), (4, 4), (5, 465), (6, 505), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12099d) f223 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 534) (RestInside.out (n := 534) f224 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 535) (ρ' := [(0, 531), (1, 447), (2, 532), (3, 519), (4, 4), (5, 465), (6, 505), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 534), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209a0) f224 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 536) (RestInside.out (n := 536) f225 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 537) (ρ' := [(0, 531), (1, 447), (2, 532), (3, 519), (4, 4), (5, 465), (6, 505), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209a5) f225 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 538) (RestInside.out (n := 538) f226 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 539) (ρ' := [(0, 538), (1, 447), (2, 532), (3, 519), (4, 4), (5, 465), (6, 505), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209a8) f226 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 540) (RestInside.out (n := 540) f227 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 541) (ρ' := [(0, 538), (1, 540), (2, 532), (3, 519), (4, 4), (5, 465), (6, 505), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209b2) f227 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 542) (RestInside.out (n := 542) f228 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 543) f228 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 544) (ρ' := [(0, 542), (1, 540), (2, 543), (3, 519), (4, 4), (5, 465), (6, 505), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209b5) f228 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 545) (RestInside.out (n := 545) f229 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 546) (ρ' := [(0, 542), (1, 540), (2, 543), (3, 519), (4, 4), (5, 465), (6, 545), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209b8) f229 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 547) (RestInside.out (n := 547) f230 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 548) f230 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 549) (ρ' := [(0, 547), (1, 540), (2, 543), (3, 519), (4, 4), (5, 465), (6, 545), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (16, 548), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209bb) f230 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 550) (RestInside.exec (n := 550) (ρ' := [(0, 547), (1, 540), (2, 543), (3, 519), (4, 4), (5, 465), (6, 545), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (16, 548), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209c0) f231 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 551) (RestInside.out (n := 551) f232 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 552) (ρ' := [(0, 547), (1, 540), (2, 543), (3, 519), (4, 4), (5, 465), (6, 551), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209c3) f232 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 553) (RestInside.out (n := 553) f233 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 554) (ρ' := [(0, 547), (1, 553), (2, 543), (3, 519), (4, 4), (5, 465), (6, 551), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209c6) f233 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 555) (RestInside.out (n := 555) f234 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 556) (ρ' := [(0, 547), (1, 553), (2, 543), (3, 519), (4, 4), (5, 465), (6, 555), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209cb) f234 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 557) (RestInside.out (n := 557) f235 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 558) (ρ' := [(0, 557), (1, 553), (2, 543), (3, 519), (4, 4), (5, 465), (6, 555), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209ce) f235 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 559) (RestInside.out (n := 559) f236 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 560) f236 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 561) (ρ' := [(0, 559), (1, 553), (2, 560), (3, 519), (4, 4), (5, 465), (6, 555), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209d1) f236 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 562) (RestInside.exec (n := 562) (ρ' := [(0, 559), (1, 553), (2, 560), (3, 519), (4, 4), (5, 465), (6, 555), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209d6) f237 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 563) (RestInside.exec (n := 563) (ρ' := [(0, 559), (1, 553), (2, 560), (3, 519), (4, 4), (5, 465), (6, 555), (7, 529), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209db) f238 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 564) (RestInside.out (n := 564) f239 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 565) (ρ' := [(0, 559), (1, 553), (2, 560), (3, 519), (4, 4), (5, 465), (6, 555), (7, 564), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 536), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1209e0) f239 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_12 code

theorem rest_l12065f_10 [Bindings] (code : CodeMap) :
    Rest (n := 483) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 476), (1, 447), (2, 477), (3, 481), (4, 4), (5, 465), (6, 470), (7, 458), (8, 453), (9, 472), (10, 460), (11, 479), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]
      236 0x120949 bytes_l12065f_10 b_l12065f_10 := by
  have f200 : InstrSpec 0x120949 [0x4C, 0x01, 0xCB] (fun s => s.RIP = 0x120949) (addR64R64Effect 0x120949 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120949 3 9).toInstrSpec (add_r64_r64_effect_step 0x120949 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f201 : InstrSpec 0x12094c [0x49, 0x11, 0xF3] (fun s => s.RIP = 0x12094c) (atFlags StatusFlags.CF (adcR64R64Effect 0x12094c 11 6))
      [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x12094c 11 6).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x12094c 0x49 0xf3 c (by decide) (by decide))) pre_rip
  have f202 : InstrSpec 0x12094f [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x12094f) (movR64R64Effect 0x12094f 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12094f 0 7).toInstrSpec (mov_r64_r64_effect_step 0x12094f 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f203 : InstrSpec 0x120952 [0x49, 0x89, 0xF8] (fun s => s.RIP = 0x120952) (movR64R64Effect 0x120952 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x120952 8 7).toInstrSpec (mov_r64_r64_effect_step 0x120952 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f204 : InstrSpec 0x120955 [0x48, 0x89, 0x7C, 0x24, 0x78] (StorePre 0x120955 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x120955 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120955 7 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120955 7 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x120955 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f205 : InstrSpec 0x12095a [0x4C, 0x8B, 0x7C, 0x24, 0x58] (LoadPre 0x12095a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12095a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12095a 15 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x12095a 15 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x12095a 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f206 : InstrSpec 0x12095f [0x49, 0xF7, 0xE7] (fun s => s.RIP = 0x12095f) (mulR64Effect 0x12095f 15)
      [.gpr 15, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x12095f 15).toInstrSpec (mul_r64_effect_step 0x12095f 0x49 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f207 : InstrSpec 0x120962 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x120962) (movR64R64Effect 0x120962 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x120962 6 2).toInstrSpec (mov_r64_r64_effect_step 0x120962 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f208 : InstrSpec 0x120965 [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x120965) (movR64R64Effect 0x120965 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x120965 9 0).toInstrSpec (mov_r64_r64_effect_step 0x120965 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f209 : InstrSpec 0x120968 [0x49, 0x01, 0xD9] (fun s => s.RIP = 0x120968) (addR64R64Effect 0x120968 9 3)
      [.gpr 9, .gpr 3] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120968 9 3).toInstrSpec (add_r64_r64_effect_step 0x120968 0x49 0xd9 (by decide) (by decide)) pre_rip
  have f210 : InstrSpec 0x12096b [0x4C, 0x11, 0xDE] (fun s => s.RIP = 0x12096b) (atFlags StatusFlags.CF (adcR64R64Effect 0x12096b 6 11))
      [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x12096b 6 11).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x12096b 0x4c 0xde c (by decide) (by decide))) pre_rip
  have f211 : InstrSpec 0x12096e [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x12096e) (movR64R64Effect 0x12096e 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12096e 0 10).toInstrSpec (mov_r64_r64_effect_step 0x12096e 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f212 : InstrSpec 0x120971 [0x4C, 0x89, 0x54, 0x24, 0x28] (StorePre 0x120971 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x120971 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120971 10 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120971 10 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x120971 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f213 : InstrSpec 0x120976 [0x4C, 0x8B, 0x64, 0x24, 0x50] (LoadPre 0x120976 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x120976 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120976 12 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x120976 12 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x120976 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f214 : InstrSpec 0x12097b [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x12097b) (mulR64Effect 0x12097b 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x12097b 12).toInstrSpec (mul_r64_effect_step 0x12097b 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f215 : InstrSpec 0x12097e [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x12097e) (movR64R64Effect 0x12097e 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x12097e 11 2).toInstrSpec (mov_r64_r64_effect_step 0x12097e 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f216 : InstrSpec 0x120981 [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x120981) (movR64R64Effect 0x120981 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x120981 3 0).toInstrSpec (mov_r64_r64_effect_step 0x120981 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f217 : InstrSpec 0x120984 [0x4C, 0x01, 0xCB] (fun s => s.RIP = 0x120984) (addR64R64Effect 0x120984 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120984 3 9).toInstrSpec (add_r64_r64_effect_step 0x120984 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f218 : InstrSpec 0x120987 [0x49, 0x11, 0xF3] (fun s => s.RIP = 0x120987) (atFlags StatusFlags.CF (adcR64R64Effect 0x120987 11 6))
      [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120987 11 6).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120987 0x49 0xf3 c (by decide) (by decide))) pre_rip
  have f219 : InstrSpec 0x12098a [0x4D, 0x89, 0xE9] (fun s => s.RIP = 0x12098a) (movR64R64Effect 0x12098a 9 13)
      [.gpr 13] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x12098a 9 13).toInstrSpec (mov_r64_r64_effect_step 0x12098a 0x4d 0xe9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 483) (RestInside.out (n := 483) f200 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 484) f200 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 485) (ρ' := [(0, 476), (1, 447), (2, 477), (3, 483), (4, 4), (5, 465), (6, 470), (7, 458), (8, 453), (9, 472), (10, 460), (11, 479), (12, 355), (13, 445), (14, 451), (15, 364), (16, 484), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12094c) f200 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 486) (RestInside.out (n := 486) f201 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 487) (ρ' := [(0, 476), (1, 447), (2, 477), (3, 483), (4, 4), (5, 465), (6, 470), (7, 458), (8, 453), (9, 472), (10, 460), (11, 486), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12094f) f201 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 488) (RestInside.out (n := 488) f202 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 489) (ρ' := [(0, 488), (1, 447), (2, 477), (3, 483), (4, 4), (5, 465), (6, 470), (7, 458), (8, 453), (9, 472), (10, 460), (11, 486), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120952) f202 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 490) (RestInside.out (n := 490) f203 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 491) (ρ' := [(0, 488), (1, 447), (2, 477), (3, 483), (4, 4), (5, 465), (6, 470), (7, 458), (8, 490), (9, 472), (10, 460), (11, 486), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120955) f203 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 492) (RestInside.exec (n := 492) (ρ' := [(0, 488), (1, 447), (2, 477), (3, 483), (4, 4), (5, 465), (6, 470), (7, 458), (8, 490), (9, 472), (10, 460), (11, 486), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12095a) f204 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 493) (RestInside.out (n := 493) f205 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 494) (ρ' := [(0, 488), (1, 447), (2, 477), (3, 483), (4, 4), (5, 465), (6, 470), (7, 458), (8, 490), (9, 472), (10, 460), (11, 486), (12, 355), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12095f) f205 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 495) (RestInside.out (n := 495) f206 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 496) f206 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 497) (ρ' := [(0, 495), (1, 447), (2, 496), (3, 483), (4, 4), (5, 465), (6, 470), (7, 458), (8, 490), (9, 472), (10, 460), (11, 486), (12, 355), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120962) f206 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 498) (RestInside.out (n := 498) f207 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 499) (ρ' := [(0, 495), (1, 447), (2, 496), (3, 483), (4, 4), (5, 465), (6, 498), (7, 458), (8, 490), (9, 472), (10, 460), (11, 486), (12, 355), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120965) f207 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 500) (RestInside.out (n := 500) f208 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 501) (ρ' := [(0, 495), (1, 447), (2, 496), (3, 483), (4, 4), (5, 465), (6, 498), (7, 458), (8, 490), (9, 500), (10, 460), (11, 486), (12, 355), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120968) f208 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 502) (RestInside.out (n := 502) f209 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 503) f209 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 504) (ρ' := [(0, 495), (1, 447), (2, 496), (3, 483), (4, 4), (5, 465), (6, 498), (7, 458), (8, 490), (9, 502), (10, 460), (11, 486), (12, 355), (13, 445), (14, 451), (15, 493), (16, 503), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12096b) f209 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 505) (RestInside.out (n := 505) f210 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 506) (ρ' := [(0, 495), (1, 447), (2, 496), (3, 483), (4, 4), (5, 465), (6, 505), (7, 458), (8, 490), (9, 502), (10, 460), (11, 486), (12, 355), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12096e) f210 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 507) (RestInside.out (n := 507) f211 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 508) (ρ' := [(0, 507), (1, 447), (2, 496), (3, 483), (4, 4), (5, 465), (6, 505), (7, 458), (8, 490), (9, 502), (10, 460), (11, 486), (12, 355), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120971) f211 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 509) (RestInside.exec (n := 509) (ρ' := [(0, 507), (1, 447), (2, 496), (3, 483), (4, 4), (5, 465), (6, 505), (7, 458), (8, 490), (9, 502), (10, 460), (11, 486), (12, 355), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120976) f212 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 510) (RestInside.out (n := 510) f213 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 511) (ρ' := [(0, 507), (1, 447), (2, 496), (3, 483), (4, 4), (5, 465), (6, 505), (7, 458), (8, 490), (9, 502), (10, 460), (11, 486), (12, 510), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12097b) f213 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 512) (RestInside.out (n := 512) f214 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 513) f214 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 514) (ρ' := [(0, 512), (1, 447), (2, 513), (3, 483), (4, 4), (5, 465), (6, 505), (7, 458), (8, 490), (9, 502), (10, 460), (11, 486), (12, 510), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12097e) f214 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 515) (RestInside.out (n := 515) f215 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 516) (ρ' := [(0, 512), (1, 447), (2, 513), (3, 483), (4, 4), (5, 465), (6, 505), (7, 458), (8, 490), (9, 502), (10, 460), (11, 515), (12, 510), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120981) f215 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 517) (RestInside.out (n := 517) f216 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 518) (ρ' := [(0, 512), (1, 447), (2, 513), (3, 517), (4, 4), (5, 465), (6, 505), (7, 458), (8, 490), (9, 502), (10, 460), (11, 515), (12, 510), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120984) f216 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 519) (RestInside.out (n := 519) f217 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 520) f217 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 521) (ρ' := [(0, 512), (1, 447), (2, 513), (3, 519), (4, 4), (5, 465), (6, 505), (7, 458), (8, 490), (9, 502), (10, 460), (11, 515), (12, 510), (13, 445), (14, 451), (15, 493), (16, 520), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120987) f217 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 522) (RestInside.out (n := 522) f218 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 523) (ρ' := [(0, 512), (1, 447), (2, 513), (3, 519), (4, 4), (5, 465), (6, 505), (7, 458), (8, 490), (9, 502), (10, 460), (11, 522), (12, 510), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12098a) f218 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 524) (RestInside.out (n := 524) f219 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 525) (ρ' := [(0, 512), (1, 447), (2, 513), (3, 519), (4, 4), (5, 465), (6, 505), (7, 458), (8, 490), (9, 524), (10, 460), (11, 522), (12, 510), (13, 445), (14, 451), (15, 493), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12098d) f219 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_11 code

theorem rest_l12065f_9 [Bindings] (code : CodeMap) :
    Rest (n := 443) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 437), (1, 441), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 435), (8, 331), (9, 402), (10, 430), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]
      256 0x1208fe bytes_l12065f_9 b_l12065f_9 := by
  have f180 : InstrSpec 0x1208fe [0x48, 0x01, 0xF9] (fun s => s.RIP = 0x1208fe) (addR64R64Effect 0x1208fe 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1208fe 1 7).toInstrSpec (add_r64_r64_effect_step 0x1208fe 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f181 : InstrSpec 0x120901 [0x49, 0x89, 0xCD] (fun s => s.RIP = 0x120901) (movR64R64Effect 0x120901 13 1)
      [.gpr 1] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x120901 13 1).toInstrSpec (mov_r64_r64_effect_step 0x120901 0x49 0xcd (by decide) (by decide)) pre_rip
  have f182 : InstrSpec 0x120904 [0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x120904) (movR64Imm64Effect 0x120904 1 0xfffffffffffff)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x120904 1 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x120904 0x48 0xb9 (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f183 : InstrSpec 0x12090e [0x4C, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x12090e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12090e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12090e 14 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x12090e 14 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12090e 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f184 : InstrSpec 0x120913 [0x49, 0x21, 0xCE] (fun s => s.RIP = 0x120913) (andR64R64Effect 0x120913 14 1)
      [.gpr 14, .gpr 1] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120913 14 1).toInstrSpec (and_r64_r64_effect_step 0x120913 0x49 0xce (by decide) (by decide)) pre_rip
  have f185 : InstrSpec 0x120916 [0x49, 0x21, 0xC8] (fun s => s.RIP = 0x120916) (andR64R64Effect 0x120916 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120916 8 1).toInstrSpec (and_r64_r64_effect_step 0x120916 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f186 : InstrSpec 0x120919 [0x4C, 0x89, 0x44, 0x24, 0x08] (StorePre 0x120919 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120919 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120919 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120919 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x120919 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f187 : InstrSpec 0x12091e [0x4C, 0x89, 0xCF] (fun s => s.RIP = 0x12091e) (movR64R64Effect 0x12091e 7 9)
      [.gpr 9] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12091e 7 9).toInstrSpec (mov_r64_r64_effect_step 0x12091e 0x4c 0xcf (by decide) (by decide)) pre_rip
  have f188 : InstrSpec 0x120921 [0x48, 0x21, 0xCF] (fun s => s.RIP = 0x120921) (andR64R64Effect 0x120921 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120921 7 1).toInstrSpec (and_r64_r64_effect_step 0x120921 0x48 0xcf (by decide) (by decide)) pre_rip
  have f189 : InstrSpec 0x120924 [0x49, 0x21, 0xCA] (fun s => s.RIP = 0x120924) (andR64R64Effect 0x120924 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120924 10 1).toInstrSpec (and_r64_r64_effect_step 0x120924 0x49 0xca (by decide) (by decide)) pre_rip
  have f190 : InstrSpec 0x120927 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x120927) (movR64R64Effect 0x120927 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120927 0 14).toInstrSpec (mov_r64_r64_effect_step 0x120927 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f191 : InstrSpec 0x12092a [0x4C, 0x89, 0x74, 0x24, 0x10] (StorePre 0x12092a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12092a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12092a 14 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12092a 14 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12092a 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f192 : InstrSpec 0x12092f [0x48, 0x8B, 0x6C, 0x24, 0x30] (LoadPre 0x12092f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x12092f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12092f 5 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x12092f 5 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x12092f 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f193 : InstrSpec 0x120934 [0x48, 0xF7, 0xE5] (fun s => s.RIP = 0x120934) (mulR64Effect 0x120934 5)
      [.gpr 5, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120934 5).toInstrSpec (mul_r64_effect_step 0x120934 0x48 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f194 : InstrSpec 0x120937 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x120937) (movR64R64Effect 0x120937 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x120937 6 2).toInstrSpec (mov_r64_r64_effect_step 0x120937 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f195 : InstrSpec 0x12093a [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x12093a) (movR64R64Effect 0x12093a 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x12093a 9 0).toInstrSpec (mov_r64_r64_effect_step 0x12093a 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f196 : InstrSpec 0x12093d [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x12093d) (movR64R64Effect 0x12093d 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12093d 0 8).toInstrSpec (mov_r64_r64_effect_step 0x12093d 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f197 : InstrSpec 0x120940 [0x49, 0xF7, 0xE3] (fun s => s.RIP = 0x120940) (mulR64Effect 0x120940 11)
      [.gpr 11, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120940 11).toInstrSpec (mul_r64_effect_step 0x120940 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f198 : InstrSpec 0x120943 [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x120943) (movR64R64Effect 0x120943 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x120943 11 2).toInstrSpec (mov_r64_r64_effect_step 0x120943 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f199 : InstrSpec 0x120946 [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x120946) (movR64R64Effect 0x120946 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x120946 3 0).toInstrSpec (mov_r64_r64_effect_step 0x120946 0x48 0xc3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 443) (RestInside.out (n := 443) f180 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 444) (ρ' := [(0, 437), (1, 443), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 435), (8, 331), (9, 402), (10, 430), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120901) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 445) (RestInside.out (n := 445) f181 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 446) (ρ' := [(0, 437), (1, 443), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 435), (8, 331), (9, 402), (10, 430), (11, 387), (12, 355), (13, 445), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120904) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 447) (RestInside.out (n := 447) f182 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 448) (ρ' := [(0, 437), (1, 447), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 435), (8, 331), (9, 402), (10, 430), (11, 387), (12, 355), (13, 445), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12090e) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 449) (RestInside.out (n := 449) f183 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 450) (ρ' := [(0, 437), (1, 447), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 435), (8, 331), (9, 402), (10, 430), (11, 387), (12, 355), (13, 445), (14, 449), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120913) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 451) (RestInside.out (n := 451) f184 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 452) (ρ' := [(0, 437), (1, 447), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 435), (8, 331), (9, 402), (10, 430), (11, 387), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120916) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 453) (RestInside.out (n := 453) f185 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 454) (ρ' := [(0, 437), (1, 447), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 435), (8, 453), (9, 402), (10, 430), (11, 387), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120919) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 455) (RestInside.exec (n := 455) (ρ' := [(0, 437), (1, 447), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 435), (8, 453), (9, 402), (10, 430), (11, 387), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12091e) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 456) (RestInside.out (n := 456) f187 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 457) (ρ' := [(0, 437), (1, 447), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 456), (8, 453), (9, 402), (10, 430), (11, 387), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120921) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 458) (RestInside.out (n := 458) f188 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 459) (ρ' := [(0, 437), (1, 447), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 458), (8, 453), (9, 402), (10, 430), (11, 387), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120924) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 460) (RestInside.out (n := 460) f189 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 461) (ρ' := [(0, 437), (1, 447), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 458), (8, 453), (9, 402), (10, 460), (11, 387), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120927) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 462) (RestInside.out (n := 462) f190 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 463) (ρ' := [(0, 462), (1, 447), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 458), (8, 453), (9, 402), (10, 460), (11, 387), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12092a) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 464) (RestInside.exec (n := 464) (ρ' := [(0, 462), (1, 447), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 458), (8, 453), (9, 402), (10, 460), (11, 387), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12092f) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 465) (RestInside.out (n := 465) f192 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 466) (ρ' := [(0, 462), (1, 447), (2, 428), (3, 416), (4, 4), (5, 465), (6, 406), (7, 458), (8, 453), (9, 402), (10, 460), (11, 387), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120934) f192 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 467) (RestInside.out (n := 467) f193 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 468) f193 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 469) (ρ' := [(0, 467), (1, 447), (2, 468), (3, 416), (4, 4), (5, 465), (6, 406), (7, 458), (8, 453), (9, 402), (10, 460), (11, 387), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120937) f193 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 470) (RestInside.out (n := 470) f194 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 471) (ρ' := [(0, 467), (1, 447), (2, 468), (3, 416), (4, 4), (5, 465), (6, 470), (7, 458), (8, 453), (9, 402), (10, 460), (11, 387), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12093a) f194 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 472) (RestInside.out (n := 472) f195 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 473) (ρ' := [(0, 467), (1, 447), (2, 468), (3, 416), (4, 4), (5, 465), (6, 470), (7, 458), (8, 453), (9, 472), (10, 460), (11, 387), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12093d) f195 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 474) (RestInside.out (n := 474) f196 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 475) (ρ' := [(0, 474), (1, 447), (2, 468), (3, 416), (4, 4), (5, 465), (6, 470), (7, 458), (8, 453), (9, 472), (10, 460), (11, 387), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120940) f196 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 476) (RestInside.out (n := 476) f197 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 477) f197 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 478) (ρ' := [(0, 476), (1, 447), (2, 477), (3, 416), (4, 4), (5, 465), (6, 470), (7, 458), (8, 453), (9, 472), (10, 460), (11, 387), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120943) f197 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 479) (RestInside.out (n := 479) f198 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 480) (ρ' := [(0, 476), (1, 447), (2, 477), (3, 416), (4, 4), (5, 465), (6, 470), (7, 458), (8, 453), (9, 472), (10, 460), (11, 479), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120946) f198 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 481) (RestInside.out (n := 481) f199 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 482) (ρ' := [(0, 476), (1, 447), (2, 477), (3, 481), (4, 4), (5, 465), (6, 470), (7, 458), (8, 453), (9, 472), (10, 460), (11, 479), (12, 355), (13, 445), (14, 451), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120949) f199 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_10 code

theorem rest_l12065f_8 [Bindings] (code : CodeMap) :
    Rest (n := 399) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 394), (1, 343), (2, 385), (3, 397), (4, 4), (5, 376), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]
      276 0x1208a8 bytes_l12065f_8 b_l12065f_8 := by
  have f160 : InstrSpec 0x1208a8 [0x4C, 0x01, 0xD0] (fun s => s.RIP = 0x1208a8) (addR64R64Effect 0x1208a8 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1208a8 0 10).toInstrSpec (add_r64_r64_effect_step 0x1208a8 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f161 : InstrSpec 0x1208ab [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x1208ab) (movR64R64Effect 0x1208ab 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1208ab 9 0).toInstrSpec (mov_r64_r64_effect_step 0x1208ab 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f162 : InstrSpec 0x1208ae [0x48, 0x11, 0xCB] (fun s => s.RIP = 0x1208ae) (atFlags StatusFlags.CF (adcR64R64Effect 0x1208ae 3 1))
      [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1208ae 3 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1208ae 0x48 0xcb c (by decide) (by decide))) pre_rip
  have f163 : InstrSpec 0x1208b1 [0x4C, 0x0F, 0xA4, 0xFE, 0x0C] (fun s => s.RIP = 0x1208b1) (shldR64R64Effect 0x1208b1 5 6 15 12)
      [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1208b1 5 6 15 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1208b1 0x4c (by decide) 0xfe (by decide) 0xc) pre_rip
  have f164 : InstrSpec 0x1208b6 [0x48, 0xB9, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x1208b6) (movR64Imm64Effect 0x1208b6 1 0xffffffffffffe)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x1208b6 1 0xffffffffffffe).toInstrSpec (mov_r64_imm64_effect_step 0x1208b6 0x48 0xb9 (by decide) (by decide) 0xffffffffffffe) pre_rip
  have f165 : InstrSpec 0x1208c0 [0x48, 0x23, 0x4C, 0x24, 0x08] (LoadPre 0x1208c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1208c0 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x1208c0 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (andR64M64Effect_footprint 0x1208c0 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (and_r64_m64_effect_step 0x1208c0 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f166 : InstrSpec 0x1208c5 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x1208c5) (movR64R64Effect 0x1208c5 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1208c5 7 3).toInstrSpec (mov_r64_r64_effect_step 0x1208c5 0x48 0xdf (by decide) (by decide)) pre_rip
  have f167 : InstrSpec 0x1208c8 [0x48, 0xC1, 0xEF, 0x34] (fun s => s.RIP = 0x1208c8) (shrR64Effect 0x1208c8 4 7 52)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x1208c8 4 7 52).toInstrSpec (shr_r64_imm8_effect_step 0x1208c8 0x48 0xef 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f168 : InstrSpec 0x1208cc [0x48, 0x0F, 0xA4, 0xC3, 0x0C] (fun s => s.RIP = 0x1208cc) (shldR64R64Effect 0x1208cc 5 3 0 12)
      [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1208cc 5 3 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1208cc 0x48 (by decide) 0xc3 (by decide) 0xc) pre_rip
  have f169 : InstrSpec 0x1208d1 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x1208d1) (movR64R64Effect 0x1208d1 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1208d1 0 6).toInstrSpec (mov_r64_r64_effect_step 0x1208d1 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f170 : InstrSpec 0x1208d4 [0x48, 0xF7, 0xE5] (fun s => s.RIP = 0x1208d4) (mulR64Effect 0x1208d4 5)
      [.gpr 5, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1208d4 5).toInstrSpec (mul_r64_effect_step 0x1208d4 0x48 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f171 : InstrSpec 0x1208d7 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x1208d7) (movR64R64Effect 0x1208d7 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1208d7 10 0).toInstrSpec (mov_r64_r64_effect_step 0x1208d7 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f172 : InstrSpec 0x1208da [0x49, 0x01, 0xCA] (fun s => s.RIP = 0x1208da) (addR64R64Effect 0x1208da 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1208da 10 1).toInstrSpec (add_r64_r64_effect_step 0x1208da 0x49 0xca (by decide) (by decide)) pre_rip
  have f173 : InstrSpec 0x1208dd [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x1208dd) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1208dd 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x1208dd 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x1208dd 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f174 : InstrSpec 0x1208e1 [0x49, 0x01, 0xDA] (fun s => s.RIP = 0x1208e1) (addR64R64Effect 0x1208e1 10 3)
      [.gpr 10, .gpr 3] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1208e1 10 3).toInstrSpec (add_r64_r64_effect_step 0x1208e1 0x49 0xda (by decide) (by decide)) pre_rip
  have f175 : InstrSpec 0x1208e4 [0x48, 0x11, 0xD7] (fun s => s.RIP = 0x1208e4) (atFlags StatusFlags.CF (adcR64R64Effect 0x1208e4 7 2))
      [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 7, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1208e4 7 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1208e4 0x48 0xd7 c (by decide) (by decide))) pre_rip
  have f176 : InstrSpec 0x1208e7 [0x4C, 0x0F, 0xA4, 0xD7, 0x0C] (fun s => s.RIP = 0x1208e7) (shldR64R64Effect 0x1208e7 5 7 10 12)
      [.gpr 7, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1208e7 5 7 10 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1208e7 0x4c (by decide) 0xd7 (by decide) 0xc) pre_rip
  have f177 : InstrSpec 0x1208ec [0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x1208ec) (movR64Imm64Effect 0x1208ec 0 0xffffffffffff)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1208ec 0 0xffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x1208ec 0x48 0xb8 (by decide) (by decide) 0xffffffffffff) pre_rip
  have f178 : InstrSpec 0x1208f6 [0x48, 0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x1208f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1208f6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1208f6 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1208f6 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1208f6 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f179 : InstrSpec 0x1208fb [0x48, 0x21, 0xC1] (fun s => s.RIP = 0x1208fb) (andR64R64Effect 0x1208fb 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1208fb 1 0).toInstrSpec (and_r64_r64_effect_step 0x1208fb 0x48 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 399) (RestInside.out (n := 399) f160 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 400) f160 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 401) (ρ' := [(0, 399), (1, 343), (2, 385), (3, 397), (4, 4), (5, 376), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (16, 400), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208ab) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 402) (RestInside.out (n := 402) f161 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 403) (ρ' := [(0, 399), (1, 343), (2, 385), (3, 397), (4, 4), (5, 376), (6, 367), (7, 318), (8, 331), (9, 402), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (16, 400), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208ae) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 404) (RestInside.out (n := 404) f162 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 405) (ρ' := [(0, 399), (1, 343), (2, 385), (3, 404), (4, 4), (5, 376), (6, 367), (7, 318), (8, 331), (9, 402), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208b1) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 406) (RestInside.out (n := 406) f163 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 407) (ρ' := [(0, 399), (1, 343), (2, 385), (3, 404), (4, 4), (5, 376), (6, 406), (7, 318), (8, 331), (9, 402), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208b6) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 408) (RestInside.out (n := 408) f164 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 409) (ρ' := [(0, 399), (1, 408), (2, 385), (3, 404), (4, 4), (5, 376), (6, 406), (7, 318), (8, 331), (9, 402), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208c0) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 410) (RestInside.out (n := 410) f165 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 411) (ρ' := [(0, 399), (1, 410), (2, 385), (3, 404), (4, 4), (5, 376), (6, 406), (7, 318), (8, 331), (9, 402), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208c5) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 412) (RestInside.out (n := 412) f166 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 413) (ρ' := [(0, 399), (1, 410), (2, 385), (3, 404), (4, 4), (5, 376), (6, 406), (7, 412), (8, 331), (9, 402), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208c8) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 414) (RestInside.out (n := 414) f167 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 415) (ρ' := [(0, 399), (1, 410), (2, 385), (3, 404), (4, 4), (5, 376), (6, 406), (7, 414), (8, 331), (9, 402), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208cc) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 416) (RestInside.out (n := 416) f168 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 417) (ρ' := [(0, 399), (1, 410), (2, 385), (3, 416), (4, 4), (5, 376), (6, 406), (7, 414), (8, 331), (9, 402), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208d1) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 418) (RestInside.out (n := 418) f169 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 419) (ρ' := [(0, 418), (1, 410), (2, 385), (3, 416), (4, 4), (5, 376), (6, 406), (7, 414), (8, 331), (9, 402), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208d4) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 420) (RestInside.out (n := 420) f170 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 421) f170 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 422) (ρ' := [(0, 420), (1, 410), (2, 421), (3, 416), (4, 4), (5, 376), (6, 406), (7, 414), (8, 331), (9, 402), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208d7) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 423) (RestInside.out (n := 423) f171 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 424) (ρ' := [(0, 420), (1, 410), (2, 421), (3, 416), (4, 4), (5, 376), (6, 406), (7, 414), (8, 331), (9, 402), (10, 423), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208da) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 425) (RestInside.out (n := 425) f172 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 426) f172 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 427) (ρ' := [(0, 420), (1, 410), (2, 421), (3, 416), (4, 4), (5, 376), (6, 406), (7, 414), (8, 331), (9, 402), (10, 425), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (16, 426), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208dd) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 428) (RestInside.out (n := 428) f173 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 429) (ρ' := [(0, 420), (1, 410), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 414), (8, 331), (9, 402), (10, 425), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208e1) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 430) (RestInside.out (n := 430) f174 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 431) f174 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 432) (ρ' := [(0, 420), (1, 410), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 414), (8, 331), (9, 402), (10, 430), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (16, 431), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208e4) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 433) (RestInside.out (n := 433) f175 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 434) (ρ' := [(0, 420), (1, 410), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 433), (8, 331), (9, 402), (10, 430), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208e7) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 435) (RestInside.out (n := 435) f176 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 436) (ρ' := [(0, 420), (1, 410), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 435), (8, 331), (9, 402), (10, 430), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208ec) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 437) (RestInside.out (n := 437) f177 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 438) (ρ' := [(0, 437), (1, 410), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 435), (8, 331), (9, 402), (10, 430), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208f6) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 439) (RestInside.out (n := 439) f178 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 440) (ρ' := [(0, 437), (1, 439), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 435), (8, 331), (9, 402), (10, 430), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208fb) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 441) (RestInside.out (n := 441) f179 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 442) (ρ' := [(0, 437), (1, 441), (2, 428), (3, 416), (4, 4), (5, 376), (6, 406), (7, 435), (8, 331), (9, 402), (10, 430), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208fe) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_9 code

theorem rest_l12065f_7 [Bindings] (code : CodeMap) :
    Rest (n := 353) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 350), (1, 343), (2, 351), (3, 280), (4, 4), (5, 314), (6, 339), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 307), (13, 60), (14, 337), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]
      296 0x12086a bytes_l12065f_7 b_l12065f_7 := by
  have f140 : InstrSpec 0x12086a [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x12086a) (movR64R64Effect 0x12086a 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x12086a 3 2).toInstrSpec (mov_r64_r64_effect_step 0x12086a 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f141 : InstrSpec 0x12086d [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x12086d) (movR64R64Effect 0x12086d 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x12086d 12 0).toInstrSpec (mov_r64_r64_effect_step 0x12086d 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f142 : InstrSpec 0x120870 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x120870) (movR64R64Effect 0x120870 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120870 0 15).toInstrSpec (mov_r64_r64_effect_step 0x120870 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f143 : InstrSpec 0x120873 [0x49, 0xF7, 0xE3] (fun s => s.RIP = 0x120873) (mulR64Effect 0x120873 11)
      [.gpr 11, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120873 11).toInstrSpec (mul_r64_effect_step 0x120873 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f144 : InstrSpec 0x120876 [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x120876) (movR64R64Effect 0x120876 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x120876 15 0).toInstrSpec (mov_r64_r64_effect_step 0x120876 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f145 : InstrSpec 0x120879 [0x4D, 0x01, 0xF7] (fun s => s.RIP = 0x120879) (addR64R64Effect 0x120879 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120879 15 14).toInstrSpec (add_r64_r64_effect_step 0x120879 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f146 : InstrSpec 0x12087c [0x48, 0x11, 0xD6] (fun s => s.RIP = 0x12087c) (atFlags StatusFlags.CF (adcR64R64Effect 0x12087c 6 2))
      [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x12087c 6 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x12087c 0x48 0xd6 c (by decide) (by decide))) pre_rip
  have f147 : InstrSpec 0x12087f [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x12087f) (movR64R64Effect 0x12087f 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12087f 0 15).toInstrSpec (mov_r64_r64_effect_step 0x12087f 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f148 : InstrSpec 0x120882 [0x48, 0x21, 0xE8] (fun s => s.RIP = 0x120882) (andR64R64Effect 0x120882 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120882 0 5).toInstrSpec (and_r64_r64_effect_step 0x120882 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f149 : InstrSpec 0x120885 [0x48, 0xF7, 0xE7] (fun s => s.RIP = 0x120885) (mulR64Effect 0x120885 7)
      [.gpr 7, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120885 7).toInstrSpec (mul_r64_effect_step 0x120885 0x48 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f150 : InstrSpec 0x120888 [0x48, 0x89, 0xFD] (fun s => s.RIP = 0x120888) (movR64R64Effect 0x120888 5 7)
      [.gpr 7] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x120888 5 7).toInstrSpec (mov_r64_r64_effect_step 0x120888 0x48 0xfd (by decide) (by decide)) pre_rip
  have f151 : InstrSpec 0x12088b [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x12088b) (movR64R64Effect 0x12088b 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x12088b 14 2).toInstrSpec (mov_r64_r64_effect_step 0x12088b 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f152 : InstrSpec 0x12088e [0x49, 0x89, 0xC5] (fun s => s.RIP = 0x12088e) (movR64R64Effect 0x12088e 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x12088e 13 0).toInstrSpec (mov_r64_r64_effect_step 0x12088e 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f153 : InstrSpec 0x120891 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x120891 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x120891 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120891 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120891 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x120891 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f154 : InstrSpec 0x120896 [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x120896) (mulR64Effect 0x120896 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120896 9).toInstrSpec (mul_r64_effect_step 0x120896 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f155 : InstrSpec 0x120899 [0x4D, 0x89, 0xCB] (fun s => s.RIP = 0x120899) (movR64R64Effect 0x120899 11 9)
      [.gpr 9] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x120899 11 9).toInstrSpec (mov_r64_r64_effect_step 0x120899 0x4d 0xcb (by decide) (by decide)) pre_rip
  have f156 : InstrSpec 0x12089c [0x4C, 0x01, 0xE0] (fun s => s.RIP = 0x12089c) (addR64R64Effect 0x12089c 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12089c 0 12).toInstrSpec (add_r64_r64_effect_step 0x12089c 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f157 : InstrSpec 0x12089f [0x48, 0x11, 0xD3] (fun s => s.RIP = 0x12089f) (atFlags StatusFlags.CF (adcR64R64Effect 0x12089f 3 2))
      [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x12089f 3 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x12089f 0x48 0xd3 c (by decide) (by decide))) pre_rip
  have f158 : InstrSpec 0x1208a2 [0x4C, 0x01, 0xE8] (fun s => s.RIP = 0x1208a2) (addR64R64Effect 0x1208a2 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1208a2 0 13).toInstrSpec (add_r64_r64_effect_step 0x1208a2 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f159 : InstrSpec 0x1208a5 [0x4C, 0x11, 0xF3] (fun s => s.RIP = 0x1208a5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1208a5 3 14))
      [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1208a5 3 14).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1208a5 0x4c 0xf3 c (by decide) (by decide))) pre_rip
  refine Rest.ofInside (n := 353) (RestInside.out (n := 353) f140 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 354) (ρ' := [(0, 350), (1, 343), (2, 351), (3, 353), (4, 4), (5, 314), (6, 339), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 307), (13, 60), (14, 337), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12086d) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 355) (RestInside.out (n := 355) f141 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 356) (ρ' := [(0, 350), (1, 343), (2, 351), (3, 353), (4, 4), (5, 314), (6, 339), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 355), (13, 60), (14, 337), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120870) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 357) (RestInside.out (n := 357) f142 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 358) (ρ' := [(0, 357), (1, 343), (2, 351), (3, 353), (4, 4), (5, 314), (6, 339), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 355), (13, 60), (14, 337), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120873) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 359) (RestInside.out (n := 359) f143 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 360) f143 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 361) (ρ' := [(0, 359), (1, 343), (2, 360), (3, 353), (4, 4), (5, 314), (6, 339), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 355), (13, 60), (14, 337), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120876) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 362) (RestInside.out (n := 362) f144 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 363) (ρ' := [(0, 359), (1, 343), (2, 360), (3, 353), (4, 4), (5, 314), (6, 339), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 355), (13, 60), (14, 337), (15, 362), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120879) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 364) (RestInside.out (n := 364) f145 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 365) f145 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 366) (ρ' := [(0, 359), (1, 343), (2, 360), (3, 353), (4, 4), (5, 314), (6, 339), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 355), (13, 60), (14, 337), (15, 364), (16, 365), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12087c) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 367) (RestInside.out (n := 367) f146 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 368) (ρ' := [(0, 359), (1, 343), (2, 360), (3, 353), (4, 4), (5, 314), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 355), (13, 60), (14, 337), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12087f) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 369) (RestInside.out (n := 369) f147 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 370) (ρ' := [(0, 369), (1, 343), (2, 360), (3, 353), (4, 4), (5, 314), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 355), (13, 60), (14, 337), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120882) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 371) (RestInside.out (n := 371) f148 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 372) (ρ' := [(0, 371), (1, 343), (2, 360), (3, 353), (4, 4), (5, 314), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 355), (13, 60), (14, 337), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120885) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 373) (RestInside.out (n := 373) f149 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 374) f149 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 375) (ρ' := [(0, 373), (1, 343), (2, 374), (3, 353), (4, 4), (5, 314), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 355), (13, 60), (14, 337), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120888) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 376) (RestInside.out (n := 376) f150 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 377) (ρ' := [(0, 373), (1, 343), (2, 374), (3, 353), (4, 4), (5, 376), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 355), (13, 60), (14, 337), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12088b) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 378) (RestInside.out (n := 378) f151 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 379) (ρ' := [(0, 373), (1, 343), (2, 374), (3, 353), (4, 4), (5, 376), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 355), (13, 60), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12088e) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 380) (RestInside.out (n := 380) f152 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 381) (ρ' := [(0, 373), (1, 343), (2, 374), (3, 353), (4, 4), (5, 376), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120891) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 382) (RestInside.out (n := 382) f153 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 383) (ρ' := [(0, 382), (1, 343), (2, 374), (3, 353), (4, 4), (5, 376), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120896) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 384) (RestInside.out (n := 384) f154 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 385) f154 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 386) (ρ' := [(0, 384), (1, 343), (2, 385), (3, 353), (4, 4), (5, 376), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120899) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 387) (RestInside.out (n := 387) f155 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 388) (ρ' := [(0, 384), (1, 343), (2, 385), (3, 353), (4, 4), (5, 376), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12089c) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 389) (RestInside.out (n := 389) f156 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 390) f156 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 391) (ρ' := [(0, 389), (1, 343), (2, 385), (3, 353), (4, 4), (5, 376), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (16, 390), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12089f) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 392) (RestInside.out (n := 392) f157 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 393) (ρ' := [(0, 389), (1, 343), (2, 385), (3, 392), (4, 4), (5, 376), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208a2) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 394) (RestInside.out (n := 394) f158 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 395) f158 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 396) (ρ' := [(0, 394), (1, 343), (2, 385), (3, 392), (4, 4), (5, 376), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (16, 395), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208a5) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 397) (RestInside.out (n := 397) f159 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 398) (ρ' := [(0, 394), (1, 343), (2, 385), (3, 397), (4, 4), (5, 376), (6, 367), (7, 318), (8, 331), (9, 216), (10, 345), (11, 387), (12, 355), (13, 380), (14, 378), (15, 364), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1208a8) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_8 code

theorem rest_l12065f_6 [Bindings] (code : CodeMap) :
    Rest (n := 310) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 297), (1, 247), (2, 298), (3, 280), (4, 4), (5, 97), (6, 249), (7, 289), (8, 270), (9, 216), (10, 278), (11, 282), (12, 307), (13, 60), (14, 305), (15, 293), (16, 308), (22, 22), (39, 39), (50, 50), (51, 51)]
      316 0x120817 bytes_l12065f_6 b_l12065f_6 := by
  have f120 : InstrSpec 0x120817 [0x49, 0x11, 0xCE] (fun s => s.RIP = 0x120817) (atFlags StatusFlags.CF (adcR64R64Effect 0x120817 14 1))
      [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120817 14 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120817 0x49 0xce c (by decide) (by decide))) pre_rip
  have f121 : InstrSpec 0x12081a [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x12081a) (movR64R64Effect 0x12081a 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12081a 0 12).toInstrSpec (mov_r64_r64_effect_step 0x12081a 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x12081d [0x48, 0xBD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x12081d) (movR64Imm64Effect 0x12081d 5 0xfffffffffffff)
      [] [] [.reg 5, .rip] :=
    (movR64Imm64Effect_footprint 0x12081d 5 0xfffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x12081d 0x48 0xbd (by decide) (by decide) 0xfffffffffffff) pre_rip
  have f123 : InstrSpec 0x120827 [0x48, 0x21, 0xE8] (fun s => s.RIP = 0x120827) (andR64R64Effect 0x120827 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120827 0 5).toInstrSpec (and_r64_r64_effect_step 0x120827 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x12082a [0x48, 0xBF, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12082a) (movR64Imm64Effect 0x12082a 7 0x1000003d10)
      [] [] [.reg 7, .rip] :=
    (movR64Imm64Effect_footprint 0x12082a 7 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x12082a 0x48 0xbf (by decide) (by decide) 0x1000003d10) pre_rip
  have f125 : InstrSpec 0x120834 [0x48, 0xF7, 0xE7] (fun s => s.RIP = 0x120834) (mulR64Effect 0x120834 7)
      [.gpr 7, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120834 7).toInstrSpec (mul_r64_effect_step 0x120834 0x48 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f126 : InstrSpec 0x120837 [0x48, 0x01, 0xD8] (fun s => s.RIP = 0x120837) (addR64R64Effect 0x120837 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120837 0 3).toInstrSpec (add_r64_r64_effect_step 0x120837 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f127 : InstrSpec 0x12083a [0x49, 0x11, 0xD2] (fun s => s.RIP = 0x12083a) (atFlags StatusFlags.CF (adcR64R64Effect 0x12083a 10 2))
      [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x12083a 10 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x12083a 0x49 0xd2 c (by decide) (by decide))) pre_rip
  have f128 : InstrSpec 0x12083d [0x4C, 0x01, 0xC0] (fun s => s.RIP = 0x12083d) (addR64R64Effect 0x12083d 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12083d 0 8).toInstrSpec (add_r64_r64_effect_step 0x12083d 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f129 : InstrSpec 0x120840 [0x49, 0x89, 0xC0] (fun s => s.RIP = 0x120840) (movR64R64Effect 0x120840 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x120840 8 0).toInstrSpec (mov_r64_r64_effect_step 0x120840 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x120843 [0x49, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x120843) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x120843 10 0x0))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x120843 10 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x120843 0x49 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f131 : InstrSpec 0x120847 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x120847) (movR64R64Effect 0x120847 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x120847 6 14).toInstrSpec (mov_r64_r64_effect_step 0x120847 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f132 : InstrSpec 0x12084a [0x4D, 0x0F, 0xA4, 0xE6, 0x0C] (fun s => s.RIP = 0x12084a) (shldR64R64Effect 0x12084a 5 14 12 12)
      [.gpr 14, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x12084a 5 14 12 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x12084a 0x4d (by decide) 0xe6 (by decide) 0xc) pre_rip
  have f133 : InstrSpec 0x12084f [0x48, 0xC1, 0xEE, 0x34] (fun s => s.RIP = 0x12084f) (shrR64Effect 0x12084f 4 6 52)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x12084f 4 6 52).toInstrSpec (shr_r64_imm8_effect_step 0x12084f 0x48 0xee 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f134 : InstrSpec 0x120853 [0x4C, 0x89, 0xD1] (fun s => s.RIP = 0x120853) (movR64R64Effect 0x120853 1 10)
      [.gpr 10] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x120853 1 10).toInstrSpec (mov_r64_r64_effect_step 0x120853 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f135 : InstrSpec 0x120856 [0x48, 0xC1, 0xE9, 0x34] (fun s => s.RIP = 0x120856) (shrR64Effect 0x120856 4 1 52)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x120856 4 1 52).toInstrSpec (shr_r64_imm8_effect_step 0x120856 0x48 0xe9 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f136 : InstrSpec 0x12085a [0x49, 0x0F, 0xA4, 0xC2, 0x0C] (fun s => s.RIP = 0x12085a) (shldR64R64Effect 0x12085a 5 10 0 12)
      [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x12085a 5 10 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x12085a 0x49 (by decide) 0xc2 (by decide) 0xc) pre_rip
  have f137 : InstrSpec 0x12085f [0x4C, 0x89, 0xE8] (fun s => s.RIP = 0x12085f) (movR64R64Effect 0x12085f 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12085f 0 13).toInstrSpec (mov_r64_r64_effect_step 0x12085f 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f138 : InstrSpec 0x120862 [0x4C, 0x89, 0x6C, 0x24, 0x58] (StorePre 0x120862 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x120862 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120862 13 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120862 13 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x120862 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f139 : InstrSpec 0x120867 [0x48, 0xF7, 0xE0] (fun s => s.RIP = 0x120867) (mulR64Effect 0x120867 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120867 0).toInstrSpec (mul_r64_effect_step 0x120867 0x48 0xe0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 310) (RestInside.out (n := 310) f120 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 311) (ρ' := [(0, 297), (1, 247), (2, 298), (3, 280), (4, 4), (5, 97), (6, 249), (7, 289), (8, 270), (9, 216), (10, 278), (11, 282), (12, 307), (13, 60), (14, 310), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12081a) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 312) (RestInside.out (n := 312) f121 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 313) (ρ' := [(0, 312), (1, 247), (2, 298), (3, 280), (4, 4), (5, 97), (6, 249), (7, 289), (8, 270), (9, 216), (10, 278), (11, 282), (12, 307), (13, 60), (14, 310), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12081d) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 314) (RestInside.out (n := 314) f122 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 315) (ρ' := [(0, 312), (1, 247), (2, 298), (3, 280), (4, 4), (5, 314), (6, 249), (7, 289), (8, 270), (9, 216), (10, 278), (11, 282), (12, 307), (13, 60), (14, 310), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120827) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 316) (RestInside.out (n := 316) f123 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 317) (ρ' := [(0, 316), (1, 247), (2, 298), (3, 280), (4, 4), (5, 314), (6, 249), (7, 289), (8, 270), (9, 216), (10, 278), (11, 282), (12, 307), (13, 60), (14, 310), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12082a) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 318) (RestInside.out (n := 318) f124 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 319) (ρ' := [(0, 316), (1, 247), (2, 298), (3, 280), (4, 4), (5, 314), (6, 249), (7, 318), (8, 270), (9, 216), (10, 278), (11, 282), (12, 307), (13, 60), (14, 310), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120834) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 320) (RestInside.out (n := 320) f125 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 321) f125 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 322) (ρ' := [(0, 320), (1, 247), (2, 321), (3, 280), (4, 4), (5, 314), (6, 249), (7, 318), (8, 270), (9, 216), (10, 278), (11, 282), (12, 307), (13, 60), (14, 310), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120837) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 323) (RestInside.out (n := 323) f126 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 324) f126 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 325) (ρ' := [(0, 323), (1, 247), (2, 321), (3, 280), (4, 4), (5, 314), (6, 249), (7, 318), (8, 270), (9, 216), (10, 278), (11, 282), (12, 307), (13, 60), (14, 310), (15, 293), (16, 324), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12083a) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 326) (RestInside.out (n := 326) f127 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 327) (ρ' := [(0, 323), (1, 247), (2, 321), (3, 280), (4, 4), (5, 314), (6, 249), (7, 318), (8, 270), (9, 216), (10, 326), (11, 282), (12, 307), (13, 60), (14, 310), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12083d) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 328) (RestInside.out (n := 328) f128 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 329) f128 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 330) (ρ' := [(0, 328), (1, 247), (2, 321), (3, 280), (4, 4), (5, 314), (6, 249), (7, 318), (8, 270), (9, 216), (10, 326), (11, 282), (12, 307), (13, 60), (14, 310), (15, 293), (16, 329), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120840) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 331) (RestInside.out (n := 331) f129 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 332) (ρ' := [(0, 328), (1, 247), (2, 321), (3, 280), (4, 4), (5, 314), (6, 249), (7, 318), (8, 331), (9, 216), (10, 326), (11, 282), (12, 307), (13, 60), (14, 310), (15, 293), (16, 329), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120843) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 333) (RestInside.out (n := 333) f130 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 334) (ρ' := [(0, 328), (1, 247), (2, 321), (3, 280), (4, 4), (5, 314), (6, 249), (7, 318), (8, 331), (9, 216), (10, 333), (11, 282), (12, 307), (13, 60), (14, 310), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120847) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 335) (RestInside.out (n := 335) f131 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 336) (ρ' := [(0, 328), (1, 247), (2, 321), (3, 280), (4, 4), (5, 314), (6, 335), (7, 318), (8, 331), (9, 216), (10, 333), (11, 282), (12, 307), (13, 60), (14, 310), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12084a) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 337) (RestInside.out (n := 337) f132 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 338) (ρ' := [(0, 328), (1, 247), (2, 321), (3, 280), (4, 4), (5, 314), (6, 335), (7, 318), (8, 331), (9, 216), (10, 333), (11, 282), (12, 307), (13, 60), (14, 337), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12084f) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 339) (RestInside.out (n := 339) f133 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 340) (ρ' := [(0, 328), (1, 247), (2, 321), (3, 280), (4, 4), (5, 314), (6, 339), (7, 318), (8, 331), (9, 216), (10, 333), (11, 282), (12, 307), (13, 60), (14, 337), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120853) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 341) (RestInside.out (n := 341) f134 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 342) (ρ' := [(0, 328), (1, 341), (2, 321), (3, 280), (4, 4), (5, 314), (6, 339), (7, 318), (8, 331), (9, 216), (10, 333), (11, 282), (12, 307), (13, 60), (14, 337), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120856) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 343) (RestInside.out (n := 343) f135 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 344) (ρ' := [(0, 328), (1, 343), (2, 321), (3, 280), (4, 4), (5, 314), (6, 339), (7, 318), (8, 331), (9, 216), (10, 333), (11, 282), (12, 307), (13, 60), (14, 337), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12085a) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 345) (RestInside.out (n := 345) f136 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 346) (ρ' := [(0, 328), (1, 343), (2, 321), (3, 280), (4, 4), (5, 314), (6, 339), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 307), (13, 60), (14, 337), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12085f) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 347) (RestInside.out (n := 347) f137 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 348) (ρ' := [(0, 347), (1, 343), (2, 321), (3, 280), (4, 4), (5, 314), (6, 339), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 307), (13, 60), (14, 337), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120862) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 349) (RestInside.exec (n := 349) (ρ' := [(0, 347), (1, 343), (2, 321), (3, 280), (4, 4), (5, 314), (6, 339), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 307), (13, 60), (14, 337), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120867) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 350) (RestInside.out (n := 350) f139 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 351) f139 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 352) (ρ' := [(0, 350), (1, 343), (2, 351), (3, 280), (4, 4), (5, 314), (6, 339), (7, 318), (8, 331), (9, 216), (10, 345), (11, 282), (12, 307), (13, 60), (14, 337), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12086a) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_7 code

theorem rest_l12065f_5 [Bindings] (code : CodeMap) :
    Rest (n := 267) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 264), (1, 247), (2, 262), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (16, 265), (22, 22), (39, 39), (50, 50), (51, 51)]
      336 0x1207cf bytes_l12065f_5 b_l12065f_5 := by
  have f100 : InstrSpec 0x1207cf [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x1207cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1207cf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1207cf 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1207cf 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1207cf 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f101 : InstrSpec 0x1207d4 [0x49, 0x11, 0xD0] (fun s => s.RIP = 0x1207d4) (atFlags StatusFlags.CF (adcR64R64Effect 0x1207d4 8 2))
      [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1207d4 8 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1207d4 0x49 0xd0 c (by decide) (by decide))) pre_rip
  have f102 : InstrSpec 0x1207d7 [0x49, 0x0F, 0xA4, 0xC0, 0x0C] (fun s => s.RIP = 0x1207d7) (shldR64R64Effect 0x1207d7 5 8 0 12)
      [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1207d7 5 8 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1207d7 0x49 (by decide) 0xc0 (by decide) 0xc) pre_rip
  have f103 : InstrSpec 0x1207dc [0x4B, 0x8D, 0x04, 0x36] (fun s => s.RIP = 0x1207dc) (leaR64Effect 0x1207dc 0 (.sib 14 (some 14) 0 .none))
      [.gpr 14, .gpr 14] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1207dc 0 (.sib 14 (some 14) 0 .none)).toInstrSpec (lea_r64_effect_step 0x1207dc 0x4b (by decide) 0 (.sib 14 (some 14) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f104 : InstrSpec 0x1207e0 [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x1207e0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1207e0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1207e0 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1207e0 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1207e0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f105 : InstrSpec 0x1207e5 [0x49, 0xF7, 0xE5] (fun s => s.RIP = 0x1207e5) (mulR64Effect 0x1207e5 13)
      [.gpr 13, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1207e5 13).toInstrSpec (mul_r64_effect_step 0x1207e5 0x49 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x1207e8 [0x49, 0x89, 0xD2] (fun s => s.RIP = 0x1207e8) (movR64R64Effect 0x1207e8 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1207e8 10 2).toInstrSpec (mov_r64_r64_effect_step 0x1207e8 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x1207eb [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x1207eb) (movR64R64Effect 0x1207eb 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1207eb 3 0).toInstrSpec (mov_r64_r64_effect_step 0x1207eb 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x1207ee [0x4D, 0x89, 0xE3] (fun s => s.RIP = 0x1207ee) (movR64R64Effect 0x1207ee 11 12)
      [.gpr 12] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1207ee 11 12).toInstrSpec (mov_r64_r64_effect_step 0x1207ee 0x4d 0xe3 (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x1207f1 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x1207f1) (movR64R64Effect 0x1207f1 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1207f1 0 12).toInstrSpec (mov_r64_r64_effect_step 0x1207f1 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x1207f4 [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x1207f4) (mulR64Effect 0x1207f4 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1207f4 12).toInstrSpec (mul_r64_effect_step 0x1207f4 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x1207f7 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x1207f7) (movR64R64Effect 0x1207f7 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1207f7 7 0).toInstrSpec (mov_r64_r64_effect_step 0x1207f7 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f112 : InstrSpec 0x1207fa [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x1207fa) (movR64R64Effect 0x1207fa 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1207fa 14 2).toInstrSpec (mov_r64_r64_effect_step 0x1207fa 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f113 : InstrSpec 0x1207fd [0x4C, 0x8D, 0x3C, 0x6D, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1207fd) (leaR64Effect 0x1207fd 15 (.abs (some 5) 1 0x0))
      [.gpr 5] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x1207fd 15 (.abs (some 5) 1 0x0)).toInstrSpec (lea_r64_effect_step 0x1207fd 0x4c (by decide) 7 (.abs (some 5) 1 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x120805 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x120805) (movR64R64Effect 0x120805 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120805 0 15).toInstrSpec (mov_r64_r64_effect_step 0x120805 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x120808 [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x120808) (mulR64Effect 0x120808 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120808 9).toInstrSpec (mul_r64_effect_step 0x120808 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f116 : InstrSpec 0x12080b [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x12080b) (movR64R64Effect 0x12080b 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x12080b 12 0).toInstrSpec (mov_r64_r64_effect_step 0x12080b 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x12080e [0x49, 0x01, 0xFC] (fun s => s.RIP = 0x12080e) (addR64R64Effect 0x12080e 12 7)
      [.gpr 12, .gpr 7] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12080e 12 7).toInstrSpec (add_r64_r64_effect_step 0x12080e 0x49 0xfc (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x120811 [0x49, 0x11, 0xD6] (fun s => s.RIP = 0x120811) (atFlags StatusFlags.CF (adcR64R64Effect 0x120811 14 2))
      [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120811 14 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120811 0x49 0xd6 c (by decide) (by decide))) pre_rip
  have f119 : InstrSpec 0x120814 [0x49, 0x01, 0xF4] (fun s => s.RIP = 0x120814) (addR64R64Effect 0x120814 12 6)
      [.gpr 12, .gpr 6] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120814 12 6).toInstrSpec (add_r64_r64_effect_step 0x120814 0x49 0xf4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 267) (RestInside.exec (n := 267) (ρ' := [(0, 264), (1, 247), (2, 262), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (16, 265), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207d4) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f101 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 269) (ρ' := [(0, 264), (1, 247), (2, 262), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 268), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207d7) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 270) (RestInside.out (n := 270) f102 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 271) (ρ' := [(0, 264), (1, 247), (2, 262), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 270), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207dc) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 272) (RestInside.out (n := 272) f103 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 273) (ρ' := [(0, 272), (1, 247), (2, 262), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 270), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207e0) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 274) (RestInside.exec (n := 274) (ρ' := [(0, 272), (1, 247), (2, 262), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 270), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207e5) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 275) (RestInside.out (n := 275) f105 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 276) f105 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 277) (ρ' := [(0, 275), (1, 247), (2, 276), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 270), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207e8) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 278) (RestInside.out (n := 278) f106 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 279) (ρ' := [(0, 275), (1, 247), (2, 276), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 270), (9, 216), (10, 278), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207eb) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 280) (RestInside.out (n := 280) f107 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 281) (ρ' := [(0, 275), (1, 247), (2, 276), (3, 280), (4, 4), (5, 97), (6, 249), (7, 192), (8, 270), (9, 216), (10, 278), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207ee) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 282) (RestInside.out (n := 282) f108 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 283) (ρ' := [(0, 275), (1, 247), (2, 276), (3, 280), (4, 4), (5, 97), (6, 249), (7, 192), (8, 270), (9, 216), (10, 278), (11, 282), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207f1) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 284) (RestInside.out (n := 284) f109 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 285) (ρ' := [(0, 284), (1, 247), (2, 276), (3, 280), (4, 4), (5, 97), (6, 249), (7, 192), (8, 270), (9, 216), (10, 278), (11, 282), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207f4) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 286) (RestInside.out (n := 286) f110 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 287) f110 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 288) (ρ' := [(0, 286), (1, 247), (2, 287), (3, 280), (4, 4), (5, 97), (6, 249), (7, 192), (8, 270), (9, 216), (10, 278), (11, 282), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207f7) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 289) (RestInside.out (n := 289) f111 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 290) (ρ' := [(0, 286), (1, 247), (2, 287), (3, 280), (4, 4), (5, 97), (6, 249), (7, 289), (8, 270), (9, 216), (10, 278), (11, 282), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207fa) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 291) (RestInside.out (n := 291) f112 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 292) (ρ' := [(0, 286), (1, 247), (2, 287), (3, 280), (4, 4), (5, 97), (6, 249), (7, 289), (8, 270), (9, 216), (10, 278), (11, 282), (12, 212), (13, 60), (14, 291), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207fd) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 293) (RestInside.out (n := 293) f113 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 294) (ρ' := [(0, 286), (1, 247), (2, 287), (3, 280), (4, 4), (5, 97), (6, 249), (7, 289), (8, 270), (9, 216), (10, 278), (11, 282), (12, 212), (13, 60), (14, 291), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120805) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 295) (RestInside.out (n := 295) f114 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 296) (ρ' := [(0, 295), (1, 247), (2, 287), (3, 280), (4, 4), (5, 97), (6, 249), (7, 289), (8, 270), (9, 216), (10, 278), (11, 282), (12, 212), (13, 60), (14, 291), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120808) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.out (n := 297) f115 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 298) f115 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 299) (ρ' := [(0, 297), (1, 247), (2, 298), (3, 280), (4, 4), (5, 97), (6, 249), (7, 289), (8, 270), (9, 216), (10, 278), (11, 282), (12, 212), (13, 60), (14, 291), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12080b) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 300) (RestInside.out (n := 300) f116 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 301) (ρ' := [(0, 297), (1, 247), (2, 298), (3, 280), (4, 4), (5, 97), (6, 249), (7, 289), (8, 270), (9, 216), (10, 278), (11, 282), (12, 300), (13, 60), (14, 291), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12080e) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f117 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 303) f117 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 304) (ρ' := [(0, 297), (1, 247), (2, 298), (3, 280), (4, 4), (5, 97), (6, 249), (7, 289), (8, 270), (9, 216), (10, 278), (11, 282), (12, 302), (13, 60), (14, 291), (15, 293), (16, 303), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120811) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 305) (RestInside.out (n := 305) f118 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 306) (ρ' := [(0, 297), (1, 247), (2, 298), (3, 280), (4, 4), (5, 97), (6, 249), (7, 289), (8, 270), (9, 216), (10, 278), (11, 282), (12, 302), (13, 60), (14, 305), (15, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120814) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 307) (RestInside.out (n := 307) f119 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 308) f119 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 309) (ρ' := [(0, 297), (1, 247), (2, 298), (3, 280), (4, 4), (5, 97), (6, 249), (7, 289), (8, 270), (9, 216), (10, 278), (11, 282), (12, 307), (13, 60), (14, 305), (15, 293), (16, 308), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120817) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_6 code

theorem rest_l12065f_4 [Bindings] (code : CodeMap) :
    Rest (n := 223) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 218), (1, 190), (2, 219), (3, 210), (4, 4), (5, 97), (6, 221), (7, 192), (8, 208), (9, 216), (10, 206), (11, 172), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]
      356 0x12077d bytes_l12065f_4 b_l12065f_4 := by
  have f80 : InstrSpec 0x12077d [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x12077d) (movR64R64Effect 0x12077d 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x12077d 11 0).toInstrSpec (mov_r64_r64_effect_step 0x12077d 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x120780 [0x48, 0x89, 0x6C, 0x24, 0x48] (StorePre 0x120780 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x120780 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120780 5 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120780 5 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x120780 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f82 : InstrSpec 0x120785 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x120785) (movR64R64Effect 0x120785 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120785 0 5).toInstrSpec (mov_r64_r64_effect_step 0x120785 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x120788 [0x49, 0xF7, 0xE5] (fun s => s.RIP = 0x120788) (mulR64Effect 0x120788 13)
      [.gpr 13, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120788 13).toInstrSpec (mul_r64_effect_step 0x120788 0x49 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x12078b [0x4C, 0x01, 0xD8] (fun s => s.RIP = 0x12078b) (addR64R64Effect 0x12078b 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12078b 0 11).toInstrSpec (add_r64_r64_effect_step 0x12078b 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x12078e [0x48, 0x11, 0xD6] (fun s => s.RIP = 0x12078e) (atFlags StatusFlags.CF (adcR64R64Effect 0x12078e 6 2))
      [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x12078e 6 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x12078e 0x48 0xd6 c (by decide) (by decide))) pre_rip
  have f86 : InstrSpec 0x120791 [0x48, 0x0F, 0xA4, 0xC6, 0x01] (fun s => s.RIP = 0x120791) (shldR64R64Effect 0x120791 5 6 0 1)
      [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x120791 5 6 0 1).toInstrSpec (shld_r64_r64_imm8_effect_step 0x120791 0x48 (by decide) 0xc6 (by decide) 0x1) pre_rip
  have f87 : InstrSpec 0x120796 [0x48, 0x01, 0xC0] (fun s => s.RIP = 0x120796) (addR64R64Effect 0x120796 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120796 0 0).toInstrSpec (add_r64_r64_effect_step 0x120796 0x48 0xc0 (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x120799 [0x48, 0x01, 0xF8] (fun s => s.RIP = 0x120799) (addR64R64Effect 0x120799 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120799 0 7).toInstrSpec (add_r64_r64_effect_step 0x120799 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x12079c [0x48, 0x11, 0xCE] (fun s => s.RIP = 0x12079c) (atFlags StatusFlags.CF (adcR64R64Effect 0x12079c 6 1))
      [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x12079c 6 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x12079c 0x48 0xce c (by decide) (by decide))) pre_rip
  have f90 : InstrSpec 0x12079f [0x48, 0x89, 0xF1] (fun s => s.RIP = 0x12079f) (movR64R64Effect 0x12079f 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12079f 1 6).toInstrSpec (mov_r64_r64_effect_step 0x12079f 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x1207a2 [0x48, 0xC1, 0xE9, 0x34] (fun s => s.RIP = 0x1207a2) (shrR64Effect 0x1207a2 4 1 52)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1207a2 4 1 52).toInstrSpec (shr_r64_imm8_effect_step 0x1207a2 0x48 0xe9 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x1207a6 [0x48, 0x0F, 0xA4, 0xC6, 0x0C] (fun s => s.RIP = 0x1207a6) (shldR64R64Effect 0x1207a6 5 6 0 12)
      [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1207a6 5 6 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1207a6 0x48 (by decide) 0xc6 (by decide) 0xc) pre_rip
  have f93 : InstrSpec 0x1207ab [0x48, 0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x1207ab) (shlR64Effect 0x1207ab 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x1207ab 4 0 4).toInstrSpec (shl_r64_imm8_effect_step 0x1207ab 0x48 0xe0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x1207af [0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00] (fun s => s.RIP = 0x1207af) (movR64Imm64Effect 0x1207af 2 0xfffffffffffff0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x1207af 2 0xfffffffffffff0).toInstrSpec (mov_r64_imm64_effect_step 0x1207af 0x48 0xba (by decide) (by decide) 0xfffffffffffff0) pre_rip
  have f95 : InstrSpec 0x1207b9 [0x48, 0x21, 0xD0] (fun s => s.RIP = 0x1207b9) (andR64R64Effect 0x1207b9 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1207b9 0 2).toInstrSpec (and_r64_r64_effect_step 0x1207b9 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f96 : InstrSpec 0x1207bc [0x48, 0x09, 0xD8] (fun s => s.RIP = 0x1207bc) (orR64R64Effect 0x1207bc 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1207bc 0 3).toInstrSpec (or_r64_r64_effect_step 0x1207bc 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f97 : InstrSpec 0x1207bf [0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1207bf) (movR64Imm64Effect 0x1207bf 2 0x1000003d1)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x1207bf 2 0x1000003d1).toInstrSpec (mov_r64_imm64_effect_step 0x1207bf 0x48 0xba (by decide) (by decide) 0x1000003d1) pre_rip
  have f98 : InstrSpec 0x1207c9 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x1207c9) (mulR64Effect 0x1207c9 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1207c9 2).toInstrSpec (mul_r64_effect_step 0x1207c9 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x1207cc [0x4C, 0x01, 0xD0] (fun s => s.RIP = 0x1207cc) (addR64R64Effect 0x1207cc 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1207cc 0 10).toInstrSpec (add_r64_r64_effect_step 0x1207cc 0x4c 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f80 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 218), (1, 190), (2, 219), (3, 210), (4, 4), (5, 97), (6, 221), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120780) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.exec (n := 225) (ρ' := [(0, 218), (1, 190), (2, 219), (3, 210), (4, 4), (5, 97), (6, 221), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120785) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 226) (RestInside.out (n := 226) f82 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 227) (ρ' := [(0, 226), (1, 190), (2, 219), (3, 210), (4, 4), (5, 97), (6, 221), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120788) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 228) (RestInside.out (n := 228) f83 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 229) f83 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 230) (ρ' := [(0, 228), (1, 190), (2, 229), (3, 210), (4, 4), (5, 97), (6, 221), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12078b) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.out (n := 231) f84 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 232) f84 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 233) (ρ' := [(0, 231), (1, 190), (2, 229), (3, 210), (4, 4), (5, 97), (6, 221), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (16, 232), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12078e) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f85 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 231), (1, 190), (2, 229), (3, 210), (4, 4), (5, 97), (6, 234), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120791) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f86 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 231), (1, 190), (2, 229), (3, 210), (4, 4), (5, 97), (6, 236), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120796) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f87 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 238), (1, 190), (2, 229), (3, 210), (4, 4), (5, 97), (6, 236), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120799) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f88 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 241) f88 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 242) (ρ' := [(0, 240), (1, 190), (2, 229), (3, 210), (4, 4), (5, 97), (6, 236), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (16, 241), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12079c) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 243) (RestInside.out (n := 243) f89 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 244) (ρ' := [(0, 240), (1, 190), (2, 229), (3, 210), (4, 4), (5, 97), (6, 243), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12079f) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.out (n := 245) f90 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 246) (ρ' := [(0, 240), (1, 245), (2, 229), (3, 210), (4, 4), (5, 97), (6, 243), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207a2) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f91 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 240), (1, 247), (2, 229), (3, 210), (4, 4), (5, 97), (6, 243), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207a6) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 249) (RestInside.out (n := 249) f92 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 250) (ρ' := [(0, 240), (1, 247), (2, 229), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207ab) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f93 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(0, 251), (1, 247), (2, 229), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207af) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f94 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 254) (ρ' := [(0, 251), (1, 247), (2, 253), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207b9) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 255) (RestInside.out (n := 255) f95 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 256) (ρ' := [(0, 255), (1, 247), (2, 253), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207bc) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f96 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 257), (1, 247), (2, 253), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207bf) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f97 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 257), (1, 247), (2, 259), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207c9) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.out (n := 261) f98 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 262) f98 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 263) (ρ' := [(0, 261), (1, 247), (2, 262), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207cc) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 264) (RestInside.out (n := 264) f99 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 265) f99 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 266) (ρ' := [(0, 264), (1, 247), (2, 262), (3, 210), (4, 4), (5, 97), (6, 249), (7, 192), (8, 208), (9, 216), (10, 206), (11, 223), (12, 212), (13, 60), (14, 203), (15, 161), (16, 265), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1207cf) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_5 code

theorem rest_l12065f_3 [Bindings] (code : CodeMap) :
    Rest (n := 182) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 177), (1, 120), (2, 159), (3, 168), (4, 4), (5, 97), (6, 124), (7, 180), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 152), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]
      376 0x120737 bytes_l12065f_3 b_l12065f_3 := by
  have f60 : InstrSpec 0x120737 [0x48, 0x01, 0xF0] (fun s => s.RIP = 0x120737) (addR64R64Effect 0x120737 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120737 0 6).toInstrSpec (add_r64_r64_effect_step 0x120737 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x12073a [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x12073a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x12073a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12073a 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12073a 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x12073a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f62 : InstrSpec 0x12073f [0x4C, 0x11, 0xFF] (fun s => s.RIP = 0x12073f) (atFlags StatusFlags.CF (adcR64R64Effect 0x12073f 7 15))
      [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 7, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x12073f 7 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x12073f 0x4c 0xff c (by decide) (by decide))) pre_rip
  have f63 : InstrSpec 0x120742 [0x48, 0x89, 0xF9] (fun s => s.RIP = 0x120742) (movR64R64Effect 0x120742 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x120742 1 7).toInstrSpec (mov_r64_r64_effect_step 0x120742 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x120745 [0x48, 0xC1, 0xE9, 0x34] (fun s => s.RIP = 0x120745) (shrR64Effect 0x120745 4 1 52)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x120745 4 1 52).toInstrSpec (shr_r64_imm8_effect_step 0x120745 0x48 0xe9 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x120749 [0x48, 0x0F, 0xA4, 0xC7, 0x0C] (fun s => s.RIP = 0x120749) (shldR64R64Effect 0x120749 5 7 0 12)
      [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x120749 5 7 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x120749 0x48 (by decide) 0xc7 (by decide) 0xc) pre_rip
  have f66 : InstrSpec 0x12074e [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x12074e) (movR64R64Effect 0x12074e 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x12074e 3 0).toInstrSpec (mov_r64_r64_effect_step 0x12074e 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x120751 [0x48, 0xC1, 0xEB, 0x30] (fun s => s.RIP = 0x120751) (shrR64Effect 0x120751 4 3 48)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x120751 4 3 48).toInstrSpec (shr_r64_imm8_effect_step 0x120751 0x48 0xeb 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x120755 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x120755) (movR64R64Effect 0x120755 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120755 0 12).toInstrSpec (mov_r64_r64_effect_step 0x120755 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x120758 [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x120758) (mulR64Effect 0x120758 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120758 12).toInstrSpec (mul_r64_effect_step 0x120758 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x12075b [0x4D, 0x89, 0xE6] (fun s => s.RIP = 0x12075b) (movR64R64Effect 0x12075b 14 12)
      [.gpr 12] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x12075b 14 12).toInstrSpec (mov_r64_r64_effect_step 0x12075b 0x4d 0xe6 (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x12075e [0x4C, 0x89, 0x64, 0x24, 0x50] (StorePre 0x12075e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x12075e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12075e 12 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12075e 12 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x12075e 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f72 : InstrSpec 0x120763 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x120763) (movR64R64Effect 0x120763 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x120763 10 0).toInstrSpec (mov_r64_r64_effect_step 0x120763 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x120766 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x120766) (movR64R64Effect 0x120766 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x120766 8 2).toInstrSpec (mov_r64_r64_effect_step 0x120766 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x120769 [0x83, 0xE3, 0x0F] (fun s => s.RIP = 0x120769) (andR32Imm8Effect 0x120769 3 3 0xf)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x120769 3 3 0xf).toInstrSpec (and_r32_imm8_effect_step 0x120769 0xe3 0xf (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x12076c [0x4D, 0x89, 0xCC] (fun s => s.RIP = 0x12076c) (movR64R64Effect 0x12076c 12 9)
      [.gpr 9] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x12076c 12 9).toInstrSpec (mov_r64_r64_effect_step 0x12076c 0x4d 0xcc (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x12076f [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x12076f) (movR64R64Effect 0x12076f 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12076f 0 9).toInstrSpec (mov_r64_r64_effect_step 0x12076f 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x120772 [0x4C, 0x8B, 0x4C, 0x24, 0x40] (LoadPre 0x120772 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x120772 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120772 9 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x120772 9 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x120772 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f78 : InstrSpec 0x120777 [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x120777) (mulR64Effect 0x120777 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120777 9).toInstrSpec (mul_r64_effect_step 0x120777 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x12077a [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x12077a) (movR64R64Effect 0x12077a 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12077a 6 2).toInstrSpec (mov_r64_r64_effect_step 0x12077a 0x48 0xd6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f60 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 183) f60 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 184) (ρ' := [(0, 182), (1, 120), (2, 159), (3, 168), (4, 4), (5, 97), (6, 124), (7, 180), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 152), (15, 161), (16, 183), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12073a) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.exec (n := 185) (ρ' := [(0, 182), (1, 120), (2, 159), (3, 168), (4, 4), (5, 97), (6, 124), (7, 180), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 152), (15, 161), (16, 183), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12073f) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 186) (RestInside.out (n := 186) f62 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 187) (ρ' := [(0, 182), (1, 120), (2, 159), (3, 168), (4, 4), (5, 97), (6, 124), (7, 186), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 152), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120742) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 188) (RestInside.out (n := 188) f63 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 189) (ρ' := [(0, 182), (1, 188), (2, 159), (3, 168), (4, 4), (5, 97), (6, 124), (7, 186), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 152), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120745) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 190) (RestInside.out (n := 190) f64 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 191) (ρ' := [(0, 182), (1, 190), (2, 159), (3, 168), (4, 4), (5, 97), (6, 124), (7, 186), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 152), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120749) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f65 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 193) (ρ' := [(0, 182), (1, 190), (2, 159), (3, 168), (4, 4), (5, 97), (6, 124), (7, 192), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 152), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12074e) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f66 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 195) (ρ' := [(0, 182), (1, 190), (2, 159), (3, 194), (4, 4), (5, 97), (6, 124), (7, 192), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 152), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120751) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.out (n := 196) f67 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 197) (ρ' := [(0, 182), (1, 190), (2, 159), (3, 196), (4, 4), (5, 97), (6, 124), (7, 192), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 152), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120755) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f68 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 198), (1, 190), (2, 159), (3, 196), (4, 4), (5, 97), (6, 124), (7, 192), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 152), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120758) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f69 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 201) f69 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 202) (ρ' := [(0, 200), (1, 190), (2, 201), (3, 196), (4, 4), (5, 97), (6, 124), (7, 192), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 152), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12075b) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f70 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 204) (ρ' := [(0, 200), (1, 190), (2, 201), (3, 196), (4, 4), (5, 97), (6, 124), (7, 192), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12075e) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 205) (RestInside.exec (n := 205) (ρ' := [(0, 200), (1, 190), (2, 201), (3, 196), (4, 4), (5, 97), (6, 124), (7, 192), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120763) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f72 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 200), (1, 190), (2, 201), (3, 196), (4, 4), (5, 97), (6, 124), (7, 192), (8, 132), (9, 154), (10, 206), (11, 172), (12, 58), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120766) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f73 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 200), (1, 190), (2, 201), (3, 196), (4, 4), (5, 97), (6, 124), (7, 192), (8, 208), (9, 154), (10, 206), (11, 172), (12, 58), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120769) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f74 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 200), (1, 190), (2, 201), (3, 210), (4, 4), (5, 97), (6, 124), (7, 192), (8, 208), (9, 154), (10, 206), (11, 172), (12, 58), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12076c) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f75 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 200), (1, 190), (2, 201), (3, 210), (4, 4), (5, 97), (6, 124), (7, 192), (8, 208), (9, 154), (10, 206), (11, 172), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12076f) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f76 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 214), (1, 190), (2, 201), (3, 210), (4, 4), (5, 97), (6, 124), (7, 192), (8, 208), (9, 154), (10, 206), (11, 172), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120772) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f77 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 214), (1, 190), (2, 201), (3, 210), (4, 4), (5, 97), (6, 124), (7, 192), (8, 208), (9, 216), (10, 206), (11, 172), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120777) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.out (n := 218) f78 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 219) f78 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 220) (ρ' := [(0, 218), (1, 190), (2, 219), (3, 210), (4, 4), (5, 97), (6, 124), (7, 192), (8, 208), (9, 216), (10, 206), (11, 172), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12077a) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f79 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 218), (1, 190), (2, 219), (3, 210), (4, 4), (5, 97), (6, 221), (7, 192), (8, 208), (9, 216), (10, 206), (11, 172), (12, 212), (13, 60), (14, 203), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12077d) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_4 code

theorem rest_l12065f_2 [Bindings] (code : CodeMap) :
    Rest (n := 136) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 129), (1, 120), (2, 130), (3, 3), (4, 4), (5, 97), (6, 124), (7, 112), (8, 132), (10, 134), (11, 107), (12, 58), (13, 60), (14, 66), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]
      396 0x1206f6 bytes_l12065f_2 b_l12065f_2 := by
  have f40 : InstrSpec 0x1206f6 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x1206f6) (movR64R64Effect 0x1206f6 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1206f6 0 1).toInstrSpec (mov_r64_r64_effect_step 0x1206f6 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x1206f9 [0x49, 0xF7, 0xE3] (fun s => s.RIP = 0x1206f9) (mulR64Effect 0x1206f9 11)
      [.gpr 11, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1206f9 11).toInstrSpec (mul_r64_effect_step 0x1206f9 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x1206fc [0x48, 0x89, 0xD7] (fun s => s.RIP = 0x1206fc) (movR64R64Effect 0x1206fc 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1206fc 7 2).toInstrSpec (mov_r64_r64_effect_step 0x1206fc 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x1206ff [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x1206ff) (movR64R64Effect 0x1206ff 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1206ff 11 0).toInstrSpec (mov_r64_r64_effect_step 0x1206ff 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x120702 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x120702) (movR64R64Effect 0x120702 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120702 0 5).toInstrSpec (mov_r64_r64_effect_step 0x120702 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x120705 [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x120705) (mulR64Effect 0x120705 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120705 12).toInstrSpec (mul_r64_effect_step 0x120705 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x120708 [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x120708) (movR64R64Effect 0x120708 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x120708 3 2).toInstrSpec (mov_r64_r64_effect_step 0x120708 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x12070b [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x12070b) (movR64R64Effect 0x12070b 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x12070b 14 0).toInstrSpec (mov_r64_r64_effect_step 0x12070b 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x12070e [0x4C, 0x8B, 0x4C, 0x24, 0x30] (LoadPre 0x12070e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x12070e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12070e 9 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x12070e 9 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x12070e 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f49 : InstrSpec 0x120713 [0x4C, 0x89, 0xC8] (fun s => s.RIP = 0x120713) (movR64R64Effect 0x120713 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120713 0 9).toInstrSpec (mov_r64_r64_effect_step 0x120713 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x120716 [0x49, 0xF7, 0xE5] (fun s => s.RIP = 0x120716) (mulR64Effect 0x120716 13)
      [.gpr 13, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120716 13).toInstrSpec (mul_r64_effect_step 0x120716 0x49 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x120719 [0x49, 0xC1, 0xEF, 0x34] (fun s => s.RIP = 0x120719) (shrR64Effect 0x120719 4 15 52)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x120719 4 15 52).toInstrSpec (shr_r64_imm8_effect_step 0x120719 0x49 0xef 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x12071d [0x4C, 0x01, 0xF0] (fun s => s.RIP = 0x12071d) (addR64R64Effect 0x12071d 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12071d 0 14).toInstrSpec (add_r64_r64_effect_step 0x12071d 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x120720 [0x48, 0x11, 0xD3] (fun s => s.RIP = 0x120720) (atFlags StatusFlags.CF (adcR64R64Effect 0x120720 3 2))
      [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120720 3 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120720 0x48 0xd3 c (by decide) (by decide))) pre_rip
  have f54 : InstrSpec 0x120723 [0x48, 0x0F, 0xA4, 0xC3, 0x01] (fun s => s.RIP = 0x120723) (shldR64R64Effect 0x120723 5 3 0 1)
      [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x120723 5 3 0 1).toInstrSpec (shld_r64_r64_imm8_effect_step 0x120723 0x48 (by decide) 0xc3 (by decide) 0x1) pre_rip
  have f55 : InstrSpec 0x120728 [0x48, 0x01, 0xC0] (fun s => s.RIP = 0x120728) (addR64R64Effect 0x120728 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120728 0 0).toInstrSpec (add_r64_r64_effect_step 0x120728 0x48 0xc0 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x12072b [0x4D, 0x01, 0xD3] (fun s => s.RIP = 0x12072b) (addR64R64Effect 0x12072b 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12072b 11 10).toInstrSpec (add_r64_r64_effect_step 0x12072b 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x12072e [0x4C, 0x11, 0xC7] (fun s => s.RIP = 0x12072e) (atFlags StatusFlags.CF (adcR64R64Effect 0x12072e 7 8))
      [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 7, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x12072e 7 8).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x12072e 0x4c 0xc7 c (by decide) (by decide))) pre_rip
  have f58 : InstrSpec 0x120731 [0x4C, 0x01, 0xD8] (fun s => s.RIP = 0x120731) (addR64R64Effect 0x120731 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120731 0 11).toInstrSpec (add_r64_r64_effect_step 0x120731 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x120734 [0x48, 0x11, 0xDF] (fun s => s.RIP = 0x120734) (atFlags StatusFlags.CF (adcR64R64Effect 0x120734 7 3))
      [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 7, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120734 7 3).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120734 0x48 0xdf c (by decide) (by decide))) pre_rip
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f40 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 136), (1, 120), (2, 130), (3, 3), (4, 4), (5, 97), (6, 124), (7, 112), (8, 132), (10, 134), (11, 107), (12, 58), (13, 60), (14, 66), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206f9) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f41 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 139) f41 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 140) (ρ' := [(0, 138), (1, 120), (2, 139), (3, 3), (4, 4), (5, 97), (6, 124), (7, 112), (8, 132), (10, 134), (11, 107), (12, 58), (13, 60), (14, 66), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206fc) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f42 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 138), (1, 120), (2, 139), (3, 3), (4, 4), (5, 97), (6, 124), (7, 141), (8, 132), (10, 134), (11, 107), (12, 58), (13, 60), (14, 66), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206ff) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f43 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 138), (1, 120), (2, 139), (3, 3), (4, 4), (5, 97), (6, 124), (7, 141), (8, 132), (10, 134), (11, 143), (12, 58), (13, 60), (14, 66), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120702) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f44 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 145), (1, 120), (2, 139), (3, 3), (4, 4), (5, 97), (6, 124), (7, 141), (8, 132), (10, 134), (11, 143), (12, 58), (13, 60), (14, 66), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120705) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f45 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 148) f45 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 149) (ρ' := [(0, 147), (1, 120), (2, 148), (3, 3), (4, 4), (5, 97), (6, 124), (7, 141), (8, 132), (10, 134), (11, 143), (12, 58), (13, 60), (14, 66), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120708) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f46 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 147), (1, 120), (2, 148), (3, 150), (4, 4), (5, 97), (6, 124), (7, 141), (8, 132), (10, 134), (11, 143), (12, 58), (13, 60), (14, 66), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12070b) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f47 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 147), (1, 120), (2, 148), (3, 150), (4, 4), (5, 97), (6, 124), (7, 141), (8, 132), (10, 134), (11, 143), (12, 58), (13, 60), (14, 152), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12070e) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f48 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 147), (1, 120), (2, 148), (3, 150), (4, 4), (5, 97), (6, 124), (7, 141), (8, 132), (9, 154), (10, 134), (11, 143), (12, 58), (13, 60), (14, 152), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120713) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f49 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 156), (1, 120), (2, 148), (3, 150), (4, 4), (5, 97), (6, 124), (7, 141), (8, 132), (9, 154), (10, 134), (11, 143), (12, 58), (13, 60), (14, 152), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120716) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f50 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 159) f50 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 160) (ρ' := [(0, 158), (1, 120), (2, 159), (3, 150), (4, 4), (5, 97), (6, 124), (7, 141), (8, 132), (9, 154), (10, 134), (11, 143), (12, 58), (13, 60), (14, 152), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120719) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f51 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 158), (1, 120), (2, 159), (3, 150), (4, 4), (5, 97), (6, 124), (7, 141), (8, 132), (9, 154), (10, 134), (11, 143), (12, 58), (13, 60), (14, 152), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12071d) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f52 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 164) f52 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 165) (ρ' := [(0, 163), (1, 120), (2, 159), (3, 150), (4, 4), (5, 97), (6, 124), (7, 141), (8, 132), (9, 154), (10, 134), (11, 143), (12, 58), (13, 60), (14, 152), (15, 161), (16, 164), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120720) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f53 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 163), (1, 120), (2, 159), (3, 166), (4, 4), (5, 97), (6, 124), (7, 141), (8, 132), (9, 154), (10, 134), (11, 143), (12, 58), (13, 60), (14, 152), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120723) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f54 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 163), (1, 120), (2, 159), (3, 168), (4, 4), (5, 97), (6, 124), (7, 141), (8, 132), (9, 154), (10, 134), (11, 143), (12, 58), (13, 60), (14, 152), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120728) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f55 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 170), (1, 120), (2, 159), (3, 168), (4, 4), (5, 97), (6, 124), (7, 141), (8, 132), (9, 154), (10, 134), (11, 143), (12, 58), (13, 60), (14, 152), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12072b) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f56 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 173) f56 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 174) (ρ' := [(0, 170), (1, 120), (2, 159), (3, 168), (4, 4), (5, 97), (6, 124), (7, 141), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 152), (15, 161), (16, 173), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12072e) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f57 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 170), (1, 120), (2, 159), (3, 168), (4, 4), (5, 97), (6, 124), (7, 175), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 152), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120731) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f58 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 178) f58 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 179) (ρ' := [(0, 177), (1, 120), (2, 159), (3, 168), (4, 4), (5, 97), (6, 124), (7, 175), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 152), (15, 161), (16, 178), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120734) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f59 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 177), (1, 120), (2, 159), (3, 168), (4, 4), (5, 97), (6, 124), (7, 180), (8, 132), (9, 154), (10, 134), (11, 172), (12, 58), (13, 60), (14, 152), (15, 161), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120737) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_3 code

theorem rest_l12065f_1 [Bindings] (code : CodeMap) :
    Rest (n := 94) code lifted (codeRange 0x12065f bytes_l12065f) [(0, 92), (1, 76), (2, 81), (3, 3), (4, 4), (5, 5), (6, 90), (7, 85), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]
      416 0x1206a4 bytes_l12065f_1 b_l12065f_1 := by
  have f20 : InstrSpec 0x1206a4 [0x49, 0xF7, 0xE7] (fun s => s.RIP = 0x1206a4) (mulR64Effect 0x1206a4 15)
      [.gpr 15, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1206a4 15).toInstrSpec (mul_r64_effect_step 0x1206a4 0x49 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1206a7 [0x4C, 0x89, 0xFD] (fun s => s.RIP = 0x1206a7) (movR64R64Effect 0x1206a7 5 15)
      [.gpr 15] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1206a7 5 15).toInstrSpec (mov_r64_r64_effect_step 0x1206a7 0x4c 0xfd (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x1206aa [0x49, 0x89, 0xC0] (fun s => s.RIP = 0x1206aa) (movR64R64Effect 0x1206aa 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1206aa 8 0).toInstrSpec (mov_r64_r64_effect_step 0x1206aa 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x1206ad [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x1206ad) (movR64R64Effect 0x1206ad 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1206ad 1 2).toInstrSpec (mov_r64_r64_effect_step 0x1206ad 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x1206b0 [0x48, 0xB8, 0xFD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] (fun s => s.RIP = 0x1206b0) (movR64Imm64Effect 0x1206b0 0 0xffffffffffffd)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1206b0 0 0xffffffffffffd).toInstrSpec (mov_r64_imm64_effect_step 0x1206b0 0x48 0xb8 (by decide) (by decide) 0xffffffffffffd) pre_rip
  have f25 : InstrSpec 0x1206ba [0x4C, 0x21, 0xC0] (fun s => s.RIP = 0x1206ba) (andR64R64Effect 0x1206ba 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1206ba 0 8).toInstrSpec (and_r64_r64_effect_step 0x1206ba 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x1206bd [0x49, 0xBB, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1206bd) (movR64Imm64Effect 0x1206bd 11 0x1000003d10)
      [] [] [.reg 11, .rip] :=
    (movR64Imm64Effect_footprint 0x1206bd 11 0x1000003d10).toInstrSpec (mov_r64_imm64_effect_step 0x1206bd 0x49 0xbb (by decide) (by decide) 0x1000003d10) pre_rip
  have f27 : InstrSpec 0x1206c7 [0x49, 0xF7, 0xE3] (fun s => s.RIP = 0x1206c7) (mulR64Effect 0x1206c7 11)
      [.gpr 11, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1206c7 11).toInstrSpec (mul_r64_effect_step 0x1206c7 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x1206ca [0x48, 0x01, 0xFF] (fun s => s.RIP = 0x1206ca) (addR64R64Effect 0x1206ca 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1206ca 7 7).toInstrSpec (add_r64_r64_effect_step 0x1206ca 0x48 0xff (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x1206cd [0x48, 0x01, 0xF8] (fun s => s.RIP = 0x1206cd) (addR64R64Effect 0x1206cd 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1206cd 0 7).toInstrSpec (add_r64_r64_effect_step 0x1206cd 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x1206d0 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x1206d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1206d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1206d0 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1206d0 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1206d0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x1206d5 [0x48, 0x11, 0xD6] (fun s => s.RIP = 0x1206d5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1206d5 6 2))
      [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x1206d5 6 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x1206d5 0x48 0xd6 c (by decide) (by decide))) pre_rip
  have f32 : InstrSpec 0x1206d8 [0x4C, 0x0F, 0xA4, 0xC1, 0x0C] (fun s => s.RIP = 0x1206d8) (shldR64R64Effect 0x1206d8 5 1 8 12)
      [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1206d8 5 1 8 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1206d8 0x4c (by decide) 0xc1 (by decide) 0xc) pre_rip
  have f33 : InstrSpec 0x1206dd [0x49, 0x89, 0xF7] (fun s => s.RIP = 0x1206dd) (movR64R64Effect 0x1206dd 15 6)
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1206dd 15 6).toInstrSpec (mov_r64_r64_effect_step 0x1206dd 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x1206e0 [0x48, 0x0F, 0xA4, 0xC6, 0x0C] (fun s => s.RIP = 0x1206e0) (shldR64R64Effect 0x1206e0 5 6 0 12)
      [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x1206e0 5 6 0 12).toInstrSpec (shld_r64_r64_imm8_effect_step 0x1206e0 0x48 (by decide) 0xc6 (by decide) 0xc) pre_rip
  have f35 : InstrSpec 0x1206e5 [0x4C, 0x89, 0x74, 0x24, 0x40] (StorePre 0x1206e5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1206e5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1206e5 14 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1206e5 14 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1206e5 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x1206ea [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x1206ea) (movR64R64Effect 0x1206ea 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1206ea 0 14).toInstrSpec (mov_r64_r64_effect_step 0x1206ea 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x1206ed [0x49, 0xF7, 0xE6] (fun s => s.RIP = 0x1206ed) (mulR64Effect 0x1206ed 14)
      [.gpr 14, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1206ed 14).toInstrSpec (mul_r64_effect_step 0x1206ed 0x49 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x1206f0 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x1206f0) (movR64R64Effect 0x1206f0 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1206f0 8 2).toInstrSpec (mov_r64_r64_effect_step 0x1206f0 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x1206f3 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x1206f3) (movR64R64Effect 0x1206f3 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1206f3 10 0).toInstrSpec (mov_r64_r64_effect_step 0x1206f3 0x49 0xc2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 95) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 96) (ρ' := [(0, 94), (1, 76), (2, 95), (3, 3), (4, 4), (5, 5), (6, 90), (7, 85), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206a7) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f21 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 94), (1, 76), (2, 95), (3, 3), (4, 4), (5, 97), (6, 90), (7, 85), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206aa) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f22 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 94), (1, 76), (2, 95), (3, 3), (4, 4), (5, 97), (6, 90), (7, 85), (8, 99), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206ad) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 94), (1, 101), (2, 95), (3, 3), (4, 4), (5, 97), (6, 90), (7, 85), (8, 99), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206b0) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 103), (1, 101), (2, 95), (3, 3), (4, 4), (5, 97), (6, 90), (7, 85), (8, 99), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206ba) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 105), (1, 101), (2, 95), (3, 3), (4, 4), (5, 97), (6, 90), (7, 85), (8, 99), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206bd) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f26 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 105), (1, 101), (2, 95), (3, 3), (4, 4), (5, 97), (6, 90), (7, 85), (8, 99), (11, 107), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206c7) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 110) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 111) (ρ' := [(0, 109), (1, 101), (2, 110), (3, 3), (4, 4), (5, 97), (6, 90), (7, 85), (8, 99), (11, 107), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206ca) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f28 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 109), (1, 101), (2, 110), (3, 3), (4, 4), (5, 97), (6, 90), (7, 112), (8, 99), (11, 107), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206cd) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 115) f29 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 116) (ρ' := [(0, 114), (1, 101), (2, 110), (3, 3), (4, 4), (5, 97), (6, 90), (7, 112), (8, 99), (11, 107), (12, 58), (13, 60), (14, 66), (15, 62), (16, 115), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206d0) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.exec (n := 117) (ρ' := [(0, 114), (1, 101), (2, 110), (3, 3), (4, 4), (5, 97), (6, 90), (7, 112), (8, 99), (11, 107), (12, 58), (13, 60), (14, 66), (15, 62), (16, 115), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206d5) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f31 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 114), (1, 101), (2, 110), (3, 3), (4, 4), (5, 97), (6, 118), (7, 112), (8, 99), (11, 107), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206d8) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 114), (1, 120), (2, 110), (3, 3), (4, 4), (5, 97), (6, 118), (7, 112), (8, 99), (11, 107), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206dd) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f33 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 114), (1, 120), (2, 110), (3, 3), (4, 4), (5, 97), (6, 118), (7, 112), (8, 99), (11, 107), (12, 58), (13, 60), (14, 66), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206e0) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f34 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 114), (1, 120), (2, 110), (3, 3), (4, 4), (5, 97), (6, 124), (7, 112), (8, 99), (11, 107), (12, 58), (13, 60), (14, 66), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206e5) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.exec (n := 126) (ρ' := [(0, 114), (1, 120), (2, 110), (3, 3), (4, 4), (5, 97), (6, 124), (7, 112), (8, 99), (11, 107), (12, 58), (13, 60), (14, 66), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206ea) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f36 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 127), (1, 120), (2, 110), (3, 3), (4, 4), (5, 97), (6, 124), (7, 112), (8, 99), (11, 107), (12, 58), (13, 60), (14, 66), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206ed) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f37 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 130) f37 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 131) (ρ' := [(0, 129), (1, 120), (2, 130), (3, 3), (4, 4), (5, 97), (6, 124), (7, 112), (8, 99), (11, 107), (12, 58), (13, 60), (14, 66), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206f0) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f38 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 129), (1, 120), (2, 130), (3, 3), (4, 4), (5, 97), (6, 124), (7, 112), (8, 132), (11, 107), (12, 58), (13, 60), (14, 66), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206f3) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f39 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 129), (1, 120), (2, 130), (3, 3), (4, 4), (5, 97), (6, 124), (7, 112), (8, 132), (10, 134), (11, 107), (12, 58), (13, 60), (14, 66), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206f6) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_2 code

theorem rest_l12065f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12065f bytes_l12065f) (entryMap (live .l12065f))
      436 0x12065f bytes_l12065f b_l12065f := by
  have f0 : InstrSpec 0x12065f [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x12065f) (movzxR32R8Effect 0x12065f 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x12065f 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x12065f 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x120662 [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x120662 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x120662 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120662 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120662 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x120662 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12066a [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x12066a) (negR64Effect 0x12066a 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x12066a 0).toInstrSpec (neg_r64_effect_step 0x12066a 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12066d [0x49, 0x21, 0xC4] (fun s => s.RIP = 0x12066d) (andR64R64Effect 0x12066d 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x12066d 12 0).toInstrSpec (and_r64_r64_effect_step 0x12066d 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x120670 [0x49, 0x21, 0xC5] (fun s => s.RIP = 0x120670) (andR64R64Effect 0x120670 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120670 13 0).toInstrSpec (and_r64_r64_effect_step 0x120670 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x120673 [0x49, 0x21, 0xC7] (fun s => s.RIP = 0x120673) (andR64R64Effect 0x120673 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120673 15 0).toInstrSpec (and_r64_r64_effect_step 0x120673 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x120676 [0x48, 0x21, 0xE8] (fun s => s.RIP = 0x120676) (andR64R64Effect 0x120676 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120676 0 5).toInstrSpec (and_r64_r64_effect_step 0x120676 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x120679 [0x49, 0x21, 0xC6] (fun s => s.RIP = 0x120679) (andR64R64Effect 0x120679 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120679 14 0).toInstrSpec (and_r64_r64_effect_step 0x120679 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12067c [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x12067c) (andR64R64Effect 0x12067c 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x12067c 0 3).toInstrSpec (and_r64_r64_effect_step 0x12067c 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x12067f [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x12067f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x12067f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12067f 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12067f 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x12067f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x120684 [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x120684) (mulR64Effect 0x120684 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120684 12).toInstrSpec (mul_r64_effect_step 0x120684 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x120687 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x120687) (movR64R64Effect 0x120687 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x120687 6 2).toInstrSpec (mov_r64_r64_effect_step 0x120687 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x12068a [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x12068a) (movR64R64Effect 0x12068a 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12068a 1 0).toInstrSpec (mov_r64_r64_effect_step 0x12068a 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x12068d [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x12068d) (movR64R64Effect 0x12068d 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12068d 0 14).toInstrSpec (mov_r64_r64_effect_step 0x12068d 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x120690 [0x49, 0xF7, 0xE5] (fun s => s.RIP = 0x120690) (mulR64Effect 0x120690 13)
      [.gpr 13, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x120690 13).toInstrSpec (mul_r64_effect_step 0x120690 0x49 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x120693 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x120693) (movR64R64Effect 0x120693 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x120693 7 0).toInstrSpec (mov_r64_r64_effect_step 0x120693 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x120696 [0x48, 0x01, 0xCF] (fun s => s.RIP = 0x120696) (addR64R64Effect 0x120696 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x120696 7 1).toInstrSpec (add_r64_r64_effect_step 0x120696 0x48 0xcf (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x120699 [0x48, 0x11, 0xD6] (fun s => s.RIP = 0x120699) (atFlags StatusFlags.CF (adcR64R64Effect 0x120699 6 2))
      [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x120699 6 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x120699 0x48 0xd6 c (by decide) (by decide))) pre_rip
  have f18 : InstrSpec 0x12069c [0x48, 0x0F, 0xA4, 0xFE, 0x01] (fun s => s.RIP = 0x12069c) (shldR64R64Effect 0x12069c 5 6 7 1)
      [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shldR64R64Effect_footprint 0x12069c 5 6 7 1).toInstrSpec (shld_r64_r64_imm8_effect_step 0x12069c 0x48 (by decide) 0xfe (by decide) 0x1) pre_rip
  have f19 : InstrSpec 0x1206a1 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x1206a1) (movR64R64Effect 0x1206a1 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1206a1 0 15).toInstrSpec (mov_r64_r64_effect_step 0x1206a1 0x4c 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120662) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12066a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12066d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 58), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120670) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 58), (13, 60), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120673) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 58), (13, 60), (14, 14), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120676) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (12, 58), (13, 60), (14, 14), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120679) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12067c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12067f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120684) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 71), (2, 72), (3, 3), (4, 4), (5, 5), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120687) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 71), (2, 72), (3, 3), (4, 4), (5, 5), (6, 74), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12068a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 71), (1, 76), (2, 72), (3, 3), (4, 4), (5, 5), (6, 74), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12068d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 76), (2, 72), (3, 3), (4, 4), (5, 5), (6, 74), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120690) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 81) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 76), (2, 81), (3, 3), (4, 4), (5, 5), (6, 74), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120693) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 80), (1, 76), (2, 81), (3, 3), (4, 4), (5, 5), (6, 74), (7, 83), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120696) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f16 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 80), (1, 76), (2, 81), (3, 3), (4, 4), (5, 5), (6, 74), (7, 85), (12, 58), (13, 60), (14, 66), (15, 62), (16, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120699) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 80), (1, 76), (2, 81), (3, 3), (4, 4), (5, 5), (6, 88), (7, 85), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12069c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 80), (1, 76), (2, 81), (3, 3), (4, 4), (5, 5), (6, 90), (7, 85), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206a1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 92), (1, 76), (2, 81), (3, 3), (4, 4), (5, 5), (6, 90), (7, 85), (12, 58), (13, 60), (14, 66), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1206a4) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12065f_1 code

theorem block_l12065f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12065f :=
  Rest.liftedBlock (rest_l12065f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12065f x hx)

theorem rest_l120d03 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120d03 bytes_l120d03) (entryMap (live .l120d03))
      20 0x120d03 bytes_l120d03 b_l120d03 := by
  have f0 : InstrSpec 0x120d03 [0x0F, 0xB6, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00] (LoadPre 0x120d03 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x120d03 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x120d03 8 0 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x120d03 8 0 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (movzx_r32_m8_effect_step 0x120d03 0 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x120d0b [0x88, 0x44, 0x24, 0x20] (StorePre 0x120d0b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x120d0b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x120d0b 4 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x120d0b 4 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m8_r8_effect_step 0x120d0b 0 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x120d0f [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x120d0f) (negR64Effect 0x120d0f 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x120d0f 0).toInstrSpec (neg_r64_effect_step 0x120d0f 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x120d12 [0x48, 0x8B, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00] (LoadPre 0x120d12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x120d12 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120d12 1 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120d12 1 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_r64_m64_effect_step 0x120d12 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x120d1a [0x48, 0x21, 0xC1] (fun s => s.RIP = 0x120d1a) (andR64R64Effect 0x120d1a 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120d1a 1 0).toInstrSpec (and_r64_r64_effect_step 0x120d1a 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x120d1d [0x48, 0x8B, 0x94, 0x24, 0x38, 0x01, 0x00, 0x00] (LoadPre 0x120d1d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x120d1d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120d1d 2 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x120d1d 2 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_r64_m64_effect_step 0x120d1d 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x120d25 [0x48, 0x21, 0xC2] (fun s => s.RIP = 0x120d25) (andR64R64Effect 0x120d25 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120d25 2 0).toInstrSpec (and_r64_r64_effect_step 0x120d25 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x120d28 [0x48, 0x8B, 0xB4, 0x24, 0x40, 0x01, 0x00, 0x00] (LoadPre 0x120d28 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x120d28 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120d28 6 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x120d28 6 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_r64_m64_effect_step 0x120d28 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x120d30 [0x48, 0x21, 0xC6] (fun s => s.RIP = 0x120d30) (andR64R64Effect 0x120d30 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120d30 6 0).toInstrSpec (and_r64_r64_effect_step 0x120d30 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x120d33 [0x48, 0x8B, 0xBC, 0x24, 0x48, 0x01, 0x00, 0x00] (LoadPre 0x120d33 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x120d33 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120d33 7 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x120d33 7 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (mov_r64_m64_effect_step 0x120d33 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x120d3b [0x48, 0x21, 0xC7] (fun s => s.RIP = 0x120d3b) (andR64R64Effect 0x120d3b 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120d3b 7 0).toInstrSpec (and_r64_r64_effect_step 0x120d3b 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x120d3e [0x48, 0x23, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00] (LoadPre 0x120d3e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x120d3e + BitVec.ofNat 64 8)) 8) (andR64M64Effect 0x120d3e 0 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (andR64M64Effect_footprint 0x120d3e 0 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (and_r64_m64_effect_step 0x120d3e 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x120d46 [0x48, 0x89, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x120d46 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x120d46 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120d46 1 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120d46 1 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x120d46 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x120d4e [0x48, 0x89, 0x94, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x120d4e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x120d4e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120d4e 2 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120d4e 2 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x120d4e 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x120d56 [0x48, 0x89, 0xB4, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x120d56 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x120d56 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120d56 6 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120d56 6 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x120d56 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x120d5e [0x48, 0x89, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x120d5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x120d5e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120d5e 7 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120d5e 7 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x120d5e 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x120d66 [0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x120d66 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x120d66 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120d66 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120d66 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x120d66 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x120d6e [0x48, 0x8D, 0xBC, 0x24, 0xE0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x120d6e) (leaR64Effect 0x120d6e 7 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x120d6e 7 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (lea_r64_effect_step 0x120d6e 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x120d76 [0x48, 0x8D, 0xB4, 0x24, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x120d76) (leaR64Effect 0x120d76 6 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x120d76 6 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (lea_r64_effect_step 0x120d76 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x120d7e [0xE8, 0xAD, 0x3B, 0xFF, 0xFF] (PushPre 0x120d7e 5) (callEffect (fun _ => 0x114930) 0x120d83)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x120d7e 0x114930 0x120d83).toInstrSpec (call_rel32_effect_step 0x120d7e 0xffff3bad (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d0b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d0f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d12) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 58), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d1a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 56), (1, 60), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d1d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 56), (1, 60), (2, 62), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d25) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 56), (1, 60), (2, 64), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d28) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 56), (1, 60), (2, 64), (3, 3), (4, 4), (5, 5), (6, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d30) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 56), (1, 60), (2, 64), (3, 3), (4, 4), (5, 5), (6, 68), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d33) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 56), (1, 60), (2, 64), (3, 3), (4, 4), (5, 5), (6, 68), (7, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d3b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 56), (1, 60), (2, 64), (3, 3), (4, 4), (5, 5), (6, 68), (7, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d3e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 60), (2, 64), (3, 3), (4, 4), (5, 5), (6, 68), (7, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d46) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (1, 60), (2, 64), (3, 3), (4, 4), (5, 5), (6, 68), (7, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d4e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 74), (1, 60), (2, 64), (3, 3), (4, 4), (5, 5), (6, 68), (7, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d56) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 74), (1, 60), (2, 64), (3, 3), (4, 4), (5, 5), (6, 68), (7, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d5e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 74), (1, 60), (2, 64), (3, 3), (4, 4), (5, 5), (6, 68), (7, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d66) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 74), (1, 60), (2, 64), (3, 3), (4, 4), (5, 5), (6, 68), (7, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d6e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 74), (1, 60), (2, 64), (3, 3), (4, 4), (5, 5), (6, 68), (7, 81), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d76) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 74), (1, 60), (2, 64), (3, 3), (4, 4), (5, 5), (6, 83), (7, 81), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d7e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 74), (1, 60), (2, 64), (3, 3), (4, 85), (5, 5), (6, 83), (7, 81), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114930) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 87) (by decide) (by decide) rfl rfl

theorem block_l120d03 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120d03 :=
  Rest.liftedBlock (rest_l120d03 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120d03 x hx)

theorem rest_l120d83_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x120d83 bytes_l120d83) [(0, 87), (1, 1), (2, 2), (3, 78), (4, 4), (5, 80), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 76), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]
      3 0x120df5 bytes_l120d83_1 b_l120d83_1 := by
  have f20 : InstrSpec 0x120df5 [0x24, 0x01] (fun s => s.RIP = 0x120df5) (andAlImm8Effect 0x120df5 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x120df5 0x1).toInstrSpec (and_al_imm8_effect_step 0x120df5 0x1) pre_rip
  have f21 : InstrSpec 0x120df7 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x120df7) (movzxR32R8Effect 0x120df7 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x120df7 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x120df7 0xf8 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x120dfa [0xE8, 0x51, 0x6F, 0x00, 0x00] (PushPre 0x120dfa 5) (callEffect (fun _ => 0x127d50) 0x120dff)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x120dfa 0x127d50 0x120dff).toInstrSpec (call_rel32_effect_step 0x120dfa 0x6f51 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 89), (1, 1), (2, 2), (3, 78), (4, 4), (5, 80), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 76), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120df7) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f21 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 89), (1, 1), (2, 2), (3, 78), (4, 4), (5, 80), (6, 6), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 76), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120dfa) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f22 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 89), (1, 1), (2, 2), (3, 78), (4, 93), (5, 80), (6, 6), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 76), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f22 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 95) (by decide) (by decide) rfl rfl

theorem rest_l120d83 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120d83 bytes_l120d83) (entryMap (live .l120d83))
      23 0x120d83 bytes_l120d83 b_l120d83 := by
  have f0 : InstrSpec 0x120d83 [0x4C, 0x8B, 0xB4, 0x24, 0xE0, 0x00, 0x00, 0x00] (LoadPre 0x120d83 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x120d83 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120d83 14 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x120d83 14 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_r64_m64_effect_step 0x120d83 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x120d8b [0x4C, 0x8B, 0xBC, 0x24, 0xE8, 0x00, 0x00, 0x00] (LoadPre 0x120d8b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x120d8b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120d8b 15 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x120d8b 15 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_r64_m64_effect_step 0x120d8b 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x120d93 [0x48, 0xB8, 0xBC, 0xF0, 0xFF, 0xFF, 0xFB, 0xFF, 0x3F, 0x00] (fun s => s.RIP = 0x120d93) (movR64Imm64Effect 0x120d93 0 0x3ffffbfffff0bc)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x120d93 0 0x3ffffbfffff0bc).toInstrSpec (mov_r64_imm64_effect_step 0x120d93 0x48 0xb8 (by decide) (by decide) 0x3ffffbfffff0bc) pre_rip
  have f3 : InstrSpec 0x120d9d [0x4C, 0x29, 0xF0] (fun s => s.RIP = 0x120d9d) (subR64R64Effect 0x120d9d 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x120d9d 0 14).toInstrSpec (sub_r64_r64_effect_step 0x120d9d 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x120da0 [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x120da0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x120da0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120da0 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120da0 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x120da0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x120da5 [0x48, 0xBB, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00] (fun s => s.RIP = 0x120da5) (movR64Imm64Effect 0x120da5 3 0x3ffffffffffffc)
      [] [] [.reg 3, .rip] :=
    (movR64Imm64Effect_footprint 0x120da5 3 0x3ffffffffffffc).toInstrSpec (mov_r64_imm64_effect_step 0x120da5 0x48 0xbb (by decide) (by decide) 0x3ffffffffffffc) pre_rip
  have f6 : InstrSpec 0x120daf [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x120daf) (movR64R64Effect 0x120daf 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120daf 0 3).toInstrSpec (mov_r64_r64_effect_step 0x120daf 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x120db2 [0x4C, 0x29, 0xF8] (fun s => s.RIP = 0x120db2) (subR64R64Effect 0x120db2 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x120db2 0 15).toInstrSpec (sub_r64_r64_effect_step 0x120db2 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x120db5 [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x120db5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x120db5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120db5 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120db5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x120db5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x120dba [0x4C, 0x8B, 0xA4, 0x24, 0xF0, 0x00, 0x00, 0x00] (LoadPre 0x120dba (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x120dba + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120dba 12 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x120dba 12 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x120dba 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x120dc2 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x120dc2) (movR64R64Effect 0x120dc2 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120dc2 0 3).toInstrSpec (mov_r64_r64_effect_step 0x120dc2 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x120dc5 [0x4C, 0x29, 0xE0] (fun s => s.RIP = 0x120dc5) (subR64R64Effect 0x120dc5 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x120dc5 0 12).toInstrSpec (sub_r64_r64_effect_step 0x120dc5 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x120dc8 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x120dc8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120dc8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120dc8 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120dc8 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x120dc8 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x120dcd [0x4C, 0x8B, 0xAC, 0x24, 0xF8, 0x00, 0x00, 0x00] (LoadPre 0x120dcd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x120dcd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120dcd 13 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x120dcd 13 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_r64_m64_effect_step 0x120dcd 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x120dd5 [0x4C, 0x29, 0xEB] (fun s => s.RIP = 0x120dd5) (subR64R64Effect 0x120dd5 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (subR64R64Effect_footprint 0x120dd5 3 13).toInstrSpec (sub_r64_r64_effect_step 0x120dd5 0x4c 0xeb (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x120dd8 [0x48, 0x8B, 0xAC, 0x24, 0x00, 0x01, 0x00, 0x00] (LoadPre 0x120dd8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x120dd8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120dd8 5 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x120dd8 5 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_r64_m64_effect_step 0x120dd8 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x120de0 [0x48, 0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x00] (fun s => s.RIP = 0x120de0) (movR64Imm64Effect 0x120de0 0 0x3fffffffffffc)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x120de0 0 0x3fffffffffffc).toInstrSpec (mov_r64_imm64_effect_step 0x120de0 0x48 0xb8 (by decide) (by decide) 0x3fffffffffffc) pre_rip
  have f17 : InstrSpec 0x120dea [0x48, 0x29, 0xE8] (fun s => s.RIP = 0x120dea) (subR64R64Effect 0x120dea 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x120dea 0 5).toInstrSpec (sub_r64_r64_effect_step 0x120dea 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x120ded [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x120ded 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120ded + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120ded 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120ded 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x120ded 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x120df2 [0x44, 0x89, 0xF0] (fun s => s.RIP = 0x120df2) (movR32R32Effect 0x120df2 3 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x120df2 3 0 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x120df2 0x44 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d8b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d93) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120d9d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120da0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120da5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120daf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120db2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120db5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120dba) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 66), (1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120dc2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120dc5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120dc8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 73), (1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120dcd) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 73), (1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 76), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120dd5) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 73), (1, 1), (2, 2), (3, 78), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 76), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120dd8) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 73), (1, 1), (2, 2), (3, 78), (4, 4), (5, 80), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 76), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120de0) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 1), (2, 2), (3, 78), (4, 4), (5, 80), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 76), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120dea) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 84), (1, 1), (2, 2), (3, 78), (4, 4), (5, 80), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 76), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ded) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 84), (1, 1), (2, 2), (3, 78), (4, 4), (5, 80), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 76), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120df2) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 1), (2, 2), (3, 78), (4, 4), (5, 80), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 76), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120df5) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l120d83_1 code

theorem block_l120d83 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120d83 :=
  Rest.liftedBlock (rest_l120d83 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120d83 x hx)

theorem rest_l120dff [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120dff bytes_l120dff) (entryMap (live .l120dff))
      3 0x120dff bytes_l120dff b_l120dff := by
  have f0 : InstrSpec 0x120dff [0x32, 0x44, 0x24, 0x6C] (LoadPre 0x120dff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x120dff + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x120dff 4 0 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x120dff 4 0 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (xor_r8_m8_effect_step 0x120dff 0 (by decide) (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x120e03 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x120e03) (movzxR32R8Effect 0x120e03 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x120e03 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x120e03 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x120e06 [0xE8, 0x45, 0x6F, 0x00, 0x00] (PushPre 0x120e06 5) (callEffect (fun _ => 0x127d50) 0x120e0b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x120e06 0x127d50 0x120e0b).toInstrSpec (call_rel32_effect_step 0x120e06 0x6f45 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e03) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e06) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l120dff [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120dff :=
  Rest.liftedBlock (rest_l120dff code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120dff x hx)

theorem rest_l120e0b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120e0b bytes_l120e0b) (entryMap (live .l120e0b))
      4 0x120e0b bytes_l120e0b b_l120e0b := by
  have f0 : InstrSpec 0x120e0b [0xF6, 0xD0] (fun s => s.RIP = 0x120e0b) (notR8Effect 0x120e0b 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x120e0b 2 0).toInstrSpec (not_r8_effect_step 0x120e0b 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x120e0d [0x24, 0x01] (fun s => s.RIP = 0x120e0d) (andAlImm8Effect 0x120e0d 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x120e0d 0x1).toInstrSpec (and_al_imm8_effect_step 0x120e0d 0x1) pre_rip
  have f2 : InstrSpec 0x120e0f [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x120e0f) (movzxR32R8Effect 0x120e0f 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x120e0f 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x120e0f 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x120e12 [0xE8, 0x39, 0x6F, 0x00, 0x00] (PushPre 0x120e12 5) (callEffect (fun _ => 0x127d50) 0x120e17)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x120e12 0x127d50 0x120e17).toInstrSpec (call_rel32_effect_step 0x120e12 0x6f39 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e0d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e0f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e12) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l120e0b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120e0b :=
  Rest.liftedBlock (rest_l120e0b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120e0b x hx)

theorem rest_l120e17_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x120e17 bytes_l120e17) [(0, 55), (1, 87), (3, 3), (4, 4), (5, 91), (10, 10), (11, 11), (12, 79), (13, 85), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]
      9 0x120e5b bytes_l120e17_1 b_l120e17_1 := by
  have f20 : InstrSpec 0x120e5b [0x48, 0x31, 0xCD] (fun s => s.RIP = 0x120e5b) (xorR64R64Effect 0x120e5b 5 1)
      [.gpr 5, .gpr 1] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120e5b 5 1).toInstrSpec (xor_r64_r64_effect_step 0x120e5b 0x48 0xcd (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x120e5e [0x4C, 0x89, 0xB4, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x120e5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x120e5e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120e5e 14 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120e5e 14 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m64_r64_effect_step 0x120e5e 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x120e66 [0x4C, 0x89, 0xBC, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x120e66 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x120e66 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120e66 15 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120e66 15 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m64_r64_effect_step 0x120e66 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x120e6e [0x4C, 0x89, 0xA4, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x120e6e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x120e6e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120e6e 12 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120e6e 12 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m64_r64_effect_step 0x120e6e 0x4c (by decide) 4 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x120e76 [0x4C, 0x89, 0xAC, 0x24, 0x20, 0x01, 0x00, 0x00] (StorePre 0x120e76 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x120e76 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120e76 13 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120e76 13 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_m64_r64_effect_step 0x120e76 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x120e7e [0x48, 0x89, 0xAC, 0x24, 0x28, 0x01, 0x00, 0x00] (StorePre 0x120e7e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x120e7e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120e7e 5 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120e7e 5 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_m64_r64_effect_step 0x120e7e 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x120e86 [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x120e86) (leaR64Effect 0x120e86 7 (.sib 4 none 0 (.d32 0x188)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x120e86 7 (.sib 4 none 0 (.d32 0x188))).toInstrSpec (lea_r64_effect_step 0x120e86 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x188)) (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x120e8e [0x48, 0x8D, 0xB4, 0x24, 0x08, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x120e8e) (leaR64Effect 0x120e8e 6 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x120e8e 6 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (lea_r64_effect_step 0x120e8e 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x120e96 [0xE8, 0x95, 0x3A, 0xFF, 0xFF] (PushPre 0x120e96 5) (callEffect (fun _ => 0x114930) 0x120e9b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x120e96 0x114930 0x120e9b).toInstrSpec (call_rel32_effect_step 0x120e96 0xffff3a95 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 55), (1, 87), (3, 3), (4, 4), (5, 93), (10, 10), (11, 11), (12, 79), (13, 85), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e5e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 55), (1, 87), (3, 3), (4, 4), (5, 93), (10, 10), (11, 11), (12, 79), (13, 85), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e66) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 55), (1, 87), (3, 3), (4, 4), (5, 93), (10, 10), (11, 11), (12, 79), (13, 85), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e6e) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 55), (1, 87), (3, 3), (4, 4), (5, 93), (10, 10), (11, 11), (12, 79), (13, 85), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e76) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 55), (1, 87), (3, 3), (4, 4), (5, 93), (10, 10), (11, 11), (12, 79), (13, 85), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e7e) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 55), (1, 87), (3, 3), (4, 4), (5, 93), (10, 10), (11, 11), (12, 79), (13, 85), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e86) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f26 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 55), (1, 87), (3, 3), (4, 4), (5, 93), (7, 100), (10, 10), (11, 11), (12, 79), (13, 85), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e8e) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f27 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 55), (1, 87), (3, 3), (4, 4), (5, 93), (6, 102), (7, 100), (10, 10), (11, 11), (12, 79), (13, 85), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e96) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f28 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 55), (1, 87), (3, 3), (4, 104), (5, 93), (6, 102), (7, 100), (10, 10), (11, 11), (12, 79), (13, 85), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114930) f28 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 106) (by decide) (by decide) rfl rfl

theorem rest_l120e17 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120e17 bytes_l120e17) (entryMap (live .l120e17))
      29 0x120e17 bytes_l120e17 b_l120e17 := by
  have f0 : InstrSpec 0x120e17 [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x120e17) (movzxR32R8Effect 0x120e17 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x120e17 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x120e17 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x120e1a [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x120e1a) (negR64Effect 0x120e1a 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x120e1a 0).toInstrSpec (neg_r64_effect_step 0x120e1a 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x120e1d [0x48, 0x8B, 0x4C, 0x24, 0x60] (LoadPre 0x120e1d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x120e1d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120e1d 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120e1d 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x120e1d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x120e22 [0x49, 0x31, 0xCE] (fun s => s.RIP = 0x120e22) (xorR64R64Effect 0x120e22 14 1)
      [.gpr 14, .gpr 1] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120e22 14 1).toInstrSpec (xor_r64_r64_effect_step 0x120e22 0x49 0xce (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x120e25 [0x49, 0x21, 0xC6] (fun s => s.RIP = 0x120e25) (andR64R64Effect 0x120e25 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120e25 14 0).toInstrSpec (and_r64_r64_effect_step 0x120e25 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x120e28 [0x49, 0x31, 0xCE] (fun s => s.RIP = 0x120e28) (xorR64R64Effect 0x120e28 14 1)
      [.gpr 14, .gpr 1] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120e28 14 1).toInstrSpec (xor_r64_r64_effect_step 0x120e28 0x49 0xce (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x120e2b [0x48, 0x8B, 0x4C, 0x24, 0x28] (LoadPre 0x120e2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x120e2b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120e2b 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120e2b 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x120e2b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x120e30 [0x49, 0x31, 0xCF] (fun s => s.RIP = 0x120e30) (xorR64R64Effect 0x120e30 15 1)
      [.gpr 15, .gpr 1] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120e30 15 1).toInstrSpec (xor_r64_r64_effect_step 0x120e30 0x49 0xcf (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x120e33 [0x49, 0x21, 0xC7] (fun s => s.RIP = 0x120e33) (andR64R64Effect 0x120e33 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120e33 15 0).toInstrSpec (and_r64_r64_effect_step 0x120e33 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x120e36 [0x49, 0x31, 0xCF] (fun s => s.RIP = 0x120e36) (xorR64R64Effect 0x120e36 15 1)
      [.gpr 15, .gpr 1] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120e36 15 1).toInstrSpec (xor_r64_r64_effect_step 0x120e36 0x49 0xcf (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x120e39 [0x48, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x120e39 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120e39 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120e39 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120e39 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x120e39 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x120e3e [0x49, 0x31, 0xCC] (fun s => s.RIP = 0x120e3e) (xorR64R64Effect 0x120e3e 12 1)
      [.gpr 12, .gpr 1] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120e3e 12 1).toInstrSpec (xor_r64_r64_effect_step 0x120e3e 0x49 0xcc (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x120e41 [0x49, 0x21, 0xC4] (fun s => s.RIP = 0x120e41) (andR64R64Effect 0x120e41 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120e41 12 0).toInstrSpec (and_r64_r64_effect_step 0x120e41 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x120e44 [0x49, 0x31, 0xCC] (fun s => s.RIP = 0x120e44) (xorR64R64Effect 0x120e44 12 1)
      [.gpr 12, .gpr 1] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120e44 12 1).toInstrSpec (xor_r64_r64_effect_step 0x120e44 0x49 0xcc (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x120e47 [0x49, 0x31, 0xDD] (fun s => s.RIP = 0x120e47) (xorR64R64Effect 0x120e47 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120e47 13 3).toInstrSpec (xor_r64_r64_effect_step 0x120e47 0x49 0xdd (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x120e4a [0x49, 0x21, 0xC5] (fun s => s.RIP = 0x120e4a) (andR64R64Effect 0x120e4a 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120e4a 13 0).toInstrSpec (and_r64_r64_effect_step 0x120e4a 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x120e4d [0x49, 0x31, 0xDD] (fun s => s.RIP = 0x120e4d) (xorR64R64Effect 0x120e4d 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120e4d 13 3).toInstrSpec (xor_r64_r64_effect_step 0x120e4d 0x49 0xdd (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x120e50 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x120e50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x120e50 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120e50 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120e50 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x120e50 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x120e55 [0x48, 0x31, 0xCD] (fun s => s.RIP = 0x120e55) (xorR64R64Effect 0x120e55 5 1)
      [.gpr 5, .gpr 1] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120e55 5 1).toInstrSpec (xor_r64_r64_effect_step 0x120e55 0x48 0xcd (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x120e58 [0x48, 0x21, 0xC5] (fun s => s.RIP = 0x120e58) (andR64R64Effect 0x120e58 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120e58 5 0).toInstrSpec (and_r64_r64_effect_step 0x120e58 0x48 0xc5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e1a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e1d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e22) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e25) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e28) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e2b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 65), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e30) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 65), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e33) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 65), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e36) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 65), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e39) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 73), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e3e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 73), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 75), (13, 13), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e41) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 55), (1, 73), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 77), (13, 13), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e44) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 55), (1, 73), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 79), (13, 13), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e47) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 55), (1, 73), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 79), (13, 81), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e4a) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 55), (1, 73), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 79), (13, 83), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e4d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 55), (1, 73), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 79), (13, 85), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e50) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 55), (1, 87), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 79), (13, 85), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e55) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 55), (1, 87), (3, 3), (4, 4), (5, 89), (10, 10), (11, 11), (12, 79), (13, 85), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e58) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 55), (1, 87), (3, 3), (4, 4), (5, 91), (10, 10), (11, 11), (12, 79), (13, 85), (14, 63), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120e5b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l120e17_1 code

theorem block_l120e17 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120e17 :=
  Rest.liftedBlock (rest_l120e17 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120e17 x hx)

theorem rest_l120e9b [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120e9b bytes_l120e9b) (entryMap (live .l120e9b))
      20 0x120e9b bytes_l120e9b b_l120e9b := by
  have f0 : InstrSpec 0x120e9b [0x48, 0x8B, 0x44, 0x24, 0x50] (LoadPre 0x120e9b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x120e9b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120e9b 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120e9b 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x120e9b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x120ea0 [0x48, 0x89, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00] (StorePre 0x120ea0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x120ea0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120ea0 0 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120ea0 0 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (mov_m64_r64_effect_step 0x120ea0 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x120ea8 [0x48, 0x8B, 0x44, 0x24, 0x58] (LoadPre 0x120ea8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x120ea8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120ea8 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120ea8 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x120ea8 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x120ead [0x48, 0x89, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00] (StorePre 0x120ead 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x120ead + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120ead 0 (.sib 4 none 0 (.d32 0x168)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120ead 0 (.sib 4 none 0 (.d32 0x168))).toInstrSpec (mov_m64_r64_effect_step 0x120ead 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x120eb5 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x120eb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x120eb5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120eb5 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120eb5 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x120eb5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x120eba [0x48, 0x89, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00] (StorePre 0x120eba 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x120eba + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120eba 0 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120eba 0 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (mov_m64_r64_effect_step 0x120eba 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x120ec2 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x120ec2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x120ec2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120ec2 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120ec2 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x120ec2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x120ec7 [0x48, 0x89, 0x84, 0x24, 0x78, 0x01, 0x00, 0x00] (StorePre 0x120ec7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x120ec7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120ec7 0 (.sib 4 none 0 (.d32 0x178)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120ec7 0 (.sib 4 none 0 (.d32 0x178))).toInstrSpec (mov_m64_r64_effect_step 0x120ec7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x178)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x120ecf [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x120ecf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x120ecf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120ecf 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120ecf 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x120ecf 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x120ed4 [0x48, 0x89, 0x84, 0x24, 0x80, 0x01, 0x00, 0x00] (StorePre 0x120ed4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x120ed4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120ed4 0 (.sib 4 none 0 (.d32 0x180)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120ed4 0 (.sib 4 none 0 (.d32 0x180))).toInstrSpec (mov_m64_r64_effect_step 0x120ed4 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x180)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x120edc [0xC6, 0x84, 0x24, 0xB0, 0x01, 0x00, 0x00, 0x00] (StorePre 0x120edc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x120edc + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x120edc (.sib 4 none 0 (.d32 0x1b0)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x120edc (.sib 4 none 0 (.d32 0x1b0)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x120edc (.sib 4 none 0 (.d32 0x1b0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x120ee4 [0x48, 0x8D, 0xB4, 0x24, 0x60, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x120ee4) (leaR64Effect 0x120ee4 6 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x120ee4 6 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (lea_r64_effect_step 0x120ee4 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x120eec [0xB9, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x120eec) (movR32Imm32Effect 0x120eec 5 1 0xb)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x120eec 5 1 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x120eec 0xb9 (by decide) 0xb) pre_rip
  have f13 : InstrSpec 0x120ef1 [0x48, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x120ef1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x120ef1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120ef1 3 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x120ef1 3 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x120ef1 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x120ef9 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x120ef9) (movR64R64Effect 0x120ef9 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x120ef9 7 3).toInstrSpec (mov_r64_r64_effect_step 0x120ef9 0x48 0xdf (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x120efc [0xF3, 0x48, 0xA5] (RepPre 0x120efc (RepMovsqPre 0x120efc)) (repMovsqEffect 0x120efc)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x120efc).toInstrSpecOfRuns (rep_movsq_runs hstride 0x120efc 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f16 : InstrSpec 0x120eff [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x120eff (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x120eff + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120eff 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120eff 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x120eff 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x120f07 [0x22, 0x44, 0x24, 0x20] (LoadPre 0x120f07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x120f07 + BitVec.ofNat 64 4)) 1) (andR8M8Effect 0x120f07 4 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (andR8M8Effect_footprint 0x120f07 4 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (and_r8_m8_effect_step 0x120f07 0 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x120f0b [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x120f0b) (movzxR32R8Effect 0x120f0b 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x120f0b 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x120f0b 0xf8 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x120f0e [0xE8, 0x3D, 0x6E, 0x00, 0x00] (PushPre 0x120f0e 5) (callEffect (fun _ => 0x127d50) 0x120f13)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x120f0e 0x127d50 0x120f13).toInstrSpec (call_rel32_effect_step 0x120f0e 0x6e3d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ea0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ea8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ead) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120eb5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120eba) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ec2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ec7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ecf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ed4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120edc) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 65), (2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ee4) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (2, 2), (4, 4), (5, 5), (6, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120eec) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (1, 71), (2, 2), (4, 4), (5, 5), (6, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ef1) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 65), (1, 71), (2, 2), (3, 73), (4, 4), (5, 5), (6, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ef9) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 65), (1, 71), (2, 2), (3, 73), (4, 4), (5, 5), (6, 69), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120efc) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 78) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 79) (ρ' := [(0, 65), (1, 78), (2, 2), (3, 73), (4, 4), (5, 5), (6, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120eff) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 78), (2, 2), (3, 73), (4, 4), (5, 5), (6, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f07) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 78), (2, 2), (3, 73), (4, 4), (5, 5), (6, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f0b) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 82), (1, 78), (2, 2), (3, 73), (4, 4), (5, 5), (6, 77), (7, 84), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f0e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 82), (1, 78), (2, 2), (3, 73), (4, 86), (5, 5), (6, 77), (7, 84), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 88) (by decide) (by decide) rfl rfl

theorem block_l120e9b [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120e9b :=
  Rest.liftedBlock (rest_l120e9b hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120e9b x hx)

theorem rest_l120f13 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120f13 bytes_l120f13) (entryMap (live .l120f13))
      10 0x120f13 bytes_l120f13 b_l120f13 := by
  have f0 : InstrSpec 0x120f13 [0x88, 0x43, 0x58] (StorePre 0x120f13 3 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x120f13 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x120f13 3 0 (.base 3 (.d8 0x58)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x120f13 3 0 (.base 3 (.d8 0x58))).toInstrSpec (mov_m8_r8_effect_step 0x120f13 0 (by decide) (.base 3 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x120f16 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x120f16) (movR64R64Effect 0x120f16 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120f16 0 3).toInstrSpec (mov_r64_r64_effect_step 0x120f16 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x120f19 [0x48, 0x81, 0xC4, 0xB8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x120f19) (addR64Imm32Effect 0x120f19 4 0x1b8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x120f19 4 0x1b8).toInstrSpec (add_r64_imm32_effect_step 0x120f19 0x48 0xc4 0x1b8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x120f20 [0x5B] (PopPre 0x120f20) (popR64Effect 0x120f20 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x120f20 1 3).toInstrSpec (pop_r64_effect_step 0x120f20 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x120f21 [0x41, 0x5C] (PopPre 0x120f21) (popR64Effect 0x120f21 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x120f21 2 12).toInstrSpec (pop_r64_rex_effect_step 0x120f21 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x120f23 [0x41, 0x5D] (PopPre 0x120f23) (popR64Effect 0x120f23 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x120f23 2 13).toInstrSpec (pop_r64_rex_effect_step 0x120f23 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x120f25 [0x41, 0x5E] (PopPre 0x120f25) (popR64Effect 0x120f25 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x120f25 2 14).toInstrSpec (pop_r64_rex_effect_step 0x120f25 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x120f27 [0x41, 0x5F] (PopPre 0x120f27) (popR64Effect 0x120f27 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x120f27 2 15).toInstrSpec (pop_r64_rex_effect_step 0x120f27 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x120f29 [0x5D] (PopPre 0x120f29) (popR64Effect 0x120f29 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x120f29 1 5).toInstrSpec (pop_r64_effect_step 0x120f29 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x120f2a [0xC3] (RetPre 0x120f2a) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x120f2a).toInstrSpec (ret_effect_step 0x120f2a) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f16) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f19) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f20) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f21) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f23) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f25) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f27) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f7 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f29) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 74), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f2a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f9 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 78) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 77), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) f9 (by decide) rfl rfl rfl (by decide)

theorem block_l120f13 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120f13 :=
  Rest.liftedBlock (rest_l120f13 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120f13 x hx)

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

theorem_by block_l1205b0_eval :
    program.runBlock (dialect code) ⟨.l1205b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120653_eval :
    program.runBlock (dialect code) ⟨.l120653, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120d03_eval :
    program.runBlock (dialect code) ⟨.l120d03, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120d83_eval :
    program.runBlock (dialect code) ⟨.l120d83, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120dff_eval :
    program.runBlock (dialect code) ⟨.l120dff, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120e0b_eval :
    program.runBlock (dialect code) ⟨.l120e0b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120e17_eval :
    program.runBlock (dialect code) ⟨.l120e17, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120e9b_eval :
    program.runBlock (dialect code) ⟨.l120e9b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120f13_eval :
    program.runBlock (dialect code) ⟨.l120f13, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Ecdh.LIR
