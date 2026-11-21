import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1170e3_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x111603 bytes_l1170e3) [(0, 0), (1, 87), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 91), (15, 15), (22, 22), (39, 39), (51, 51)]
      19 0x111646 bytes_l1170e3_1 b_l1170e3_1 := by
  have f20 : InstrSpec 0x111646 [0x89, 0xE9] (fun s => s.RIP = 0x111646) (movR32R32Effect 0x111646 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x111646 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x111646 0xe9 (by decide)) pre_rip
  have f21 : InstrSpec 0x111648 [0x49, 0xD3, 0xEE] (fun s => s.RIP = 0x111648) (shrR64ClEffect 0x111648 3 14)
      [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x111648 3 14).toInstrSpec (shr_r64_cl_effect_step 0x111648 0x49 0xee (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x11164b [0x89, 0xC1] (fun s => s.RIP = 0x11164b) (movR32R32Effect 0x11164b 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x11164b 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x11164b 0xc1 (by decide)) pre_rip
  have f23 : InstrSpec 0x11164d [0x48, 0xD3, 0xE6] (fun s => s.RIP = 0x11164d) (shlR64ClEffect 0x11164d 3 6)
      [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x11164d 3 6).toInstrSpec (shl_r64_cl_effect_step 0x11164d 0x48 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x111650 [0x89, 0xE9] (fun s => s.RIP = 0x111650) (movR32R32Effect 0x111650 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x111650 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x111650 0xe9 (by decide)) pre_rip
  have f25 : InstrSpec 0x111652 [0x48, 0xD3, 0xEA] (fun s => s.RIP = 0x111652) (shrR64ClEffect 0x111652 3 2)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x111652 3 2).toInstrSpec (shr_r64_cl_effect_step 0x111652 0x48 0xea (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x111655 [0x4D, 0x09, 0xC3] (fun s => s.RIP = 0x111655) (orR64R64Effect 0x111655 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111655 11 8).toInstrSpec (or_r64_r64_effect_step 0x111655 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x111658 [0x49, 0x09, 0xFE] (fun s => s.RIP = 0x111658) (orR64R64Effect 0x111658 14 7)
      [.gpr 14, .gpr 7] [] [.reg 14, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111658 14 7).toInstrSpec (or_r64_r64_effect_step 0x111658 0x49 0xfe (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x11165b [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x11165b) (orR64R64Effect 0x11165b 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11165b 2 6).toInstrSpec (or_r64_r64_effect_step 0x11165b 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x11165e [0x48, 0x89, 0x13] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11165e 3 (fun s => AddrMode.addr (.base 3 .none) s (0x11165e + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11165e 2 (.base 3 .none))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x11165e 2 (.base 3 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x11165e 0x48 (by decide) 2 (.base 3 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f30 : InstrSpec 0x111661 [0x4C, 0x89, 0x73, 0x08] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111661 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x111661 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111661 14 (.base 3 (.d8 0x8)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x111661 14 (.base 3 (.d8 0x8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111661 0x4c (by decide) 6 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f31 : InstrSpec 0x111665 [0x4C, 0x89, 0x5B, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111665 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x111665 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111665 11 (.base 3 (.d8 0x10)))
      [.gpr 11, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x111665 11 (.base 3 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111665 0x4c (by decide) 3 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f32 : InstrSpec 0x111669 [0x4C, 0x89, 0x4B, 0x18] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111669 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x111669 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111669 9 (.base 3 (.d8 0x18)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x111669 9 (.base 3 (.d8 0x18))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111669 0x4c (by decide) 1 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f33 : InstrSpec 0x11166d [0x44, 0x88, 0x53, 0x20] (StorePre 0x11166d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x11166d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11166d 4 10 (.base 3 (.d8 0x20)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x11166d 4 10 (.base 3 (.d8 0x20))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11166d 0x44 (by decide) 2 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x111671 [0x48, 0x83, 0xC4, 0x30] (fun s => s.RIP = 0x111671) (addR64Imm8Effect 0x111671 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x111671 4 0x30).toInstrSpec (add_r64_imm8_effect_step 0x111671 0x48 0xc4 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x111675 [0x5B] (PopPre 0x111675) (popR64Effect 0x111675 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x111675 1 3).toInstrSpec (pop_r64_effect_step 0x111675 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f36 : InstrSpec 0x111676 [0x41, 0x5E] (PopPre 0x111676) (popR64Effect 0x111676 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x111676 2 14).toInstrSpec (pop_r64_rex_effect_step 0x111676 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f37 : InstrSpec 0x111678 [0x5D] (PopPre 0x111678) (popR64Effect 0x111678 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x111678 1 5).toInstrSpec (pop_r64_effect_step 0x111678 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f38 : InstrSpec 0x111679 [0xC3] (RetPre 0x111679) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x111679).toInstrSpec (ret_effect_step 0x111679) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 0), (1, 93), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 91), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111648) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 0), (1, 93), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11164b) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 0), (1, 97), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11164d) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 0), (1, 97), (2, 53), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111650) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 0), (1, 101), (2, 53), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111652) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 0), (1, 101), (2, 103), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111655) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 0), (1, 101), (2, 103), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111658) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 0), (1, 101), (2, 103), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11165b) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11165e) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.exec (n := 111) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111661) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111665) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111669) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 114) (RestInside.exec (n := 114) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11166d) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111671) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f34 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 116), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111675) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f35 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 119) f35 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 120) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 118), (4, 119), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111676) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 122) f36 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 123) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 118), (4, 122), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 121), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111678) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f37 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 125) f37 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 126) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 118), (4, 125), (5, 124), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 121), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111679) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f38 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 128) f38 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 129) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 118), (4, 128), (5, 124), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 121), (15, 15), (22, 22), (39, 39), (51, 51)]) f38 (by decide) rfl rfl rfl (by decide)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine
