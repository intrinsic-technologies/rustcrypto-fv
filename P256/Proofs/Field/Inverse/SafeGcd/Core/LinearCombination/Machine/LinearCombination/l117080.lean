import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117080 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1115a0 bytes_l117080) (entryMap (live .l117080))
      16 0x1115a0 bytes_l117080 b_l117080 := by
  have f0 : InstrSpec 0x1115a0 [0x48, 0x89, 0x37] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1115a0 3 (fun s => AddrMode.addr (.base 7 .none) s (0x1115a0 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1115a0 6 (.base 7 .none))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x1115a0 6 (.base 7 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1115a0 0x48 (by decide) 6 (.base 7 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1115a3 [0x48, 0x89, 0x47, 0x08] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1115a3 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1115a3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1115a3 0 (.base 7 (.d8 0x8)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x1115a3 0 (.base 7 (.d8 0x8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1115a3 0x48 (by decide) 0 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1115a7 [0x4C, 0x89, 0x47, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1115a7 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x1115a7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1115a7 8 (.base 7 (.d8 0x10)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x1115a7 8 (.base 7 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1115a7 0x4c (by decide) 0 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1115ab [0x4C, 0x89, 0x4F, 0x18] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1115ab 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x1115ab + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1115ab 9 (.base 7 (.d8 0x18)))
      [.gpr 9, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x1115ab 9 (.base 7 (.d8 0x18))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1115ab 0x4c (by decide) 1 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1115af [0x4C, 0x89, 0x57, 0x20] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1115af 4 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x1115af + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1115af 10 (.base 7 (.d8 0x20)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x1115af 10 (.base 7 (.d8 0x20))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1115af 0x4c (by decide) 2 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1115b3 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x1115b3) (movR64R64Effect 0x1115b3 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1115b3 0 2).toInstrSpec (mov_r64_r64_effect_step 0x1115b3 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1115b6 [0x08, 0xC8] (fun s => s.RIP = 0x1115b6) (orR8R8Effect 0x1115b6 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (orR8R8Effect_footprint 0x1115b6 2 0 1).toInstrSpec (or_r8_r8_effect_step 0x1115b6 0xc8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1115b8 [0x88, 0x47, 0x28] (StorePre 0x1115b8 3 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x1115b8 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1115b8 3 0 (.base 7 (.d8 0x28)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x1115b8 3 0 (.base 7 (.d8 0x28))).toInstrSpec (mov_m8_r8_effect_step 0x1115b8 0 (by decide) (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1115bb [0x48, 0x83, 0xC4, 0x40] (fun s => s.RIP = 0x1115bb) (addR64Imm8Effect 0x1115bb 4 0x40)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1115bb 4 0x40).toInstrSpec (add_r64_imm8_effect_step 0x1115bb 0x48 0xc4 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1115bf [0x5B] (PopPre 0x1115bf) (popR64Effect 0x1115bf 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1115bf 1 3).toInstrSpec (pop_r64_effect_step 0x1115bf 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x1115c0 [0x41, 0x5C] (PopPre 0x1115c0) (popR64Effect 0x1115c0 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1115c0 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1115c0 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x1115c2 [0x41, 0x5D] (PopPre 0x1115c2) (popR64Effect 0x1115c2 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1115c2 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1115c2 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x1115c4 [0x41, 0x5E] (PopPre 0x1115c4) (popR64Effect 0x1115c4 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1115c4 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1115c4 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f13 : InstrSpec 0x1115c6 [0x41, 0x5F] (PopPre 0x1115c6) (popR64Effect 0x1115c6 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1115c6 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1115c6 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f14 : InstrSpec 0x1115c8 [0x5D] (PopPre 0x1115c8) (popR64Effect 0x1115c8 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1115c8 1 5).toInstrSpec (pop_r64_effect_step 0x1115c8 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f15 : InstrSpec 0x1115c9 [0xC3] (RetPre 0x1115c9) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1115c9).toInstrSpec (ret_effect_step 0x1115c9) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115a3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115a7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115ab) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115af) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115b3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115b6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115b8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115bb) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115bf) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 60), (1, 1), (2, 2), (3, 65), (4, 66), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115c0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 70) (ρ' := [(0, 60), (1, 1), (2, 2), (3, 65), (4, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (12, 68), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115c2) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 60), (1, 1), (2, 2), (3, 65), (4, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (12, 68), (13, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115c4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 75) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 76) (ρ' := [(0, 60), (1, 1), (2, 2), (3, 65), (4, 75), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (12, 68), (13, 71), (14, 74), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115c6) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 78) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 79) (ρ' := [(0, 60), (1, 1), (2, 2), (3, 65), (4, 78), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (12, 68), (13, 71), (14, 74), (15, 77), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115c8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 81) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 82) (ρ' := [(0, 60), (1, 1), (2, 2), (3, 65), (4, 81), (5, 80), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (12, 68), (13, 71), (14, 74), (15, 77), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115c9) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 84) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 85) (ρ' := [(0, 60), (1, 1), (2, 2), (3, 65), (4, 84), (5, 80), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (12, 68), (13, 71), (14, 74), (15, 77), (22, 22), (39, 39), (51, 51)]) f15 (by decide) rfl rfl rfl (by decide)

theorem block_l117080 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117080 :=
  Rest.liftedBlock (rest_l117080 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117080 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
