import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1188e7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112e07 bytes_l1188e7) (entryMap (live .l1188e7))
      12 0x112e07 bytes_l1188e7 b_l1188e7 := by
  have f0 : InstrSpec 0x112e07 [0x4C, 0x89, 0x3F] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e07 3 (fun s => AddrMode.addr (.base 7 .none) s (0x112e07 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x112e07 15 (.base 7 .none))
      [.gpr 15, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x112e07 15 (.base 7 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112e07 0x4c (by decide) 7 (.base 7 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x112e0a [0x4C, 0x89, 0x5F, 0x08] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e0a 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x112e0a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112e0a 11 (.base 7 (.d8 0x8)))
      [.gpr 11, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x112e0a 11 (.base 7 (.d8 0x8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112e0a 0x4c (by decide) 3 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f2 : InstrSpec 0x112e0e [0x4C, 0x89, 0x4F, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e0e 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x112e0e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112e0e 9 (.base 7 (.d8 0x10)))
      [.gpr 9, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x112e0e 9 (.base 7 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112e0e 0x4c (by decide) 1 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f3 : InstrSpec 0x112e12 [0x4C, 0x89, 0x47, 0x18] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e12 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x112e12 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112e12 8 (.base 7 (.d8 0x18)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x112e12 8 (.base 7 (.d8 0x18))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112e12 0x4c (by decide) 0 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f4 : InstrSpec 0x112e16 [0x48, 0x83, 0xC4, 0x40] (fun s => s.RIP = 0x112e16) (addR64Imm8Effect 0x112e16 4 0x40)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x112e16 4 0x40).toInstrSpec (add_r64_imm8_effect_step 0x112e16 0x48 0xc4 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112e1a [0x5B] (PopPre 0x112e1a) (popR64Effect 0x112e1a 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x112e1a 1 3).toInstrSpec (pop_r64_effect_step 0x112e1a 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x112e1b [0x41, 0x5C] (PopPre 0x112e1b) (popR64Effect 0x112e1b 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x112e1b 2 12).toInstrSpec (pop_r64_rex_effect_step 0x112e1b 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x112e1d [0x41, 0x5D] (PopPre 0x112e1d) (popR64Effect 0x112e1d 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x112e1d 2 13).toInstrSpec (pop_r64_rex_effect_step 0x112e1d 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x112e1f [0x41, 0x5E] (PopPre 0x112e1f) (popR64Effect 0x112e1f 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x112e1f 2 14).toInstrSpec (pop_r64_rex_effect_step 0x112e1f 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x112e21 [0x41, 0x5F] (PopPre 0x112e21) (popR64Effect 0x112e21 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x112e21 2 15).toInstrSpec (pop_r64_rex_effect_step 0x112e21 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x112e23 [0x5D] (PopPre 0x112e23) (popR64Effect 0x112e23 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x112e23 1 5).toInstrSpec (pop_r64_effect_step 0x112e23 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x112e24 [0xC3] (RetPre 0x112e24) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x112e24).toInstrSpec (ret_effect_step 0x112e24) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e0a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e0e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e12) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e16) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (4, 57), (7, 7), (8, 8), (9, 9), (11, 11), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e1a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 2), (3, 59), (4, 60), (7, 7), (8, 8), (9, 9), (11, 11), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e1b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (2, 2), (3, 59), (4, 63), (7, 7), (8, 8), (9, 9), (11, 11), (12, 62), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e1d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (2, 2), (3, 59), (4, 66), (7, 7), (8, 8), (9, 9), (11, 11), (12, 62), (13, 65), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e1f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (2, 2), (3, 59), (4, 69), (7, 7), (8, 8), (9, 9), (11, 11), (12, 62), (13, 65), (14, 68), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e21) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (2, 2), (3, 59), (4, 72), (7, 7), (8, 8), (9, 9), (11, 11), (12, 62), (13, 65), (14, 68), (15, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e23) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 75) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (2, 2), (3, 59), (4, 75), (5, 74), (7, 7), (8, 8), (9, 9), (11, 11), (12, 62), (13, 65), (14, 68), (15, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x112e24) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f11 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 78) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 79) (ρ' := [(0, 0), (2, 2), (3, 59), (4, 78), (5, 74), (7, 7), (8, 8), (9, 9), (11, 11), (12, 62), (13, 65), (14, 68), (15, 71), (22, 22), (39, 39), (51, 51)]) f11 (by decide) rfl rfl rfl (by decide)

theorem block_l1188e7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1188e7 :=
  Rest.liftedBlock (rest_l1188e7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1188e7 x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
