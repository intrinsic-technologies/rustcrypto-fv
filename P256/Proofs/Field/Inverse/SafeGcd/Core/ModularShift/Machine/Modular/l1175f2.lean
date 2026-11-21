import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1175f2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111b12 bytes_l1175f2) (entryMap (live .l1175f2))
      14 0x111b12 bytes_l1175f2 b_l1175f2 := by
  have f0 : InstrSpec 0x111b12 [0x48, 0x8B, 0x74, 0x24, 0x70] (LoadPre 0x111b12 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x111b12 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111b12 6 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x111b12 6 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x111b12 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x111b17 [0x4C, 0x89, 0x06] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111b17 3 (fun s => AddrMode.addr (.base 6 .none) s (0x111b17 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x111b17 8 (.base 6 .none))
      [.gpr 8, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x111b17 8 (.base 6 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111b17 0x4c (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f2 : InstrSpec 0x111b1a [0x48, 0x89, 0x46, 0x08] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111b1a 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x111b1a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111b1a 0 (.base 6 (.d8 0x8)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x111b1a 0 (.base 6 (.d8 0x8))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111b1a 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f3 : InstrSpec 0x111b1e [0x48, 0x89, 0x56, 0x10] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111b1e 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x111b1e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111b1e 2 (.base 6 (.d8 0x10)))
      [.gpr 2, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x111b1e 2 (.base 6 (.d8 0x10))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111b1e 0x48 (by decide) 2 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f4 : InstrSpec 0x111b22 [0x48, 0x89, 0x4E, 0x18] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111b22 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x111b22 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111b22 1 (.base 6 (.d8 0x18)))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x111b22 1 (.base 6 (.d8 0x18))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111b22 0x48 (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f5 : InstrSpec 0x111b26 [0x40, 0x88, 0x6E, 0x20] (StorePre 0x111b26 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x111b26 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111b26 4 5 (.base 6 (.d8 0x20)))
      [.gpr 5, .gpr 6] [] [.rip] :=
    (movM8R8Effect_footprint 0x111b26 4 5 (.base 6 (.d8 0x20))).toInstrSpec (mov_m8_r8_rex_effect_step 0x111b26 0x40 (by decide) 5 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x111b2a [0x48, 0x83, 0xC4, 0x78] (fun s => s.RIP = 0x111b2a) (addR64Imm8Effect 0x111b2a 4 0x78)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x111b2a 4 0x78).toInstrSpec (add_r64_imm8_effect_step 0x111b2a 0x48 0xc4 0x78 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111b2e [0x5B] (PopPre 0x111b2e) (popR64Effect 0x111b2e 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x111b2e 1 3).toInstrSpec (pop_r64_effect_step 0x111b2e 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x111b2f [0x41, 0x5C] (PopPre 0x111b2f) (popR64Effect 0x111b2f 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x111b2f 2 12).toInstrSpec (pop_r64_rex_effect_step 0x111b2f 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x111b31 [0x41, 0x5D] (PopPre 0x111b31) (popR64Effect 0x111b31 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x111b31 2 13).toInstrSpec (pop_r64_rex_effect_step 0x111b31 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x111b33 [0x41, 0x5E] (PopPre 0x111b33) (popR64Effect 0x111b33 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x111b33 2 14).toInstrSpec (pop_r64_rex_effect_step 0x111b33 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x111b35 [0x41, 0x5F] (PopPre 0x111b35) (popR64Effect 0x111b35 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x111b35 2 15).toInstrSpec (pop_r64_rex_effect_step 0x111b35 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x111b37 [0x5D] (PopPre 0x111b37) (popR64Effect 0x111b37 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x111b37 1 5).toInstrSpec (pop_r64_effect_step 0x111b37 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f13 : InstrSpec 0x111b38 [0xC3] (RetPre 0x111b38) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x111b38).toInstrSpec (ret_effect_step 0x111b38) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (8, 8), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b17) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (8, 8), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b1a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (8, 8), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b1e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (8, 8), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b22) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (8, 8), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b26) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (8, 8), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b2a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 60), (5, 5), (6, 53), (8, 8), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b2e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 62), (4, 63), (5, 5), (6, 53), (8, 8), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b2f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 62), (4, 66), (5, 5), (6, 53), (8, 8), (12, 65), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b31) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 62), (4, 69), (5, 5), (6, 53), (8, 8), (12, 65), (13, 68), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b33) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 62), (4, 72), (5, 5), (6, 53), (8, 8), (12, 65), (13, 68), (14, 71), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b35) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 75) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 62), (4, 75), (5, 5), (6, 53), (8, 8), (12, 65), (13, 68), (14, 71), (15, 74), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b37) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 78) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 62), (4, 78), (5, 77), (6, 53), (8, 8), (12, 65), (13, 68), (14, 71), (15, 74), (22, 22), (39, 39), (51, 51)]) (p' := 0x111b38) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f13 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 81) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 62), (4, 81), (5, 77), (6, 53), (8, 8), (12, 65), (13, 68), (14, 71), (15, 74), (22, 22), (39, 39), (51, 51)]) f13 (by decide) rfl rfl rfl (by decide)

theorem block_l1175f2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1175f2 :=
  Rest.liftedBlock (rest_l1175f2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1175f2 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
