import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l118837 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112d57 bytes_l118837) (entryMap (live .l118837))
      9 0x112d57 bytes_l118837 b_l118837 := by
  have f0 : InstrSpec 0x112d57 [0x48, 0x89, 0x14, 0x24] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112d57 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112d57 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112d57 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112d57 2 (.sib 4 none 0 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112d57 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x112d5b [0x48, 0x89, 0xE2] (fun s => s.RIP = 0x112d5b) (movR64R64Effect 0x112d5b 2 4)
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x112d5b 2 4).toInstrSpec (mov_r64_r64_effect_step 0x112d5b 0x48 0xe2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112d5e [0x48, 0x8B, 0x14, 0x24] (LoadPre 0x112d5e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112d5e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112d5e 2 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x112d5e 2 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x112d5e 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x112d62 [0x48, 0xFF, 0xCA] (fun s => s.RIP = 0x112d62) (decR64Effect 0x112d62 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (decR64Effect_footprint 0x112d62 2).toInstrSpec (dec_r64_effect_step 0x112d62 0x48 0xca (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x112d65 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x112d65) (shrR64Effect 0x112d65 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x112d65 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x112d65 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112d69 [0x48, 0x01, 0xF2] (fun s => s.RIP = 0x112d69) (addR64R64Effect 0x112d69 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112d69 2 6).toInstrSpec (add_r64_r64_effect_step 0x112d69 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112d6c [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x112d6c) (notR64Effect 0x112d6c 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x112d6c 6).toInstrSpec (not_r64_effect_step 0x112d6c 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x112d6f [0x48, 0x09, 0xD6] (fun s => s.RIP = 0x112d6f) (orR64R64Effect 0x112d6f 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x112d6f 6 2).toInstrSpec (or_r64_r64_effect_step 0x112d6f 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x112d72 [0x48, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x112d72) (shrR64Effect 0x112d72 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x112d72 4 6 63).toInstrSpec (shr_r64_imm8_effect_step 0x112d72 0x48 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d5b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d5e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d62) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d65) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d69) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d6c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 61), (4, 4), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d6f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 61), (4, 4), (6, 65), (7, 7), (8, 8), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d72) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 61), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d76) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 69) (by decide) rfl

theorem block_l118837 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l118837 :=
  Rest.liftedBlock (rest_l118837 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l118837 x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
