import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1187ed [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112d0d bytes_l1187ed) (entryMap (live .l1187ed))
      7 0x112d0d bytes_l1187ed b_l1187ed := by
  have f0 : InstrSpec 0x112d0d [0x4C, 0x89, 0x14, 0x24] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112d0d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112d0d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112d0d 10 (.sib 4 none 0 .none))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112d0d 10 (.sib 4 none 0 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112d0d 0x4c (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x112d11 [0x49, 0x89, 0xE0] (fun s => s.RIP = 0x112d11) (movR64R64Effect 0x112d11 8 4)
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x112d11 8 4).toInstrSpec (mov_r64_r64_effect_step 0x112d11 0x49 0xe0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112d14 [0x49, 0xB8, 0xAF, 0xDA, 0x9C, 0x03, 0x3D, 0x35, 0x46, 0x0C] (fun s => s.RIP = 0x112d14) (movR64Imm64Effect 0x112d14 8 0xc46353d039cdaaf)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x112d14 8 0xc46353d039cdaaf).toInstrSpec (mov_r64_imm64_effect_step 0x112d14 0x49 0xb8 (by decide) (by decide) 0xc46353d039cdaaf) pre_rip
  have f3 : InstrSpec 0x112d1e [0x49, 0x01, 0xC0] (fun s => s.RIP = 0x112d1e) (addR64R64Effect 0x112d1e 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112d1e 8 0).toInstrSpec (add_r64_r64_effect_step 0x112d1e 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x112d21 [0x48, 0xF7, 0xD0] (fun s => s.RIP = 0x112d21) (notR64Effect 0x112d21 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR64Effect_footprint 0x112d21 0).toInstrSpec (not_r64_effect_step 0x112d21 0x48 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112d24 [0x4C, 0x09, 0xC0] (fun s => s.RIP = 0x112d24) (orR64R64Effect 0x112d24 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x112d24 0 8).toInstrSpec (or_r64_r64_effect_step 0x112d24 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112d27 [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x112d27) (shrR64Effect 0x112d27 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x112d27 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x112d27 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d11) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d14) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d1e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 57), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d21) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 57), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d24) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 57), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d27) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 57), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112d2b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 65) (by decide) rfl

theorem block_l1187ed [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1187ed :=
  Rest.liftedBlock (rest_l1187ed code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1187ed x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
