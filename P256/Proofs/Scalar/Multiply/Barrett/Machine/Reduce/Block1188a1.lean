import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1188a1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112dc1 bytes_l1188a1) (entryMap (live .l1188a1))
      9 0x112dc1 bytes_l1188a1 b_l1188a1 := by
  have f0 : InstrSpec 0x112dc1 [0x48, 0x89, 0x0C, 0x24] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112dc1 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112dc1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112dc1 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112dc1 1 (.sib 4 none 0 .none)).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112dc1 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f1 : InstrSpec 0x112dc5 [0x48, 0x89, 0xE1] (fun s => s.RIP = 0x112dc5) (movR64R64Effect 0x112dc5 1 4)
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x112dc5 1 4).toInstrSpec (mov_r64_r64_effect_step 0x112dc5 0x48 0xe1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112dc8 [0x48, 0x8B, 0x0C, 0x24] (LoadPre 0x112dc8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112dc8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112dc8 1 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x112dc8 1 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x112dc8 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x112dcc [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x112dcc) (movR64R64Effect 0x112dcc 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x112dcc 9 2).toInstrSpec (mov_r64_r64_effect_step 0x112dcc 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x112dcf [0x49, 0x29, 0xC9] (fun s => s.RIP = 0x112dcf) (subR64R64Effect 0x112dcf 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x112dcf 9 1).toInstrSpec (sub_r64_r64_effect_step 0x112dcf 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112dd2 [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x112dd2) (negR64Effect 0x112dd2 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x112dd2 1).toInstrSpec (neg_r64_effect_step 0x112dd2 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x112dd5 [0x49, 0x21, 0xCF] (fun s => s.RIP = 0x112dd5) (andR64R64Effect 0x112dd5 15 1)
      [.gpr 15, .gpr 1] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112dd5 15 1).toInstrSpec (and_r64_r64_effect_step 0x112dd5 0x49 0xcf (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x112dd8 [0x49, 0xBB, 0x84, 0x9E, 0x17, 0xA7, 0xAD, 0xFA, 0xE6, 0xBC] (fun s => s.RIP = 0x112dd8) (movR64Imm64Effect 0x112dd8 11 0xbce6faada7179e84)
      [] [] [.reg 11, .rip] :=
    (movR64Imm64Effect_footprint 0x112dd8 11 0xbce6faada7179e84).toInstrSpec (mov_r64_imm64_effect_step 0x112dd8 0x49 0xbb (by decide) (by decide) 0xbce6faada7179e84) pre_rip
  have f8 : InstrSpec 0x112de2 [0x49, 0x21, 0xCB] (fun s => s.RIP = 0x112de2) (andR64R64Effect 0x112de2 11 1)
      [.gpr 11, .gpr 1] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112de2 11 1).toInstrSpec (and_r64_r64_effect_step 0x112de2 0x49 0xcb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112dc5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112dc8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112dcc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112dcf) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112dd2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 59), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112dd5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 61), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 59), (15, 63), (22, 22), (39, 39), (51, 51)]) (p' := 0x112dd8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 61), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 59), (11, 65), (15, 63), (22, 22), (39, 39), (51, 51)]) (p' := 0x112de2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 61), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 59), (11, 67), (15, 63), (22, 22), (39, 39), (51, 51)]) (p' := 0x112de5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 69) (by decide) rfl

theorem block_l1188a1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1188a1 :=
  Rest.liftedBlock (rest_l1188a1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1188a1 x hx)

end P256.Proofs.Scalar.Multiply.Barrett.Machine
